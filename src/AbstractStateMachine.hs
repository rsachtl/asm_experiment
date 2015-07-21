 {-# LANGUAGE GADTs              #-}
 {-# LANGUAGE StandaloneDeriving #-}

module AbstractStateMachine where

import Data.Map as Map
import Data.Set as Set
import Data.List as List
import System.Random
import Control.Monad
import Data.Maybe
import Data.Either

data FunType =
    Static
  | Controlled
  | In
  | Shared
  | Out

data Signature = Signature
  { staticS :: Map String Int
  , controlledS :: Map String Int
  , inS :: Map String Int
  , outS :: Map String Int
  , sharedS :: Map String Int
  }

data ASM a = ASM
  { universe :: [UElem a]
  , staticF :: Map String (Fun a)
  , inF :: Map String (Fun a)
  , outF :: Map String (Fun a)
  , sharedF :: Map String (Fun a)
  , controlledF :: Map String (Fun a)
  , rules :: [Rule a]
  }

createASM :: (Eq a) => Signature -> Map String (Fun a) -> [a] -> [Rule a] -> Either String (ASM a)
createASM sig statics elems ruleset = if (validStatics (staticS sig) (statics))
  then Right $ ASM {
    universe = fmap EVal elems,
    inF = createUndefFunctions (inS sig),
    controlledF = createUndefFunctions (controlledS sig),
    outF = createUndefFunctions (outS sig),
    sharedF = createUndefFunctions (sharedS sig),
    staticF = statics,
    rules = ruleset
  }
  else Left "Invalid or unknown static Function"


createUndefFunctions :: Map String Int -> Map String (Fun a)
createUndefFunctions = Map.mapWithKey sigToUndefFun

sigToUndefFun :: String -> Int -> Fun a
sigToUndefFun name arity = Fun name arity (\x -> EUndef)

validStatics :: Map String Int -> Map String (Fun a) -> Bool
validStatics sig def = Map.foldWithKey (compareDef sig) True def
  where
    compareDef :: Map String Int -> String -> Fun a -> Bool -> Bool
    compareDef sig name (Fun n a f) prev = (&&) prev $
      case Map.lookup name sig of
        Just(a) -> True
        _ -> False

notF :: UElem a -> UElem a
notF ETrue = EFalse
notF EFalse = ETrue
notF _ = EUndef

andF :: UElem a -> UElem a -> UElem a
andF ETrue ETrue = ETrue
andF ETrue EFalse = EFalse
andF EFalse ETrue = EFalse
andF EFalse EFalse = EFalse
andF _ _ = EUndef

-- universe element
data UElem a where
    ETrue :: UElem a
    EFalse :: UElem a
    EUndef :: UElem a
    EVal :: (Eq a) => a -> UElem a
    EReserve :: Int -> UElem a
    EError :: UElem a
deriving instance Eq a => Eq (UElem a)
deriving instance Show a => Show (UElem a)

data Fun a = Fun String Int ([UElem a] -> UElem a)

data Term a =
    App String [Term a]
  | TVar String
  | TVal (UElem a)
deriving instance Eq a => Eq (Term a)
deriving instance Show a => Show (Term a)

replaceT :: String -> UElem a -> Term a -> Term a
replaceT x v (App f ts) = App f $ fmap (replaceT x v) ts
replaceT x v (TVar y) = if (x == y)
  then TVal v
  else TVar y
replaceT x v t = t

evalFun :: Fun a -> [UElem a] -> UElem a
evalFun (Fun n a f) args = if (length args == a)
  then f args
  else EError

eval :: ASM a -> Term a -> UElem a
eval asm (App fn args) = case (fIn,fOut,fShrd,fCtrl,fStc) of
  (Just fun@(Fun n a f),_,_,_,_) -> evalFun fun eArgs
  (_,Just fun@(Fun n a f),_,_,_) -> evalFun fun eArgs
  (_,_,Just fun@(Fun n a f),_,_) -> evalFun fun eArgs
  (_,_,_,Just fun@(Fun n a f),_) -> evalFun fun eArgs
  (_,_,_,_,Just fun@(Fun n a f)) -> evalFun fun eArgs
  where
    fIn = Map.lookup fn (inF asm)
    fOut = Map.lookup fn (outF asm)
    fShrd = Map.lookup fn (sharedF asm)
    fCtrl = Map.lookup fn (controlledF asm)
    fStc = Map.lookup fn (staticF asm)
    eArgs = fmap (eval asm) args
eval asm (TVar s) = EError
eval asm (TVal a) = a

data Rule a =
    Skip
  | Modify String [Term a] (Term a)
  | If (Term a) (Term a) (Rule a)
  | Par [Rule a]
  | Forall String (Term a) (Rule a)
  | Choose String (Term a) (Rule a)
  | Import String (Rule a)

data Update a where
  Update :: (Eq a) => String -> [UElem a] -> UElem a -> Update a
deriving instance Eq a => Eq (Update a)
deriving instance Show a => Show (Update a)

update :: (Eq a) => Fun a -> Update a -> Fun a
update fn@(Fun n1 a f) (Update n2 xs res) = if (n1 == n2 && length xs == a)
  then Fun n1 a $ \fxs -> if (fxs == xs)
    then res
    else f fxs
  else fn

-- do not update static funs
updateFuns :: [Update a] -> ASM a -> ASM a
updateFuns (u@(Update fn vs res):us) asm = case (fIn,fOut,fShrd,fCtrl) of
  (Just fun@(Fun n a f),_,_,_) -> updateFuns us asm {
    inF = Map.insert fn (ASM.update fun u) (inF asm) }
  (_,Just fun@(Fun n a f),_,_) -> updateFuns us asm {
    outF = Map.insert fn (ASM.update fun u) (outF asm) }
  (_,_,Just fun@(Fun n a f),_) -> updateFuns us asm {
    sharedF = Map.insert fn (ASM.update fun u) (sharedF asm) }
  (_,_,_,Just fun@(Fun n a f)) -> updateFuns us asm {
    controlledF = Map.insert fn (ASM.update fun u) (controlledF asm) }
  _ -> updateFuns us asm
  where
    fIn = Map.lookup fn (inF asm)
    fOut = Map.lookup fn (outF asm)
    fShrd = Map.lookup fn (sharedF asm)
    fCtrl = Map.lookup fn (controlledF asm)
updateFuns [] asm = asm

replaceR :: String -> UElem a -> Rule a -> Rule a
replaceR x v (If t1 t2 r) = If
  (replaceT x v t1)
  (replaceT x v t2)
  (replaceR x v r)
replaceR x v (Modify f args res) = Modify f
  (fmap (replaceT x v) args)
  (replaceT x v res)
replaceR x v (Par rs) = Par $ fmap (replaceR x v) rs
replaceR x v (Forall s t r) = Forall s
  (replaceT x v t)
  (replaceR x v r)
replaceR x v (Choose s t r) = Choose s
  (replaceT x v t)
  (replaceR x v r)
replaceR x v (Import s r) = Import s
  (replaceR x v r)
replaceR x v r = r

calcRule :: (Eq a) => ASM a -> StdGen -> Rule a -> Maybe [Update a]
calcRule asm gen Skip = Nothing
calcRule asm gen (Modify fn tArgs tRes) = Just [Update fn uArgs uRes]
  where
    uArgs = fmap (eval asm) tArgs
    uRes = eval asm tRes
calcRule asm gen (If t1 t2 r) = if ((eval asm t1) == (eval asm t2))
  then calcRule asm gen r
  else Nothing
calcRule asm gen (Par rs) =
  fmap concat $ sequence $ List.filter isJust $ fmap (calcRule asm gen) rs
calcRule asm gen (Forall x t r) = calcRule asm gen $ Par $ fmap toIf us
  where
    us = universe asm
    toIf u = If (replaceT x u t) (TVal ETrue) (replaceR x u r)
calcRule asm gen (Choose x t r) = if (length opts > 0)
  then calcRule asm nGen $ replaceR x choice r
  else Nothing
  where
    opts = List.filter (\u -> (eval asm $ replaceT x u t) == ETrue) $ universe asm
    (rnd,nGen) = next gen
    choice = (!!) opts $ mod rnd (length opts)
calcRule asm gen (Import x r) = undefined

step :: (Eq a) => ASM a -> StdGen -> ASM a
step asm gen = if (isInconsistent updates)
  then asm
  else updateFuns updates asm
  where
    res = fmap (calcRule asm gen) (rules asm)
    updates = concat $ concat $ fmap maybeToList $ List.filter isJust res



isInconsistent :: [Update a] -> Bool
isInconsistent upds = Map.fold checkSubset False subsets
  where
    subsets = updatesForSameFunctions upds Map.empty
    checkSubset :: [Update a] -> Bool -> Bool
    checkSubset us prev = prev || isInconsistentSubset us

isInconsistentSubset :: [Update a] -> Bool
isInconsistentSubset ((u@(Update name vals res)):us) =
  noDifferent && isInconsistentSubset otherVals
  where
    sameVals = List.filter (\(Update n' v' r') -> vals == v') us
    otherVals = (List.\\) us sameVals
    noDifferent = (||) ((length us) == 0) $
      all (\(Update n' v' r') -> r' == res) sameVals
isInconsistentSubset [] = False

updatesForSameFunctions :: [Update a] -> Map String [Update a] -> Map String [Update a]
updatesForSameFunctions ((u@(Update name vals res)):us) m = m'
  where
    m' = Map.insertWith (++) name [u] m
updatesForSameFunctions [] m = m




{- Exapmle ASMs -}


testSig :: Signature
testSig = Signature
  { staticS = Map.fromList [("f0",0), ("f1",1), ("f2",2), ("f3",1)]
  , controlledS = Map.empty
  , inS = Map.empty
  , outS = Map.empty
  , sharedS = Map.fromList [("s1",1)]
  }

toUElemBool :: Bool -> UElem a
toUElemBool True = ETrue
toUElemBool False = EFalse

evenF :: UElem Int -> UElem Int
evenF (EVal x) = toUElemBool (even x)
evenF _ = EUndef

plusF :: [UElem Int] -> UElem Int
plusF ((EVal x):(EVal y):zs) = EVal $ x + y

testStatics :: Map String (Fun Int)
testStatics = Map.fromList [
  ("f0", Fun "f0" 0 (\x -> ETrue)),
  ("f1", Fun "f1" 1 (\x -> evenF $ head x)),
  ("f2", Fun "f2" 2 (\(x:y:zs) -> andF x y)),
  ("f3", Fun "f3" 1 (\x -> plusF ((EVal 0) : [head x])))]

testUniverse :: [Int]
testUniverse = [1..10]

testRules :: [Rule Int]
testRules = [
  (Choose "x"
    (App "f1" [TVar "x"])
    (Modify "s1" [TVar "x"] (TVar "x"))
  )]


testASM = createASM testSig testStatics testUniverse testRules

isRight :: Either a b -> Bool
isRight (Right _) = True
isRight _ = False

fromRight :: Either a b -> b
fromRight (Right x) = x

asm1 = fromRight testASM
asm2 = step asm1 $ mkStdGen 1

testEval asm fn args = eval asm (App fn args)

instance (Show a) => Show (Rule a) where
  show (Modify x s r) = "Modify " ++ (show x) ++ " | " ++ (show s) ++ " | " ++ (show r)
  show (Par rs) = concatMap ((++ " ; ") . show) rs
  show _ = "?"

t = replaceT "x" (EVal (2::Int)) (App "f1" [TVar "x"])
r = replaceR "x" (EVal (2::Int)) (Modify "s1" [TVar "x"] (TVal (EVal 0)))
c = calcRule asm1 (mkStdGen 1) (If t (TVal ETrue) r)
