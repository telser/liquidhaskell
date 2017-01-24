{-# LANGUAGE ImplicitParams        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE EmptyDataDecls        #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE DoAndIfThenElse       #-}

--------------------------------------------------------------------------------
-- | Axiom Instantiation  ------------------------------------------------------
--------------------------------------------------------------------------------

module Language.Haskell.Liquid.Constraint.Instantiate (

  instantiateAxioms

  ) where


-- import           Language.Fixpoint.Misc            
import           Language.Fixpoint.Types hiding (Eq, simplify)
import qualified Language.Fixpoint.Types as F        
import           Language.Fixpoint.Types.Visitor (eapps, mapExpr)            

import           Language.Haskell.Liquid.Constraint.Types hiding (senv)


import qualified Data.List as L 
import Data.Maybe (catMaybes)

import qualified Debug.Trace as T 

import System.IO.Unsafe
import Control.Monad

trace :: AxiomEnv -> String -> a -> a 
trace aenv str x 
  | aenvVerbose aenv
  = T.trace str x 
  | otherwise
  = x 

instantiateAxioms :: BindEnv  -> AxiomEnv -> FixSubC -> FixSubC
instantiateAxioms _  aenv sub
  | not (aenvExpand aenv sub)
  = sub  
instantiateAxioms bds aenv sub 
  = strengthenLhs (pAnd is) sub
  where
    is               = instances maxNumber aenv (pAnd initExpressions) (trace aenv initMsg $ initOccurences)
    initExpressions  = (expr $ slhs sub):(expr $ srhs sub):(expr <$> envCs bds (senv sub))
    initOccurences   = concatMap (makeInitOccurences as eqs) initExpressions

    as  = (,fuelNumber) . eqName <$> (filter (not . null . eqArgs) $ aenvEqs aenv)
    eqs = aenvEqs  aenv

    showMaybeVar sub   = case subVar sub of 
                           Just x  -> " for " ++ show x
                           Nothing -> "" 

    fuelNumber    = aenvFuel aenv sub 
    initOccNumber = length initOccurences
    axiomNumber   = length $ aenvSyms aenv
    maxNumber     =  (axiomNumber * initOccNumber) ^ fuelNumber
    initMsg = "\nStart instantiation" ++ showMaybeVar sub ++ 
              " with fuel = " ++ show fuelNumber ++ " init occurences = " ++ show initOccNumber ++ " axioms = " ++ show axiomNumber ++ 
              " can generate up to " ++ show maxNumber ++ " instantiations\n" 


instances :: Int -> AxiomEnv -> Expr -> [Occurence] -> [Expr] 
instances maxIs aenv einit !occs 
  = (eqBody <$> eqsZero) ++ is ++ evals 
  where
    (eqsZero, eqs) = L.partition (null . eqArgs) (aenvEqs  aenv)
    is             = instancesLoop aenv maxIs einit eqs occs
    evals          = concatMap (runLazyEval aenv) occs 


-------------------------------------------------------------------------------
--------  Equations by Lazy Evaluation ----------------------------------------
-------------------------------------------------------------------------------

{-

seq (seq (seq (pure compose) x) y) z
-> 
seq (seq (seq (Just compose) x) y) z
-> 
seq (seq (Just ((fromJust (Just compose)) fromJust x)) y) z
-> 
seq (seq (Just (compose (fromJust x))) y) z
-> 
seq (seq (Just (compose (fromJust x))) y) z

-}


runLazyEval :: AxiomEnv -> Occurence -> [Expr]
runLazyEval aenv occ 
  = T.trace ("INIT EVAL EQUATIONS FOR = " ++ show occ ++ "\nARE\n" ++ showpp eqs ++ "\nEVALS\n" ++ showpp es) eqs
  where 
    eqs = catMaybes [ (PAtom F.Eq e) <$> evalOne eq e | eq <- aenvEqs aenv, e <- oargs occ, eqInfo eq == EqAxiom]
    es  = evaluate 5 (aenvEqs aenv) $ eApps (EVar (ofun occ)) (oargs occ)

-- seq (seq (pure compose) x##a1gY) y##a1gZ


evaluate :: Int -> [Equation] -> Expr -> (Int, Expr) 
evaluate i eqs e 
  | null es = (i, e)
  | otherwise
  = eval j (eApps f es')
  where 
    (f, es) = splitEApp e 
    (j, es') = evals i [] es

    evals i acc es | i <= 0 = (i, (acc ++ es)
    evals i acc (e:es) = let (j, e') = evaluate i eqs e in 
                         if j < i then evals j acc (e':es)
                         else let (jj, e'') = eval i e in 
                         if jj == i then evals i (e':acc) es else  evals jj acc (e'':es)
    evals i acc []  = (i, reverse acc)


    eval i e | i <= 0 = (i, e)
    eval i e = case catMaybes [evalOne eq e | eq <- eqs] of
                  e':_ -> (i-1, T.trace ("\nEVAL:\n" ++ showpp e ++ " -> " ++ showpp e'++ "\n") e')
                  []   -> (i, T.trace ("\nDoes not evaluate: " ++ showpp e) e)   


evalOne :: Equation -> Expr -> Maybe Expr 
evalOne eq e
  | (EVar x, es) <-  splitEApp e 
  , eqName eq == x 
  , length (eqArgs eq) == length es 
  -- CHECK THIS 
  , PAnd (PAtom F.Eq v ebd:_) <- eqBody eq
  , v == F.eApps (F.EVar x) (F.EVar <$> eqArgs eq)
  = Just $ subst (mkSubst (zip (eqArgs eq) es)) ebd
  | otherwise
  = Nothing 

{- 
evalOne eq e 
  = T.trace ("\nBad eq\n" ++ show eq ++ "\nFOR\n" ++ showpp e ++ "\nSPLIT\n" ++ showpp e
             ++ "\nCMP1 = " ++ show (EVar (eqName eq) == f)
             ++ "\nCMP2 = " ++ show (length (eqArgs eq) == length xs)
             ++ "\nCMP3 = " ++ show (checkEq (eqBody eq)) 
            ) Nothing 
  where
    (f, xs) = splitEApp e 
    checkEq (PAtom F.Eq _ _) = True 
    checkEq _ = False
-}










-- Currently: Instantiation happens arbitrary times (in recursive functions it diverges)
-- Step 1: Hack it so that instantiation of axiom A happens from an occurences and its 
-- subsequent instances <= FUEL times 
-- How? Hack expressions to contatin fuel info within eg Cst
-- Step 2: Compute fuel based on Ranjit's algorithm

instancesLoop :: AxiomEnv -> Int -> Expr ->  [Equation] -> [Occurence] -> [Expr]
instancesLoop aenv maxIns _einit eqs = go 0 [] []
  where 
    go :: Int -> [Expr] -> [Occurence] -> [Occurence] -> [Expr]
    go !i acc oldoccs occs = let is      = concatMap (applySimplifications (aenvSims aenv)) $ concatMap (unfold eqs) occs 
                                 newIs   = findNewEqs is acc 
                                 newOccs = {- selectOccs $ -} filter (not . (\e -> elemBy eqOcc e oldoccs)) $ nubOccurences $ concatMap (grepOccurences eqs) newIs
                                 msg     = show (i + length newIs) ++ "/" ++ (show maxIns) --  ++  "\n\nNewOccs\n" ++ L.intercalate "\n" (show  <$> filter (\oc -> oinfo oc == EqAxiom) newOccs) -- ++ L.intercalate "\n" (showExpr . fst <$> newIs)  -- ++ "\n\nOccurences\n" ++ show occs ++   "\n\nEquations\n" ++ show eqs ++  "\n\nNew Occs\n" ++ show newOccs ++ )
                             in  if null newIs then acc else go (trace aenv msg (i + length newIs)) ((fst <$> newIs) ++ acc) (oldoccs ++ occs) newOccs



elemBy :: (a -> a -> Bool) -> a -> [a] -> Bool
elemBy _ _ [] = False
elemBy cmp x (y:ys) 
  | cmp x y   = True 
  | otherwise = elemBy cmp x ys 

_selectOccs :: [Occurence] -> [Occurence]
_selectOccs occs = unsafePerformIO $ do 
  putStrLn "Do you want to select occurences? [Y/N]"
  c <- getYNChar
  if (c == 'N') 
    then (return occs)
    else (putStrLn ("All occs = " ++ show occs) >> filterM selectOc occs)

  where
  selectOc oc | oinfo oc == EqMeasure = return True  
  selectOc oc = 
    do putStrLn ("Keep that? [Y/N]\n" ++ show oc)
       c <- getYNChar
       return (c == 'Y')

  getYNChar = do 
    c <- getChar 
    if (c == 'Y' || c == 'y')
      then return 'Y'
      else if (c == 'N' || c == 'n')
        then return 'N'
        else (putStrLn "Type Y or N" >> getYNChar)


nubOccurences :: [Occurence] -> [Occurence]
nubOccurences occs = mergeOccs <$> groupBy eqOcc occs
  where
    mergeOccs x = (head x){ofuel = maxFuelMap (map ofuel x)}

eqOcc :: Occurence -> Occurence -> Bool
eqOcc occ1 occ2 = oargs occ1 == oargs occ2 && ofun occ1 == ofun occ2 


groupBy :: (a -> a -> Bool) -> [a] -> [[a]]
groupBy _ []     = [] 
groupBy cmp (x:xs) = (x:xs1):groupBy cmp xs2
  where
    (xs1,xs2) = L.partition (cmp x) xs

maxFuelMap :: [FuelMap] -> FuelMap
maxFuelMap fs = mergeMax <$> L.transpose fs
  where 
    mergeMax :: FuelMap -> (Symbol, Fuel)
    mergeMax xfs = let (xs, fs) = unzip xfs in (head xs, maximum fs)


findNewEqs :: [(Expr, FuelMap)] -> [Expr] -> [(Expr, FuelMap)]
findNewEqs [] _ = []
findNewEqs ((e, f):xss) es 
  | e `elem` es = findNewEqs xss es 
  | otherwise   = (e,f):findNewEqs xss es 

applySimplifications :: [Simplify] -> (Expr, FuelMap) -> [(Expr, FuelMap)]
applySimplifications sis (e, fm) 
  = (e,fm):[(es,fm) | Just es <- (`simplify` e) <$> sis] 

simplify :: Simplify -> Expr -> Maybe Expr
simplify si ee  = if ee == esimple then Nothing else Just $  esimple
  where
    esimple = mapExpr f ee 
    f e = case unify (sargs si) (scomplex si) e of 
            Just su -> let simple = subst (mkSubst su) (ssimple si) in simple -- T.trace ("\n\nSimplify\n" ++ showpp e ++ "\nto\n" ++ showpp simple ++ "\nin\n" ++ showpp ee) simple
            Nothing -> e

unify :: [Symbol] -> Expr -> Expr -> Maybe [(Symbol, Expr)]
unify xs ex e = go [] ex e 
  where
    go acc (EVar x) e 
      | x `elem` xs, Nothing <- L.lookup x acc
      = Just ((x,e):acc)
    go acc (EVar x) e 
      | x `elem` xs, Just e' <- L.lookup x acc, e == e'
      = Just acc
    go acc (EApp e1 e2) (EApp e1' e2')
      = do su1 <- go acc e1 e1' 
           go su1 e2 e2'
    go acc (PAnd es) (PAnd es')
      = go' acc es es'
    go acc e1 e2 
      | e1 == e2
      = Just acc 
    go _ _ _ 
      = Nothing

    go' acc [] [] = Just acc 
    go' acc (e1:es1) (e2:es2) 
      = do su <- go acc e1 e2
           go' su es1 es2
    go' _ _ _ = Nothing 



makeInitOccurences :: [(Symbol, Fuel)] -> [Equation] -> Expr -> [Occurence]
makeInitOccurences xs eqs e 
  = [Occ x es xs eqi | (EVar x, es) <- splitEApp <$> eapps e
                 , Eq x' xs' _ eqi <- eqs, x == x'
                 , length xs' == length es]  

grepOccurences :: [Equation] -> (Expr, FuelMap) -> [Occurence]
grepOccurences eqs (e, fs) 
  = filter (goodFuelMap . ofuel)  
           [Occ x es fs eqi | (EVar x, es) <- splitEApp <$> eapps e
                        , Eq x' xs' _ eqi <- eqs, x == x'
                        , length xs' == length es]  

goodFuelMap :: FuelMap -> Bool 
goodFuelMap = any ((>0) . snd)

unfold :: [Equation] -> Occurence -> [(Expr, FuelMap)]
unfold eqs (Occ x es fs _) 
  = catMaybes [if hasFuel fs x then Just (subst (mkSubst $ zip  xs' es) e, makeFuelMap (\x -> x-1) fs x) else Nothing 
              | Eq x' xs' e _ <- eqs
              , x == x'
              , length xs' == length es]  

hasFuel :: FuelMap -> Symbol -> Bool 
hasFuel fm x = maybe True (\x -> 0 < x) (L.lookup x fm)


makeFuelMap :: (Fuel -> Fuel) -> FuelMap -> Symbol -> FuelMap

{- 
makeFuelMap' :: (Fuel -> Fuel) -> FuelMap -> Symbol -> FuelMap
makeFuelMap' f fm x = let fm' = makeFuelMap f fm x in  
                      -- T.trace ("New fuel map for " ++ show x ++ "\n OLD = " ++ show (snd <$> fm) ++ "\n NEW = " ++ show (snd <$> fm')) 
                      fm'
-}
makeFuelMap f ((x, fx):fs) y  
  | x == y    = (x, f fx) : fs
  | otherwise = (x, fx)   : makeFuelMap f fs y
makeFuelMap _ _ _ = error "makeFuelMap"


type Fuel = Int 
type FuelMap = [(Symbol, Fuel)]

data Occurence = Occ {ofun :: Symbol, oargs :: [Expr], ofuel :: FuelMap, oinfo :: EqInfo}

instance Show Occurence where
  show occ = showpp (ofun occ) ++ "(" ++ showpp (oargs occ) ++ ")" -- ++ " fuel =" ++ show (ofuel occ)





{- 

showExpr :: Expr -> String 
showExpr (PAnd eqs) 
  = L.intercalate "\n" (showpp . lhs <$> eqs )
  where
    lhs (PAtom F.Eq l _) = l 
    lhs e                = e 
showExpr e = showpp e 
-}


instance Expression (Symbol, SortedReft) where
  expr (x, RR _ (Reft (v, r))) = subst1 (expr r) (v, EVar x)
