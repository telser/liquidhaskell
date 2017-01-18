{-# LANGUAGE ImplicitParams        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE EmptyDataDecls        #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE FlexibleInstances     #-}

--------------------------------------------------------------------------------
-- | Axiom Instantiation  ------------------------------------------------------
--------------------------------------------------------------------------------

module Language.Haskell.Liquid.Constraint.Instantiate (

  instantiateAxioms

  ) where


-- import           Language.Fixpoint.Misc            
import           Language.Fixpoint.Types hiding (Eq, simplify)
-- import qualified Language.Fixpoint.Types as F        
import           Language.Fixpoint.Types.Visitor (eapps, mapExpr)            

import           Language.Haskell.Liquid.Constraint.Types hiding (senv)


import qualified Data.List as L 
import Data.Maybe (catMaybes)

import qualified Debug.Trace as T 

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
    is               = instances maxNumber aenv (trace aenv initMsg $ initOccurences)
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


instances :: Int -> AxiomEnv -> [Occurence] -> [Expr] 
instances maxIs aenv !occs 
  = (eqBody <$> eqsZero) ++ is
  where
    (eqsZero, eqs) = L.partition (null . eqArgs) (aenvEqs  aenv)
    is             = instancesLoop aenv maxIs eqs occs

-- Currently: Instantiation happens arbitrary times (in recursive functions it diverges)
-- Step 1: Hack it so that instantiation of axiom A happens from an occurences and its 
-- subsequent instances <= FUEL times 
-- How? Hack expressions to contatin fuel info within eg Cst
-- Step 2: Compute fuel based on Ranjit's algorithm

instancesLoop :: AxiomEnv -> Int ->  [Equation] -> [Occurence] -> [Expr]
instancesLoop aenv maxIns eqs = go 0 [] 
  where 
    go :: Int -> [Expr] -> [Occurence] -> [Expr]
    go !i acc occs = let is      = concatMap (applySimplifications (aenvSims aenv)) $ concatMap (unfold eqs) occs 
                         newIs   = findNewEqs is acc 
                         newOccs = nubOccurences $ concatMap (grepOccurences eqs) newIs
                         msg     = show (i + length newIs) ++ "/" ++ (show maxIns) --  ++  "\n\nNewExpr\n" ++ L.intercalate "\n" (showExpr . fst <$> newIs)  -- ++ "\n\nOccurences\n" ++ show occs ++   "\n\nEquations\n" ++ show eqs ++  "\n\nNew Occs\n" ++ show newOccs ++ )
                     in  if null newIs then acc else go (trace aenv msg (i + length newIs)) ((fst <$> newIs) ++ acc) newOccs

nubOccurences :: [Occurence] -> [Occurence]
nubOccurences occs = mergeOccs <$> L.groupBy eqOcc occs 
  where
    eqOcc occ1 occ2 = oargs occ1 == oargs occ2 && ofun occ1 == ofun occ2 
    mergeOccs x = (head x){ofuel = maxFuelMap (map ofuel x)}


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
            Just su -> let simple = subst (mkSubst su) (ssimple si) in T.trace ("\n\nSimplify\n" ++ showpp e ++ "\nto\n" ++ showpp simple ++ "\nin\n" ++ showpp ee) simple
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
  = [Occ x es xs | (EVar x, es) <- splitEApp <$> eapps e
                 , Eq x' xs' _ <- eqs, x == x'
                 , length xs' == length es]  

grepOccurences :: [Equation] -> (Expr, FuelMap) -> [Occurence]
grepOccurences eqs (e, fs) 
  = filter (goodFuelMap . ofuel)  
           [Occ x es fs | (EVar x, es) <- splitEApp <$> eapps e
                        , Eq x' xs' _ <- eqs, x == x'
                        , length xs' == length es]  

goodFuelMap :: FuelMap -> Bool 
goodFuelMap = any ((>0) . snd)

unfold :: [Equation] -> Occurence -> [(Expr, FuelMap)]
unfold eqs (Occ x es fs) 
  = catMaybes [if hasFuel fs x then Just (subst (mkSubst $ zip  xs' es) e, makeFuelMap (\x -> x-1) fs x) else Nothing 
              | Eq x' xs' e <- eqs
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

data Occurence = Occ {ofun :: Symbol, oargs :: [Expr], ofuel :: FuelMap}
 deriving (Show)


type Fuel = Int 

type FuelMap = [(Symbol, Fuel)]



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
