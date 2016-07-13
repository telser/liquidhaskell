{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.Haskell.Liquid.Constraint.Fresh
  (
  -- * Types that can be refreshed
    Freshable(..)

  )
  where

import qualified Data.List                      as L
import qualified Data.HashMap.Strict            as M
import           Control.Monad.State            (get, put, modify)
import           Prelude                        hiding (error)

import           Var      (Var)
-- import           Language.Fixpoint.Types
import qualified Language.Fixpoint.Types as F
import           Language.Haskell.Liquid.Misc  (single)
import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.Types.RefType
import           Language.Haskell.Liquid.Constraint.Types

class (Applicative m, Monad m) => Freshable m a where
  fresh   :: m a
  true    :: a -> m a
  true    = return
  refresh :: a -> m a
  refresh = return

instance Freshable CG Integer where
  fresh = do s <- get
             let n = freshIndex s
             put $ s { freshIndex = n + 1 }
             return n

instance Freshable m Integer => Freshable m F.Symbol where
  fresh = F.tempSymbol "x" <$> fresh

instance Freshable m Integer => Freshable m F.Expr where
  fresh  = kv <$> fresh
    where
      kv = (`F.PKVar` mempty) . F.intKvar

instance Freshable m Integer => Freshable m [F.Expr] where
  fresh = single <$> fresh

instance Freshable m Integer => Freshable m F.Reft where
  fresh                  = panic Nothing "fresh Reft"
  true    (F.Reft (v,_)) = return $ F.Reft (v, mempty)
  refresh (F.Reft (_,_)) = (F.Reft .) . (,) <$> freshVV <*> fresh
    where
      freshVV            = F.vv . Just <$> fresh

instance Freshable m Integer => Freshable m RReft where
  fresh             = panic Nothing "fresh RReft"
  true (MkUReft r _ s)    = MkUReft <$> true r    <*> return mempty <*> true s
  refresh (MkUReft r _ s) = MkUReft <$> refresh r <*> return mempty <*> refresh s

instance Freshable m Integer => Freshable m Strata where
  fresh      = (:[]) . SVar <$> fresh
  true []    = fresh
  true s     = return s
  refresh [] = fresh
  refresh s  = return s

instance (Freshable m Integer, Freshable m r, F.Reftable r ) => Freshable m (RRType r) where
  fresh   = panic Nothing "fresh RefType"
  refresh = refreshRefType
  true    = trueRefType

-----------------------------------------------------------------------------------------------
trueRefType :: (Freshable m Integer, Freshable m r, F.Reftable r) => RRType r -> m (RRType r)
-----------------------------------------------------------------------------------------------
trueRefType (RAllT α t)
  = RAllT α <$> true t

trueRefType (RAllP π t)
  = RAllP π <$> true t

trueRefType (RFun _ t t' _)
  = rFun <$> fresh <*> true t <*> true t'

trueRefType (RApp c ts _  _) | isClass c
  = rRCls c <$> mapM true ts

trueRefType (RApp c ts rs r)
  = RApp c <$> mapM true ts <*> mapM trueRef rs <*> true r

trueRefType (RAppTy t t' _)
  = RAppTy <$> true t <*> true t' <*> return mempty

trueRefType (RVar a r)
  = RVar a <$> true r

trueRefType (RAllE y ty tx)
  = do y'  <- fresh
       ty' <- true ty
       tx' <- true tx
       return $ RAllE y' ty' (tx' `F.subst1` (y, F.EVar y'))

trueRefType (RRTy e o r t)
  = RRTy e o r <$> trueRefType t

trueRefType t
  = return t

trueRef :: (F.Reftable r, Freshable f r, Freshable f Integer)
        => Ref τ (RType RTyCon RTyVar r) -> f (Ref τ (RRType r))
trueRef (RProp _ (RHole _)) = panic Nothing "trueRef: unexpected RProp _ (RHole _))"
trueRef (RProp s t) = RProp s <$> trueRefType t


-----------------------------------------------------------------------------------------------
refreshRefType :: (Freshable m Integer, Freshable m r, F.Reftable r) => RRType r -> m (RRType r)
-----------------------------------------------------------------------------------------------
refreshRefType (RAllT α t)
  = RAllT α <$> refresh t

refreshRefType (RAllP π t)
  = RAllP π <$> refresh t

refreshRefType (RFun b t t' _)
  | b == F.dummySymbol = rFun <$> fresh <*> refresh t <*> refresh t'
  | otherwise          = rFun     b     <$> refresh t <*> refresh t'

refreshRefType (RApp rc ts _ _) | isClass rc
  = return $ rRCls rc ts

refreshRefType (RApp rc ts rs r)
  = RApp rc <$> mapM refresh ts <*> mapM refreshRef rs <*> refresh r

refreshRefType (RVar a r)
  = RVar a <$> refresh r

refreshRefType (RAppTy t t' r)
  = RAppTy <$> refresh t <*> refresh t' <*> refresh r

refreshRefType (RAllE y ty tx)
  = do y'  <- fresh
       ty' <- refresh ty
       tx' <- refresh tx
       return $ RAllE y' ty' (tx' `F.subst1` (y, F.EVar y'))

refreshRefType (RRTy e o r t)
  = RRTy e o r <$> refreshRefType t

refreshRefType t
  = return t

refreshRef :: (F.Reftable r, Freshable f r, Freshable f Integer)
           => Ref τ (RType RTyCon RTyVar r) -> f (Ref τ (RRType r))
refreshRef (RProp _ (RHole _)) = panic Nothing "refreshRef: unexpected (RProp _ (RHole _))"
refreshRef (RProp s t) = RProp <$> mapM freshSym s <*> refreshRefType t

freshSym :: Freshable f a => (t, t1) -> f (a, t1)
freshSym (_, t)        = (, t) <$> fresh


--------------------------------------------------------------------------------
refreshTy :: SpecType -> CG SpecType
--------------------------------------------------------------------------------
refreshTy t = refreshVV t >>= refreshArgs

refreshVV :: Freshable m Integer => SpecType -> m SpecType
refreshVV (RAllT a t) = RAllT a <$> refreshVV t
refreshVV (RAllP p t) = RAllP p <$> refreshVV t

refreshVV (REx x t1 t2)
  = do [t1', t2'] <- mapM refreshVV [t1, t2]
       shiftVV (REx x t1' t2') <$> fresh

refreshVV (RFun x t1 t2 r)
  = do [t1', t2'] <- mapM refreshVV [t1, t2]
       shiftVV (RFun x t1' t2' r) <$> fresh

refreshVV (RAppTy t1 t2 r)
  = do [t1', t2'] <- mapM refreshVV [t1, t2]
       shiftVV (RAppTy t1' t2' r) <$> fresh

refreshVV (RApp c ts rs r)
  = do ts' <- mapM refreshVV ts
       rs' <- mapM refreshVVRef rs
       shiftVV (RApp c ts' rs' r) <$> fresh

refreshVV t
  = return t

refreshVVRef :: Freshable m Integer
             => Ref b (RType RTyCon RTyVar RReft)
             -> m (Ref b (RType RTyCon RTyVar RReft))
refreshVVRef (RProp ss (RHole r))
  = return $ RProp ss (RHole r)

refreshVVRef (RProp ss t)
  = do xs    <- mapM (const fresh) (fst <$> ss)
       let su = F.mkSubst $ zip (fst <$> ss) (F.EVar <$> xs)
       (RProp (zip xs (snd <$> ss)) . F.subst su) <$> refreshVV t

refreshArgsTop :: (Var, SpecType) -> CG SpecType
refreshArgsTop (x, t)
  = do (t', su) <- refreshArgsSub t
       modify $ \s -> s {termExprs = M.adjust (F.subst su <$>) x $ termExprs s}
       return t'

refreshArgs :: SpecType -> CG SpecType
refreshArgs t
  = fst <$> refreshArgsSub t


-- NV TODO: this does not refresh args if they are wrapped in an RRTy
refreshArgsSub :: SpecType -> CG (SpecType, F.Subst)
refreshArgsSub t
  = do ts     <- mapM refreshArgs ts_u
       xs'    <- mapM (const fresh) xs
       let sus = F.mkSubst <$> L.inits (zip xs (F.EVar <$> xs'))
       let su  = last sus
       ts'    <- mapM refreshPs $ zipWith F.subst sus ts
       let rs' = zipWith F.subst sus rs
       tr     <- refreshPs $ F.subst su tbd
       let t'  = fromRTypeRep $ trep {ty_binds = xs', ty_args = ts', ty_res = tr, ty_refts = rs'}
       return (t', su)
    where
       trep    = toRTypeRep t
       xs      = ty_binds trep
       ts_u    = ty_args  trep
       tbd     = ty_res   trep
       rs      = ty_refts trep

refreshPs :: SpecType -> CG SpecType
refreshPs = mapPropM go
  where
    go (RProp s t) = do t'    <- refreshPs t
                        xs    <- mapM (const fresh) s
                        let su = F.mkSubst [(y, F.EVar x) | (x, (y, _)) <- zip xs s]
                        return $ RProp [(x, t) | (x, (_, t)) <- zip xs s] $ F.subst su t'
