{-@ LIQUID "--higherorder"     @-}
{- LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}


{-# LANGUAGE IncoherentInstances   #-}
{-# LANGUAGE FlexibleContexts #-}
module ListFunctors where

import Prelude hiding (fmap, id, Maybe(..), seq, pure)

import Language.Haskell.Liquid.ProofCombinators
import Helper

-- | Applicative Laws :
-- | identity      pure id <*> v = v
-- | composition   pure (.) <*> u <*> v <*> w = u <*> (v <*> w)
-- | homomorphism  pure f <*> pure x = pure (f x)
-- | interchange   u <*> pure y = pure ($ y) <*> u


{-@ axiomatize pure @-}
pure :: a -> Maybe a
pure x = Just x

{-@ axiomatize seq @-}
seq :: Maybe (a -> b) -> Maybe a -> Maybe b
seq (Just f) (Just x) = Just (f x)
seq _         _       = Nothing

{-@ axiomatize fmap @-}
fmap :: (a -> b) -> Maybe a -> Maybe b
fmap f (Just x) = Just (f x)
fmap f Nothing  = Nothing

{-@ axiomatize id @-}
id :: a -> a
id x = x

{-@ axiomatize idollar @-}
idollar :: a -> (a -> b) -> b
idollar x f = f x

{-@ axiomatize compose @-}
compose :: (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)


-- | Identity

{-@ identity :: x:Maybe a -> {v:Proof | seq (pure id) x == x } @-}
identity :: Maybe a -> Proof
identity Nothing
  = trivial 
identity (Just x)
  = trivial 


-- | Composition

{-@ composition :: x:Maybe (a -> a)
                -> y:Maybe (a -> a)
                -> z:Maybe a
                -> {v:Proof | (seq (seq (seq (pure compose) x) y) z) = seq x (seq y z) } @-}
composition :: Maybe (a -> a) -> Maybe (a -> a) -> Maybe a -> Proof
composition Nothing y z
   = trivial

composition x Nothing z
   = trivial 

composition x y Nothing
   = trivial 


composition (Just x) (Just y) (Just z) = (compose x y z *** QED )
{- 
 = seq (seq (seq (pure compose) (Just x)) (Just y)) (Just z)
        ==. seq (seq (seq (Just compose) (Just x)) (Just y)) (Just z)
        ==. seq (seq (Just (compose x)) (Just y)) (Just z)
        ==. seq (Just (compose x y)) (Just z)
        ==. Just (compose x y z)
--         ==. Just (x (y z)) 
--         ==. seq (Just x) (Just (y z))
--         ==. seq (Just x) (seq (Just y) (Just z))
        *** QED 
-}
-- | homomorphism  pure f <*> pure x = pure (f x)

{-@ homomorphism :: f:(a -> a) -> x:a
                 -> {v:Proof | seq (pure f) (pure x) == pure (f x) } @-}
homomorphism :: (a -> a) -> a -> Proof
homomorphism f x
  = trivial


-- | interchange
interchange :: Maybe (a -> a) -> a -> Proof
{-@ interchange :: u:(Maybe (a -> a)) -> y:a
     -> {v:Proof | seq u (pure y) == seq (pure (idollar y)) u }
  @-}
interchange Nothing y  = trivial
interchange (Just _) y = trivial


data Maybe a = Nothing | Just a
{-@ data Maybe a = Nothing | Just a @-}












