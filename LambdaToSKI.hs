{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}

module LambdaToSKI where

import Data.Proxy
import Data.Functor.Identity
import Data.Functor.Const

{-
References:

KISELYOV, O. λ to ski, semantically. In Functional and Logic Programming (Cham, 2018), J. P. Gallagher and M. Sulzmann, Eds., Springer International Publishing, pp. 33–50.

KISELYOV, O. Typed tagless final interpreters. In Proceedings of the 2010 International Spring School Conference on Generic and Indexed Programming (Berlin, Heidelberg, 2012), SSGIP’10, Springer-Verlag, pp. 130–174.

https://github.com/gallais/potpourri/blob/master/haskell/strongly-scoped/Lambda.hs

https://github.com/dramforever/haskell-stuff/blob/master/de-bruijn-a-la-carte-alt.hs
-}

class Lambda repr where
  z :: repr (a, gamma) a
  s :: repr (b, gamma) a -> repr (any, (b, gamma)) a
  lam :: repr (a, gamma) b -> repr gamma (a -> b)
  app :: repr gamma (a -> b) -> repr gamma a -> repr gamma b

type family a :==: b where
  a :==: a = 'True
  a :==: b = 'False

class AutoLift (gamma :: *) (gamma' :: *) (flag :: Bool) where
  autoLift :: (Lambda r) => Proxy flag -> r gamma t -> r gamma' t

type AutoLiftCtx gamma gamma' flag = ((gamma :==: gamma') ~ flag, AutoLift gamma gamma' flag)

instance AutoLift a a 'True where
  autoLift _ = id

instance (AutoLiftCtx gamma (b, gamma') flag) => AutoLift gamma (any, (b, gamma')) 'False where
  autoLift _ = s . autoLift (Proxy :: Proxy flag)

hlam :: forall a b r gamma. (Lambda r) => 
  ((forall gamma' flag. AutoLiftCtx (a, gamma) gamma' flag => r gamma' a) -> r (a, gamma) b) -> r gamma (a -> b)
hlam f = lam (f var)
  where var :: forall gamma' flag. (AutoLiftCtx (a, gamma) gamma' flag) => r gamma' a
        var = autoLift (Proxy :: Proxy flag) (z :: r (a, gamma) a)

(#) :: (Lambda r) => r gamma (a -> b) -> r gamma a -> r gamma b
(#) = app

class SKIC repr where
  capp :: repr (a -> b) -> repr a -> repr b
  
  cI :: repr (a -> a)
  cI = cS `capp` cK `capp` cK
  
  cK :: repr (a -> b -> a)
  
  cS :: repr ((a -> b -> c) -> (a -> b) -> a -> c)
  
  cB :: repr ((a -> b) -> (c -> a) -> c -> b)
  cB = cS `capp` (cK `capp` cS) `capp` cK
  
  cC :: repr ((a -> b -> c) -> b -> a -> c)
  cC = cS `capp` (cK `capp` (cS `capp` (cK `capp` (cS `capp` cS `capp` (cK `capp` cK))) `capp` cK)) `capp` cS

data Conv :: (* -> *) -> * -> * -> * where
  C :: r a -> Conv r gamma a
  V :: Conv r (a, gamma) a
  N :: Conv r gamma (a -> b) -> Conv r (a, gamma) b
  W :: Conv r gamma a -> Conv r (any, gamma) a

instance (SKIC r) => Lambda (Conv r) where
  z = V
  s = W
  
  app (W e1) (W e2) = W (e1 `app` e2)
  app (W e)  (C d)  = W (e `app` C d)
  app (C d)  (W e)  = W (C d `app` e)
  app (W e1) (N e2) = N (C cB `app` e1 `app` e2)
  app (N e1) (W e2) = N (C cC `app` e1 `app` e2)
  app (W e)    V    = N e
  app   V    (W e)  = N (C (cC `capp` cI) `app` e)
  app (N e1) (N e2) = N (C cS `app` e1 `app` e2)
  app (C d)  (N e)  = N (C (cB `capp` d) `app` e)
  app (N e)  (C d)  = N (C (cC `capp` cC `capp` d) `app` e)
  app (N e)    V    = N (C cS `app` e `app` C cI)
  app   V    (N e)  = N (C (cS `capp` cI) `app` e)
  app (C d1) (C d2) = C (d1 `capp` d2)
  app (C d)    V    = N (C d)
  app   V    (C d)  = N (C (cC `capp` cI `capp` d))
  
  lam (C d) = C (cK `capp` d)
  lam V = C cI
  lam (N e) = e
  lam (W e) = C cK `app` e
  
observe :: (SKIC r) => Conv r () a -> r a
observe (C d) = d

toSKI :: (SKIC r) => Conv r () a -> r a
toSKI = observe

instance SKIC Identity where
  cI = Identity id
  cK = Identity const
  cS = Identity (<*>)
  capp (Identity ab) (Identity a) = Identity (ab a)

instance SKIC (Const String) where
  cI = Const "I"
  cK = Const "K"
  cS = Const "S"
  capp (Const ab) (Const a) = Const ("(" ++ ab ++ " " ++ a ++ ")")

runSKI :: Identity a -> a
runSKI = runIdentity

printSKI :: Const String a -> String
printSKI = getConst

example :: (SKIC r) => r (a -> (a -> b) -> b)
example = toSKI $ hlam (\x -> hlam (\f -> f # x))