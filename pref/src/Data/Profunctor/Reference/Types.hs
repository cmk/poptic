{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ExistentialQuantification     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-# LANGUAGE RankNTypes #-}


{-# LANGUAGE ScopedTypeVariables, TypeOperators , KindSignatures, GADTs, DataKinds #-}

--for tupled constraints
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}


{-# LANGUAGE TypeApplications #-}

{-# LANGUAGE TemplateHaskell #-}
-- {-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ConstraintKinds, StandaloneDeriving, DeriveAnyClass #-}
-- {-# LANGUAGE PolyKinds #-}
-- {-# LANGUAGE ImpredicativeTypes #-}



 {-# OPTIONS_GHC -w #-}
-- | Environment values with stateful capabilities.
module Data.Profunctor.Reference.Types where


import Data.Kind (Constraint, Type)
import Data.Monoid (First)

import Data.Profunctor.Optic
import Control.Concurrent.STM (STM)
import Control.Applicative (Const(..))
import Data.Tuple (swap)
import Data.Bitraversable


import Data.Function ((&)) 
import Data.Void
import Data.IORef



type X = Void

---------------------------------------------------------------------
--  PRef
---------------------------------------------------------------------


{- | A profunctor reference is a pair of mutable references bound 

together with a profunctor optic by existentializing over the read and

write reference types.

The type variables signify:

  * @r@ - The reference type (e.g. 'TVar', 'MVar', 'STRef', 'IORef' etc.)

  * @c@ - The constraint determining which operations can be performed.

  * @b@ - The contravariant write-only type.

  * @a@ - The covariant read-only type.


data Proxy a' a b' b m r Source#

A Proxy is a monad transformer that receives and sends information on both an upstream and downstream interface.

The type variables signify:

a' and a - The upstream interface, where (a')s go out and (a)s come in
b' and b - The downstream interface, where (b)s go out and (b')s come in
m - The base monad
r - The return value

-}

data P rt rs c b a = forall s t. P (Optical c s t a b) !(rt t) !(rs s)


data Pxy t s c b a = forall x y . Pxy (Optical c x y a b) !(s x) !(t y)

data Pxx t s c b a = forall x . Pxx (Optical c x x a b) !(s x) !(t x)

data Px s c a = forall x . Px (Optical c x x a a) !(s x)


--data P'' rs c a = forall s. P'' (Optical c s s a a) !(rs s) !(rs s)

--data P''' rt rs c a = forall s t. P''' (Optical c s t a b) !(rt t) !(rs s) !(rs s)

{-
type Pxy = Pxy IORef IORef
type PVar = Pxy MVar MVar
type PChan = Pxy Chan
type PStream = Pxy InputStream OutputStream
-}

{-
-- experiment w/ removingOptical type
data QRef r c b a = forall s t. QRef (forall p. c p => Optic p s t a b) !(r t) !(r s)

withQRef 
  :: QRef r c b a 
  -> (forall s t . (forall p. c p => Optic p s t a b) -> r t -> r s -> x) 
  -> x
withQRef (QRef o rt rs) f = f o rt rs

data Pxy rs rt c b a where 

  --Pxy :: (Optic c s t a b) -> r t -> r s -> Pxy rs rt c b a
  Pxy :: forall a b c r s t. (forall p. c p => Optic p s t a b) -> r t -> r s -> Pxy rs rt c b a
-}

instance Profunctor (Pxy rs rt Profunctor) where  dimap bt sa (Pxy o rs rt) = Pxy (o . dimap sa bt) rs rt
instance Profunctor (Pxy rs rt Strong) where dimap bt sa (Pxy o rs rt) = Pxy (o . dimap sa bt) rs rt
instance Profunctor (Pxy rs rt Costrong) where dimap bt sa (Pxy o rs rt) = Pxy (o . dimap sa bt) rs rt
instance Profunctor (Pxy rs rt Choice) where dimap bt sa (Pxy o rs rt) = Pxy (o . dimap sa bt) rs rt
instance Profunctor (Pxy rs rt Cochoice) where dimap bt sa (Pxy o rs rt) = Pxy (o . dimap sa bt) rs rt
instance Profunctor (Pxy rs rt Traversing) where dimap bt sa (Pxy o rs rt) = Pxy (o . dimap sa bt) rs rt
instance Profunctor (Pxy rs rt Mapping) where dimap bt sa (Pxy o rs rt) = Pxy (o . dimap sa bt) rs rt
instance Profunctor (Pxy rs rt Closed) where dimap bt sa (Pxy o rs rt) = Pxy (o . dimap sa bt) rs rt

instance Profunctor (Pxy rs rt AffineFolding) where dimap bt sa (Pxy o rs rt) = Pxy (o . dimap sa bt) rs rt
instance Profunctor (Pxy rs rt Folding) where dimap bt sa (Pxy o rs rt) = Pxy (o . dimap sa bt) rs rt
instance Profunctor (Pxy rs rt Getting) where dimap bt sa (Pxy o rs rt) = Pxy (o . dimap sa bt) rs rt
instance Profunctor (Pxy rs rt Reviewing) where dimap bt sa (Pxy o rs rt) = Pxy (o . dimap sa bt) rs rt
instance Profunctor (Pxy rs rt AffineTraversing) where dimap bt sa (Pxy o rs rt) = Pxy (o . dimap sa bt) rs rt


instance Strong (Pxy rs rt Costrong) where first' (Pxy o rs rt) = Pxy (o . unfirst) rs rt
instance Costrong (Pxy rs rt Strong) where unfirst (Pxy o rs rt) = Pxy (o . first') rs rt

instance Choice (Pxy rs rt Cochoice) where right' (Pxy o rs rt) = Pxy (o . unright) rs rt
instance Cochoice (Pxy rs rt Choice) where unright (Pxy o rs rt) = Pxy (o . right') rs rt


-------------------------------------------------------------------------------
--  PRef'
-------------------------------------------------------------------------------


-- Note that Pxy rs rt c a a is distinct from PRef' r c a in that it has
-- a read-only Ref and a write-only Ref of the same type, rather than one Ref for both reading and writing.
-- Because the Refs are existentialized this makes certain opimitations (e.g 'atomicModifyRef') 
-- unavaliable to a Pxy rs rt c a a.
--
-- Note that for TVars 'atomicModifyRef' is equiv / makes no difference
--data PRef' r c a = forall s. PRef' (Optic' c s a) !(r s) 

--instance Functor (PRef' r c)

primGetter :: Bicontravariant p => (s -> a) -> Optic' p s a
primGetter sa = primgetting sa sa

{-
newtype LocalRef c s a = 
  LocalRef { unLocalRef :: Ref m r => forall r. ReaderT (PRef' STRef c s) (ST r) a }

modifyPRef' :: Ref r m => PRef' r Mapping a -> (a -> a) -> m ()
modifyPRef' (PRef' o rs) f = modifyRef' rs $ over o f

atomicModifyPRef' :: ARef r m => PRef' r Strong a -> (a -> (a, x)) -> m x
atomicModifyPRef' (PRef' o rs) f = atomicModifyRef' rs ssa
    where ssa = withLens o $ \sa sas -> \s -> let (a, x) = f . sa $! s in (sas s a, x)

-}








{-

-- | Unbox a 'PRef' by providing an existential continuation.
withPxy 
  :: Pxy rs rt c b a 
  -> (forall s t. Optical c s t a b -> rt t -> rs s -> x) 
  -> x
withPxy (Pxy o rs rt) f = f o rt rs

-- Affine PRef
--
aff :: Affine (Either c a, d) (Either c b, d) a b
aff = first' . right'

s = (Just "hi!", 2) :: (Maybe String, Int)
t = (Nothing, 2) :: (Maybe Int, Int)

rs <- newRef @IORef @IO s
rt <- newRef @IORef @IO t

o :: Pxy IORef AffineLike Int String = Pxy (_1 . _Just) rs rt
o' :: Pxy IORef AffineLike String String = Pxy (_1 . _Just) rs rs


modifyPxy o' tail >> readRef rs >>= print >> readRef rt >>= print
-- (Just "i!",2)
-- (Nothing,2)

modifyPxy o length >> readRef rs >>= print >> readRef rt >>= print
--(Just "i!",2)
--(Just 2,2)


-- Affine Pxy 2
--

s = (Nothing, 2) :: (Maybe String, Int)
t = (Just 4, 2) :: (Maybe Int, Int)

rs <- newRef @IORef @IO s
rt <- newRef @IORef @IO t

o :: Pxy IORef AffineLike Int String = Pxy (_1 . _Just) rs rt
o' :: Pxy IORef AffineLike String String = Pxy (_1 . _Just) rs rs


modifyPxy o' tail >> readRef rs >>= print >> readRef rt >>= print
-- (Nothing,2)
-- (Just 4,2)

modifyPxy o length >> readRef rs >>= print >> readRef rt >>= print
-- (Nothing,2)
-- (Nothing,2)


-}







