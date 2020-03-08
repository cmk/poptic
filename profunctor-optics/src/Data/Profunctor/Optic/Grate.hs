{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Optic.Grate  (
    -- * Grate & Cxgrate
    Grate
  , Grate'
  , grate
  , grateVl
  , inverting
  , cloneGrate
    -- * Optics
  , represented
  , distributed
  , endomorphed
  , continued
  , continuedT
  , calledCC
    -- * Primitive operators
  , withGrate 
  , withGrateVl
    -- * Operators
  , zipsWith0
  , zipsWith2
  , zipsWith3
  , zipsWith4 
  , toClosure
  , toEnvironment
    -- * Classes
  , Closed(..)
  , Costrong(..)
) where

import Control.Monad.Reader
import Control.Monad.Cont
import Data.Distributive
import Data.Monoid (Endo(..))
import Data.Profunctor.Closed
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Types
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Iso (tabulated)

import qualified Data.Functor.Rep as F

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> :set -XTupleSections
-- >>> import Control.Monad.Reader
-- >>> import Data.Complex
-- >>> import Data.Connection.Int
-- >>> import Data.List as L
-- >>> import Data.Monoid (Endo(..))
-- >>> :load Data.Profunctor.Optic

---------------------------------------------------------------------
-- 'Grate'
---------------------------------------------------------------------

-- | Obtain a 'Grate' from a nested continuation.
--
-- The resulting optic is the corepresentable counterpart to 'Lens', 
-- and sits between 'Iso' and 'Setter'.
--
-- A 'Grate' lets you lift a profunctor through any representable 
-- functor (aka Naperian container). In the special case where the 
-- indexing type is finitary (e.g. 'Bool') then the tabulated type is 
-- isomorphic to a fied length vector (e.g. 'V2 a').
--
-- The identity container is representable, and representable functors 
-- are closed under composition.
--
-- See <https://www.cs.ox.ac.uk/jeremy.gibbons/publications/proyo.pdf>
-- section 4.6 for more background on 'Grate's, and compare to the 
-- /lens-family/ <http://hackage.haskell.org/package/lens-family-2.0.0/docs/Lens-Family2.html#t:Grate version>.
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input function satisfies the following
-- properties:
--
-- * @sabt ($ s) ≡ s@
--
-- * @sabt (\k -> f (k . sabt)) ≡ sabt (\k -> f ($ k))@
--
-- More generally, a profunctor optic must be monoidal as a natural 
-- transformation:
-- 
-- * @o id ≡ id@
--
-- * @o ('Data.Profunctor.Composition.Procompose' p q) ≡ 'Data.Profunctor.Composition.Procompose' (o p) (o q)@
--
-- See 'Data.Profunctor.Optic.Property'.
--
grate :: (((s -> a) -> b) -> t) -> Grate s t a b
grate sabt = dimap (flip ($)) sabt . closed

-- | Transform a Van Laarhoven grate into a profunctor grate.
--
-- Compare 'Data.Profunctor.Optic.Lens.lensVl' & 'Data.Profunctor.Optic.Traversal.cotraversalVl'.
--
-- /Caution/: In order for the generated family to be well-defined,
-- you must ensure that the traversal1 law holds for the input function:
--
-- * @abst runIdentity ≡ runIdentity@
--
-- * @abst f . fmap (abst g) ≡ abst (f . fmap g . getCompose) . Compose@
--
-- See 'Data.Profunctor.Optic.Property'.
--
grateVl :: (forall f. Functor f => (f a -> b) -> f s -> t) -> Grate s t a b 
grateVl o = dimap (curry eval) ((o trivial) . Coindex) . closed

-- | Construct a 'Grate' from a pair of inverses.
--
inverting :: (s -> a) -> (b -> t) -> Grate s t a b
inverting sa bt = grate $ \sab -> bt (sab sa)

-- | TODO: Document
--
cloneGrate :: AGrate s t a b -> Grate s t a b
cloneGrate k = withGrate k grate

---------------------------------------------------------------------
-- Optics 
---------------------------------------------------------------------

-- | Obtain a 'Grate' from a 'F.Representable' functor.
--
represented :: F.Representable f => Grate (f a) (f b) a b
represented = tabulated . closed
{-# INLINE represented #-}

-- | Obtain a 'Grate' from a distributive functor.
--
distributed :: Distributive f => Grate (f a) (f b) a b
distributed = grate (`cotraverse` id)
{-# INLINE distributed #-}

-- | Obtain a 'Grate' from an endomorphism. 
--
-- >>> flip appEndo 2 $ zipsWith2 endomorphed (+) (Endo (*3)) (Endo (*4))
-- 14
--
endomorphed :: Grate' (Endo a) a
endomorphed = dimap appEndo Endo . closed
{-# INLINE endomorphed #-}

-- | Obtain a 'Grate' from a continuation.
--
-- @
-- 'zipsWith2' 'continued' :: (r -> r -> r) -> s -> s -> 'Cont' r s
-- @
--
continued :: Grate a (Cont r a) r r
continued = grate cont
{-# INLINE continued #-}

-- | Obtain a 'Grate' from a continuation.
--
-- @
-- 'zipsWith2' 'continued' :: (m r -> m r -> m r) -> s -> s -> 'ContT' r m s 
-- @
--
continuedT :: Grate a (ContT r m a) (m r) (m r)
continuedT = grate ContT
{-# INLINE continuedT #-}

-- | Lift the current continuation into the calling context.
--
-- @
-- 'zipsWith2' 'calledCC' :: 'MonadCont' m => (m b -> m b -> m s) -> s -> s -> m s
-- @
--
calledCC :: MonadCont m => Grate a (m a) (m b) (m a)
calledCC = grate callCC
{-# INLINE calledCC #-}

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

-- | Extract the higher order function that characterizes a 'Grate'.
--
-- The grate laws can be stated in terms or 'withGrate':
-- 
-- Identity:
-- 
-- @
-- withGrateVl o runIdentity ≡ runIdentity
-- @
-- 
-- Composition:
-- 
-- @ 
-- withGrateVl o f . fmap (withGrateVl o g) ≡ withGrateVl o (f . fmap g . getCompose) . Compose
-- @
--
withGrateVl :: Functor f => AGrate s t a b -> (f a -> b) -> f s -> t
withGrateVl o ab s = withGrate o $ \sabt -> sabt $ \get -> ab (fmap get s)
{-# INLINE withGrateVl #-}

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- | Set all fields to the given value.
--
-- This is essentially a restricted variant of 'Data.Profunctor.Optic.View.review'.
--
zipsWith0 :: AGrate s t a b -> b -> t
zipsWith0 o b = withGrate o $ \sabt -> sabt (const b)
{-# INLINE zipsWith0 #-}

-- | Zip over a 'Grate'. 
--
-- @\\f -> 'zipsWith2' 'closed' ('zipsWith2' 'closed' f) ≡ 'zipsWith2' ('closed' . 'closed')@
--
zipsWith2 :: AGrate s t a b -> (a -> a -> b) -> s -> s -> t
zipsWith2 o aab s1 s2 = withGrate o $ \sabt -> sabt $ \get -> aab (get s1) (get s2)
{-# INLINE zipsWith2 #-}

-- | Zip over a 'Grate' with 3 arguments.
--
zipsWith3 :: AGrate s t a b -> (a -> a -> a -> b) -> (s -> s -> s -> t)
zipsWith3 o aaab s1 s2 s3 = withGrate o $ \sabt -> sabt $ \sa -> aaab (sa s1) (sa s2) (sa s3)
{-# INLINE zipsWith3 #-}

-- | Zip over a 'Grate' with 4 arguments.
--
zipsWith4 :: AGrate s t a b -> (a -> a -> a -> a -> b) -> (s -> s -> s -> s -> t)
zipsWith4 o aaaab s1 s2 s3 s4 = withGrate o $ \sabt -> sabt $ \sa -> aaaab (sa s1) (sa s2) (sa s3) (sa s4)
{-# INLINE zipsWith4 #-}

-- | Use a 'Grate' to construct a 'Closure'.
--
toClosure :: Closed p => AGrate s t a b -> p a b -> Closure p s t
toClosure o p = withGrate o $ \sabt -> Closure (closed . grate sabt $ p)
{-# INLINE toClosure #-}

-- | Use a 'Grate' to construct an 'Environment'.
--
toEnvironment :: Closed p => AGrate s t a b -> p a b -> Environment p s t
toEnvironment o p = withGrate o $ \sabt -> Environment sabt p (curry eval)
{-# INLINE toEnvironment #-}
