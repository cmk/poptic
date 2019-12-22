{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Optic.Cotraversal (
    -- * Cotraversal & Cxtraversal
    Cotraversal
  , Cotraversal'
  , cotraversing
  , retraversing
  , cotraversalVl
    -- * List & List1
  , list
  , list1
    -- * Optics
  , cotraversed
  , scoped
  , scoped1
  , pointwise
  , padded
  , partitioned
    -- * Operators
  , (/~)
  , (//~)
  , withCotraversal
  , distributes 
) where

import Data.Bitraversable
import Data.List.NonEmpty as NonEmpty
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Grate
import Data.Profunctor.Optic.Lens
import Data.Profunctor.Optic.Import hiding (id,(.))
import Data.Profunctor.Optic.Types
import Data.Profunctor.Optic.Operator
import Data.Semigroupoid
import Data.Semiring
import Control.Monad.Trans.State
import Prelude (Foldable(..), reverse)
import qualified Data.Functor.Rep as F

import Control.Applicative
import Data.Ord
import Data.Function
import Prelude
import Data.Semigroup.Foldable as F1
import Data.Foldable as F
import Data.List as L
import Data.List.NonEmpty as L1

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XFlexibleContexts
-- >>> :set -XTypeApplications
-- >>> :set -XTupleSections
-- >>> :set -XRankNTypes
-- >>> import Data.Maybe
-- >>> import Data.Int.Instance ()
-- >>> import Data.List.NonEmpty (NonEmpty(..))
-- >>> import qualified Data.List.NonEmpty as NE
-- >>> import Data.Functor.Identity
-- >>> import Data.Foldable
-- >>> import Data.List.Index
-- >>> import Data.List as L
-- >>> import Data.Ord
-- >>> :load Data.Profunctor.Optic
-- >>> data Species = Setosa | Versicolor | Virginica deriving (Eq, Show)
-- >>> type Features = [Float]
-- >>> data Flower = Flower { flowerSpecies :: Species, flowerFeatures :: Features} deriving (Eq, Show)
-- >>> euclidean :: Features -> Features -> Float ; euclidean xs ys = sqrt . sum $ L.zipWith diff xs ys where diff a b = (a - b) ** 2
-- >>> classify :: Foldable f => f Flower -> Features -> Flower ; classify dset feats = flip Flower feats $ flowerSpecies $ minimumBy (comparing (euclidean feats . flowerFeatures)) dset
-- >>> let features :: List' Flower Features ; features = list flowerFeatures classify
-- >>> let flower1 = Flower Versicolor [2, 3, 4, 2]
-- >>> let flower2 = Flower Setosa [5, 4, 3, 2.5]
-- >>> let dataset :: NonEmpty Flower ; dataset = flower1 :| [flower2]

---------------------------------------------------------------------
-- 'Cotraversal'
---------------------------------------------------------------------

-- | Obtain a 'Cotraversal' by embedding a continuation into a 'Distributive' functor. 
--
-- @
--  'withGrate' o 'cotraversing' ≡ 'cotraversed' . o
-- @
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input function satisfies the following
-- properties:
--
-- * @sabt ($ s) ≡ s@
--
-- * @sabt (\k -> f (k . sabt)) ≡ sabt (\k -> f ($ k))@
--
cotraversing :: Distributive g => (((s -> a) -> b) -> t) -> Cotraversal (g s) (g t) a b
cotraversing sabt = corepn cotraverse . grate sabt

-- | Obtain a 'Cotraversal' by embedding a reversed lens getter and setter into a 'Distributive' functor.
--
-- @
--  'withLens' ('re' o) 'cotraversing' ≡ 'cotraversed' . o
-- @
--
retraversing :: Distributive g => (b -> t) -> (b -> s -> a) -> Cotraversal (g s) (g t) a b
retraversing bsa bt = corepn cotraverse . (re $ lens bsa bt)

-- | Obtain a profunctor 'Cotraversal' from a Van Laarhoven 'Cotraversal'.
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input satisfies the following properties:
--
-- * @abst runIdentity ≡ runIdentity@
--
-- * @abst f . fmap (abst g) ≡ abst (f . fmap g . getCompose) . Compose@
--
-- See 'Data.Profunctor.Optic.Property'.
--
cotraversalVl :: (forall f. Coapplicative f => (f a -> b) -> f s -> t) -> Cotraversal s t a b
cotraversalVl abst = cotabulate . abst . cosieve 

---------------------------------------------------------------------
-- 'List' & 'List1'
---------------------------------------------------------------------

-- | Obtain a 'List' directly.
--
-- >>> flower1 & features . fmapped ..~ negate
-- Flower {flowerSpecies = Versicolor, flowerFeatures = [-2.0,-3.0,-4.0,-2.0]}
--
-- >>> dataset & features . pointwise //~ maximum
-- Flower {flowerSpecies = Setosa, flowerFeatures = [5.0,4.0,4.0,2.5]}
-- 
-- >>> dataset & features /~ [1.9, 3.2, 3.8, 2]
-- Flower {flowerSpecies = Versicolor, flowerFeatures = [1.9,3.2,3.8,2.0]}
-- 
list :: (s -> a) -> ([s] -> b -> t) -> List s t a b
list sa sbt p = cotabulate $ \s -> sbt (F.toList s) (cosieve p . fmap sa $ s)
{-# INLINE list #-}

-- | Obtain a 'List1' directly.
--
list1 :: (s -> a) -> (NonEmpty s -> b -> t) -> List1 s t a b
list1 sa sbt p = cotabulate $ \s -> sbt (F1.toNonEmpty s) (cosieve p . fmap sa $ s)
{-# INLINE list1 #-}

---------------------------------------------------------------------
-- Optics
---------------------------------------------------------------------

-- | TODO: Document
--
cotraversed :: Distributive f => Cotraversal (f a) (f b) a b 
cotraversed = cotraversalVl cotraverse
{-# INLINE cotraversed #-}

-- | TODO: Document
--
scoped :: Applicative f => Scope (f a) (f b) a b
scoped p = cotabulate $ fmap (cosieve p) . sequenceA
{-# INLINE scoped #-}

-- | TODO: Document
--
scoped1 :: Apply f => Scope1 (f a) (f b) a b
scoped1 p = cotabulate $ fmap (cosieve p) . sequence1
{-# INLINE scoped1 #-}

-- | Variant of 'fmapped' that works over arbitrary Scopes.
--
-- Useful because lists are not 'Coapplicative'.
--
pointwise :: Scope [a] [b] a b
pointwise = dimap ZipList getZipList . scoped
{-# INLINE pointwise #-}

-- | TODO: Document
--
-- >>> ["foo", "foobar"] & padded 'x' /~ 8
-- ["fooxxxxx","foobarxx"]
--
-- >>> ["foo", "foobar"] & padded 'x' /~ 4
-- ["foox","foob"]
--
-- >>> ["foo", "foobar"] & padded 'x' //~ maximum
-- ["fooxxx","foobar"]
--
padded :: a -> List [a] [[a]] Int Int
padded x = list L.length $ \xs n -> fmap (\s -> L.take n $ s <> L.repeat x) xs
{-# INLINE padded #-}

-- | TODO: Document
--
partitioned :: (a -> a -> Bool) -> List a ([a],[a]) a a
partitioned f = list id $ \xs ref -> (L.filter (\x -> False == f ref x) (F.toList xs), L.filter (\x -> True == f ref x) (F.toList xs))
{-# INLINE partitioned #-}

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- |
--
-- @
-- 'withCotraversal' $ 'Data.Profuncto.Optic.Grate.grate' (flip 'Data.Distributive.cotraverse' id) ≡ 'Data.Distributive.cotraverse'
-- @
--
-- The cotraversal laws can be restated in terms of 'withCotraversal':
--
-- * @withCotraversal o (f . runIdentity) ≡  fmap f . runIdentity@
--
-- * @withCotraversal o f . fmap (withCotraversal o g) == withCotraversal o (f . fmap g . getCompose) . Compose@
--
-- See also < https://www.cs.ox.ac.uk/jeremy.gibbons/publications/iterator.pdf >
--
withCotraversal :: Coapplicative f => ACotraversal f s t a b -> (f a -> b) -> (f s -> t)
withCotraversal = withCostar
{-# INLINE withCotraversal #-}

-- | TODO: Document
--
-- >>> distributes left' (1, Left "foo")
-- Left (1,"foo")
--
-- >>> distributes left' (1, Right "foo")
-- Right "foo"
--
distributes :: Coapplicative f => ACotraversal f s t a (f a) -> f s -> t
distributes o = withCotraversal o id
{-# INLINE distributes #-}
