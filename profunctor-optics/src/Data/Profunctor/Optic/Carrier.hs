{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE DeriveGeneric         #-}
module Data.Profunctor.Optic.Carrier (
    -- * Iso carrier
    AIso
  , AIso'
    -- * Prism carriers
  , APrism
  , APrism'
    -- * Lens carriers
  , ALens
  , AColens
  , AIxlens
  , ACxlens
  , ALens'
  , AColens'
  , AIxlens'
  , ACxlens'
    -- * Traversal carriers
  , ATraversal0
  , ACotraversal0
  , ATraversal
  , ACotraversal
  , AIxtraversal0
  , AIxtraversal
  , ACxtraversal
  , ATraversal0'
  , ACotraversal0'
  , ATraversal'
  , ACotraversal'
  , AIxtraversal0'
  , AIxtraversal'
  , ACxtraversal'
    -- * Fold carriers
  , AFold0
  , AFold
  , ACofold
  , AIxfold0
  , AIxfold
  , ACxfold
    -- * Machine carriers
  , AFoldl
  , AFoldl1
  , ACxfoldl
  , ACxfoldl1
  , AFoldl'
  , AFoldl1'
  , ACxfoldl'
  , ACxfoldl1'
    -- * Setter carriers
  , ASetter
  , AResetter
  , AIxsetter
  , ARxsetter
  , ASetter'
  , AResetter'
  , AIxsetter'
  , ARxsetter'
    -- * View carriers
  , AView
  , AReview
  , AIxview
  , ARxview
    -- * Carrier operators
  , withIso
  , withPrism
  , withLens
  , withIxlens
  , withColens
  , withCxlens
  , withAffine
  , withAffine'
  , withCoaffine
    -- * Carrier profunctors
  , IsoRep(..)
  , PrismRep(..)
  , LensRep(..)
  , IxlensRep(..)
  , ColensRep(..)
  , CxlensRep(..)
  , AffineRep(..)
  , CoaffineRep(..)
  , Star(..)
  , Costar(..)
  , Tagged(..)
    -- * Paired
  , Paired(..)
  , paired
  , fromTambara
    -- * Split
  , Split(..)
  , split
  , fromTambaraSum
    -- * Index
  , Index(..)
  , vals
  , info
    -- * Coindex
  , Coindex(..)
  , trivial
  , noindex
  , coindex
  , (<<<<)
    -- * Conjoin
  , Conjoin(..)
) where

import Control.Category (Category)
import Control.Monad.Fix (MonadFix(..))
import Data.Profunctor.Types as Export (Star(..), Costar(..))
import Data.Bifunctor as B
import Data.Function
import Data.Monoid(Alt(..))
import Data.Profunctor.Choice
import Data.Profunctor.Strong
import Data.Profunctor.Optic.Types
import Data.Profunctor.Optic.Import
import Data.Profunctor.Rep (unfirstCorep)
import GHC.Generics (Generic)
import qualified Control.Arrow as A
import qualified Control.Category as C
import qualified Data.Profunctor.Rep.Foldl as L
import qualified Data.Profunctor.Rep.Foldl1 as L1

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> :set -XRankNTypes
-- >>> import Data.Functor.Identity
-- >>> import Data.Map as Map
-- >>> import Data.Maybe
-- >>> import Data.Monoid
-- >>> :load Data.Profunctor.Optic

---------------------------------------------------------------------
-- Iso carriers
---------------------------------------------------------------------

type AIso s t a b = Optic (IsoRep a b) s t a b

type AIso' s a = AIso s s a a

---------------------------------------------------------------------
-- Prism carriers
---------------------------------------------------------------------

type APrism s t a b = Optic (PrismRep a b) s t a b

type APrism' s a = APrism s s a a

---------------------------------------------------------------------
-- Lens carriers
---------------------------------------------------------------------

type ALens s t a b = Optic (LensRep a b) s t a b

type AColens s t a b = Optic (ColensRep a b) s t a b

type AIxlens k s t a b = Ixoptic (IxlensRep k a b) k s t a b

type ACxlens k s t a b = Cxoptic (CxlensRep k a b) k s t a b

type ALens' s a = ALens s s a a

type AColens' s a = AColens s s a a

type AIxlens' k s a = AIxlens k s s a a

type ACxlens' k s a = ACxlens k s s a a

---------------------------------------------------------------------
-- Traversal carriers
---------------------------------------------------------------------

type ATraversal0 s t a b = Optic (AffineRep a b) s t a b

type ACotraversal0 s t a b = Optic (CoaffineRep a b) s t a b

type ATraversal f s t a b = Optic (Star f) s t a b

type ACotraversal f s t a b = Optic (Costar f) s t a b

type AIxtraversal0 k s t a b = Ixoptic (AffineRep a b) k s t a b

type AIxtraversal f k s t a b = Ixoptic (Star f) k s t a b

type ACxtraversal f k s t a b = Cxoptic (Costar f) k s t a b 

type ATraversal0' s a = ATraversal0 s s a a

type ACotraversal0' s a = ACotraversal0 s s a a

type ATraversal' f s a = ATraversal f s s a a

type ACotraversal' f s a = ACotraversal f s s a a

type AIxtraversal0' k s a = AIxtraversal0 k s s a a

type AIxtraversal' f k s a = AIxtraversal f k s s a a

type ACxtraversal' f k t b = ACxtraversal f k t t b b

---------------------------------------------------------------------
-- Fold carriers
---------------------------------------------------------------------

type AFold0 r s a = AFold ((Alt Maybe r)) s a

type AFold r s a = ATraversal' (Const r) s a

type ACofold r t b = ACotraversal' (Const r) t b

type AIxfold0 r k s a = AIxfold (Alt Maybe r) k s a

type AIxfold r k s a = AIxtraversal' (Const r) k s a

type ACxfold r k t b = ACxtraversal' (Const r) k t b

---------------------------------------------------------------------
-- Machine carriers
---------------------------------------------------------------------

type AFoldl s t a b = Optic L.Foldl s t a b

type AFoldl1 s t a b = Optic L1.Foldl1 s t a b

type ACxfoldl k s t a b = Cxoptic L.Foldl k s t a b

type ACxfoldl1 k s t a b = Cxoptic L1.Foldl1 k s t a b

type AFoldl' t b = AFoldl t t b b

type AFoldl1' t b = AFoldl1 t t b b

type ACxfoldl' k t b = ACxfoldl k t t b b

type ACxfoldl1' k t b = ACxfoldl1 k t t b b 

---------------------------------------------------------------------
-- Setter carriers
---------------------------------------------------------------------

type ASetter s t a b = ATraversal Identity s t a b

type AResetter s t a b = ACotraversal Identity s t a b

type AIxsetter k s t a b = AIxtraversal Identity k s t a b

type ARxsetter k s t a b = ACxtraversal Identity k s t a b

type ASetter' s a = ASetter s s a a

type AResetter' s a = AResetter s s a a

type AIxsetter' k s a = AIxsetter k s s a a

type ARxsetter' k t b = ARxsetter k t t b b

---------------------------------------------------------------------
-- View carriers
---------------------------------------------------------------------

type AView r s a = AFold r s a

type AReview t b = Optic' Tagged t b

type AIxview k s a = AIxfold (Maybe k, a) k s a

type ARxview k t b = Cxoptic' Tagged k t b

---------------------------------------------------------------------
-- Carrier operators
---------------------------------------------------------------------

-- | Extract the two functions that characterize an 'Iso'.
--
withIso :: AIso s t a b -> ((s -> a) -> (b -> t) -> r) -> r
withIso x k = case x (IsoRep id id) of IsoRep sa bt -> k sa bt
{-# INLINE withIso #-}

-- | Extract the two functions that characterize a 'Prism'.
--
withPrism :: APrism s t a b -> ((s -> t + a) -> (b -> t) -> r) -> r
withPrism o f = case o (PrismRep Right id) of PrismRep g h -> f g h
{-# INLINE withPrism #-}

-- | Extract the two functions that characterize a 'Lens'.
--
withLens :: ALens s t a b -> ((s -> a) -> (s -> b -> t) -> r) -> r
withLens o f = case o (LensRep id (flip const)) of LensRep x y -> f x y
{-# INLINE withLens #-}

-- | Extract the two functions that characterize a 'Ixlens'.
--
-- @since 0.0.3
withIxlens :: Monoid k => AIxlens k s t a b -> ((s -> (k , a)) -> (s -> b -> t) -> r) -> r
withIxlens o f = case o (IxlensRep id $ flip const) of IxlensRep x y -> f (x . (mempty,)) (\s b -> y (mempty, s) b)
{-# INLINE withIxlens #-}

-- | Extract the function that characterizes a 'Colens'.
--
withColens :: AColens s t a b -> ((((s -> a) -> b) -> t) -> r) -> r
withColens o f = case o (ColensRep $ \k -> k id) of ColensRep sabt -> f sabt
{-# INLINE withColens #-}

-- | TODO: Document
--
-- @since 0.0.3
withCxlens :: Monoid k => ACxlens k s t a b -> ((((s -> a) -> k -> b) -> t) -> r) -> r
withCxlens o f = case o (CxlensRep ($ id)) of CxlensRep saibt -> f $ flip saibt mempty
{-# INLINE withCxlens #-}

-- | TODO: Document
--
withAffine :: ATraversal0 s t a b -> ((s -> t + a) -> (s -> b -> t) -> r) -> r
withAffine o k = case o (AffineRep Right $ const id) of AffineRep x y -> k x y
{-# INLINE withAffine #-}

-- | TODO: Document
--
-- @since 0.0.3
withAffine' :: ATraversal0 s s a b -> ((s -> Maybe a) -> (s -> b -> s) -> r) -> r
withAffine' o k = case o (AffineRep Right $ const id) of AffineRep x y -> k (either (const Nothing) Just . x) y
{-# INLINE withAffine' #-}

-- | TODO: Document
--
withCoaffine :: ACotraversal0 s t a b -> ((((s -> t + a) -> b) -> t) -> r) -> r
withCoaffine o k = case o (CoaffineRep $ \f -> f Right) of CoaffineRep g -> k g
{-# INLINE withCoaffine #-}

---------------------------------------------------------------------
-- IsoRep
---------------------------------------------------------------------

-- | The 'IsoRep' profunctor precisely characterizes an 'Iso'.
data IsoRep a b s t = IsoRep (s -> a) (b -> t)

instance Profunctor (IsoRep a b) where
  dimap f g (IsoRep sa bt) = IsoRep (sa . f) (g . bt)
  {-# INLINE dimap #-}
  lmap f (IsoRep sa bt) = IsoRep (sa . f) bt
  {-# INLINE lmap #-}
  rmap f (IsoRep sa bt) = IsoRep sa (f . bt)
  {-# INLINE rmap #-}

instance Sieve (IsoRep a b) (Index a b) where
  sieve (IsoRep sa bt) s = Index (sa s) bt

instance Cosieve (IsoRep a b) (Coindex b a) where
  cosieve (IsoRep sa bt) (Coindex sab) = bt (sab sa)

---------------------------------------------------------------------
-- PrismRep
---------------------------------------------------------------------

-- | The 'PrismRep' profunctor precisely characterizes a 'Prism'.
--
data PrismRep a b s t = PrismRep (s -> t + a) (b -> t)

instance Profunctor (PrismRep a b) where
  dimap f g (PrismRep sta bt) = PrismRep (first g . sta . f) (g . bt)
  {-# INLINE dimap #-}

  lmap f (PrismRep sta bt) = PrismRep (sta . f) bt
  {-# INLINE lmap #-}

  rmap f (PrismRep sta bt) = PrismRep (first f . sta) (f . bt)
  {-# INLINE rmap #-}

instance Choice (PrismRep a b) where
  left' (PrismRep sta bt) = PrismRep (either (first Left . sta) (Left . Right)) (Left . bt)
  {-# INLINE left' #-}

  right' (PrismRep sta bt) = PrismRep (either (Left . Left) (first Right . sta)) (Right . bt)
  {-# INLINE right' #-}

---------------------------------------------------------------------
-- LensRep
---------------------------------------------------------------------

-- | The `LensRep` profunctor precisely characterizes a 'Lens'.
--
data LensRep a b s t = LensRep (s -> a) (s -> b -> t)

instance Profunctor (LensRep a b) where
  dimap f g (LensRep sa sbt) = LensRep (sa . f) (\s -> g . sbt (f s))

instance Strong (LensRep a b) where
  first' (LensRep sa sbt) =
    LensRep (\(a, _) -> sa a) (\(s, c) b -> (sbt s b, c))

  second' (LensRep sa sbt) =
    LensRep (\(_, a) -> sa a) (\(c, s) b -> (c, sbt s b))

instance Sieve (LensRep a b) (Index a b) where
  sieve (LensRep sa sbt) s = Index (sa s) (sbt s)

instance Representable (LensRep a b) where
  type Rep (LensRep a b) = Index a b

  tabulate f = LensRep (\s -> info (f s)) (\s -> vals (f s))


---------------------------------------------------------------------
-- IxlensRep
---------------------------------------------------------------------

data IxlensRep k a b s t = IxlensRep (s -> (k , a)) (s -> b -> t)

instance Profunctor (IxlensRep k a b) where
  dimap f g (IxlensRep sia sbt) = IxlensRep (sia . f) (\s -> g . sbt (f s))

instance Strong (IxlensRep k a b) where
  first' (IxlensRep sia sbt) =
    IxlensRep (\(a, _) -> sia a) (\(s, c) b -> (sbt s b, c))

  second' (IxlensRep sia sbt) =
    IxlensRep (\(_, a) -> sia a) (\(c, s) b -> (c, sbt s b))

---------------------------------------------------------------------
-- ColensRep
---------------------------------------------------------------------

-- | The 'ColensRep' profunctor precisely characterizes 'Colens'.
--
newtype ColensRep a b s t = ColensRep { unColensRep :: ((s -> a) -> b) -> t }

instance Profunctor (ColensRep a b) where
  dimap f g (ColensRep z) = ColensRep $ \d -> g (z $ \k -> d (k . f))

instance Closed (ColensRep a b) where
  closed (ColensRep sabt) = ColensRep $ \xsab x -> sabt $ \sa -> xsab $ \xs -> sa (xs x)

instance Costrong (ColensRep a b) where
  unfirst = unfirstCorep

instance Cosieve (ColensRep a b) (Coindex b a) where
  cosieve (ColensRep f) (Coindex g) = f g

instance Corepresentable (ColensRep a b) where
  type Corep (ColensRep a b) = Coindex b a

  cotabulate f = ColensRep $ f . Coindex

---------------------------------------------------------------------
-- CxlensRep
---------------------------------------------------------------------

-- @since 0.0.3
newtype CxlensRep k a b s t = CxlensRep { unCxlensRep :: ((s -> a) -> k -> b) -> t }

instance Profunctor (CxlensRep k a b) where
  dimap f g (CxlensRep z) = CxlensRep $ \d -> g (z $ \k -> d (k . f))

instance Closed (CxlensRep k a b) where
  closed (CxlensRep sabt) = CxlensRep $ \xsab x -> sabt $ \sa -> xsab $ \xs -> sa (xs x)

---------------------------------------------------------------------
-- AffineRep
---------------------------------------------------------------------

-- | The `AffineRep` profunctor precisely characterizes an 'Traversal0'.
data AffineRep a b s t = AffineRep (s -> t + a) (s -> b -> t)

instance Profunctor (AffineRep a b) where
  dimap f g (AffineRep sta sbt) = AffineRep
      (\a -> first g $ sta (f a))
      (\a v -> g (sbt (f a) v))

instance Strong (AffineRep a b) where
  first' (AffineRep sta sbt) = AffineRep
      (\(a, c) -> first (,c) $ sta a)
      (\(a, c) v -> (sbt a v, c))

instance Choice (AffineRep a b) where
  right' (AffineRep sta sbt) = AffineRep
      (\eca -> eassocl (second sta eca))
      (\eca v -> second (`sbt` v) eca)

instance Sieve (AffineRep a b) (Index0 a b) where
  sieve (AffineRep sta sbt) s = Index0 (sta s) (sbt s)

instance Representable (AffineRep a b) where
  type Rep (AffineRep a b) = Index0 a b

  tabulate f = AffineRep (info0 . f) (values0 . f)

data Index0 a b r = Index0 (r + a) (b -> r)

values0 :: Index0 a b r -> b -> r
values0 (Index0 _ br) = br

info0 :: Index0 a b r -> r + a
info0 (Index0 a _) = a

instance Functor (Index0 a b) where
  fmap f (Index0 ra br) = Index0 (first f ra) (f . br)

instance Applicative (Index0 a b) where
  pure r = Index0 (Left r) (const r)
  liftA2 f (Index0 ra1 br1) (Index0 ra2 br2) = Index0 (eswap $ liftA2 f (eswap ra1) (eswap ra2)) (liftA2 f br1 br2)

---------------------------------------------------------------------
-- CoaffineRep
---------------------------------------------------------------------

--TODO: Corepresentable, Coapplicative (Corep)

-- | The 'CoaffineRep' profunctor precisely characterizes 'Cotraversal0'.
--
newtype CoaffineRep a b s t = CoaffineRep { unCoaffineRep :: ((s -> t + a) -> b) -> t }

instance Profunctor (CoaffineRep a b) where
  dimap us tv (CoaffineRep stabt) =
    CoaffineRep $ \f -> tv (stabt $ \sta -> f (first tv . sta . us))

instance Closed (CoaffineRep a b) where
  closed (CoaffineRep stabt) =
    CoaffineRep $ \f x -> stabt $ \sta -> f $ \xs -> first const $ sta (xs x)

instance Choice (CoaffineRep a b) where
  left' (CoaffineRep stabt) =
    CoaffineRep $ \f -> Left $ stabt $ \sta -> f $ eassocl . fmap eswap . eassocr . first sta


---------------------------------------------------------------------
-- 'Paired'
---------------------------------------------------------------------

newtype Paired p c d a b = Paired { runPaired :: p (c , a) (d , b) }

fromTambara :: Profunctor p => Tambara p a b -> Paired p d d a b
fromTambara = Paired . dimap swap swap . runTambara

instance Profunctor p => Profunctor (Paired p c d) where
  dimap f g (Paired pab) = Paired $ dimap (fmap f) (fmap g) pab

instance Strong p => Strong (Paired p c d) where
  second' (Paired pab) = Paired . dimap shuffle shuffle . second' $ pab
   where
    shuffle (x,(y,z)) = (y,(x,z))

-- ^ @
-- paired :: Iso s t a b -> Iso s' t' a' b' -> Iso (s, s') (t, t') (a, a') (b, b')
-- paired :: Lens s t a b -> Lens s' t' a' b' -> Lens (s, s') (t, t') (a, a') (b, b')
-- @
--
paired 
  :: Profunctor p 
  => Optic (Paired p s2 t2) s1 t1 a1 b1 
  -> Optic (Paired p a1 b1) s2 t2 a2 b2 
  -> Optic p (s1 , s2) (t1 , t2) (a1 , a2) (b1 , b2)
paired x y = 
  dimap swap swap . runPaired . x . Paired . dimap swap swap . runPaired . y . Paired

---------------------------------------------------------------------
-- 'Split'
---------------------------------------------------------------------

newtype Split p c d a b = Split { runSplit :: p (Either c a) (Either d b) }

fromTambaraSum :: Profunctor p => TambaraSum p a b -> Split p d d a b
fromTambaraSum = Split . dimap eswap eswap . runTambaraSum

instance Profunctor p => Profunctor (Split p c d) where
  dimap f g (Split pab) = Split $ dimap (fmap f) (fmap g) pab

instance Choice p => Choice (Split p c d) where
  right' (Split pab) = Split . dimap shuffle shuffle . right' $ pab
   where
    shuffle = Right . Left ||| (Left ||| Right . Right)

-- ^ @
-- split :: Iso s t a b -> Iso s' t' a' b' -> Iso (Either s s') (Either t t') (Either a a') (Either b b')
-- split :: Prism s t a b -> Prism s' t' a' b' -> Lens (Either s s') (Either t t') (Either a a') (Either b b')
-- split :: View s t a b -> View s' t' a' b' -> Review (Either s s') (Either t t') (Either a a') (Either b b')
-- @
split 
  :: Profunctor p
  => Optic (Split p s2 t2) s1 t1 a1 b1 
  -> Optic (Split p a1 b1) s2 t2 a2 b2 
  -> Optic p (s1 + s2) (t1 + t2) (a1 + a2) (b1 + b2)
split x y = 
  dimap eswap eswap . runSplit . x . Split . dimap eswap eswap . runSplit . y . Split

---------------------------------------------------------------------
-- Index
---------------------------------------------------------------------

-- | An indexed store that characterizes a 'Data.Profunctor.Optic.Lens.Lens'
--
-- @'Index' a b s ≡ forall f. 'Functor' f => (a -> f b) -> f s@,
--
-- See also 'Data.Profunctor.Optic.Lens.cloneLensVl'.
--
data Index a b s = Index a (b -> s) deriving Generic

vals :: Index a b s -> b -> s
vals (Index _ bs) = bs
{-# INLINE vals #-}

info :: Index a b s -> a
info (Index a _) = a
{-# INLINE info #-}

instance Functor (Index a b) where
  fmap f (Index a bs) = Index a (f . bs)
  {-# INLINE fmap #-}

instance Profunctor (Index a) where
  dimap f g (Index a bs) = Index a (g . bs . f)
  {-# INLINE dimap #-}

instance a ~ b => Foldable (Index a b) where
  foldMap f (Index b bs) = f . bs $ b

--coapp f = either (Left . const) (Right . const) $ f b

instance a ~ b => Coapply (Index a b) where
  coapply (Index b bs) = bimap f g $ bs b
    where f = (Index b) . const
          g = (Index b) . const

instance a ~ b => Coapplicative (Index a b) where
  copure (Index b bs) = bs b

---------------------------------------------------------------------
-- Coindex
---------------------------------------------------------------------

-- | An indexed continuation that characterizes a 'Data.Profunctor.Optic.Lens.Colens'
--
-- @'Coindex' a b s ≡ forall f. 'Functor' f => (f a -> b) -> f s@,
--
-- See also 'Data.Profunctor.Optic.Lens.cloneColensVl'.
--
-- 'Coindex' can also be used to compose indexed maps, folds, or traversals directly.
--
-- For example, using the @containers@ library:
--
-- @
--  Coindex mapWithKey :: Coindex (a -> b) (Map k a -> Map k b) k
--  Coindex foldMapWithKey :: Monoid m => Coindex (a -> m) (Map k a -> m) k
--  Coindex traverseWithKey :: Applicative t => Coindex (a -> t b) (Map k a -> t (Map k b)) k
-- @
--
newtype Coindex a b s = Coindex { runCoindex :: (s -> b) -> a } deriving Generic

instance Functor (Coindex a b) where
  fmap sl (Coindex ab) = Coindex $ \la -> ab (la . sl)

instance a ~ b => Apply (Coindex a b) where
  (Coindex slab) <.> (Coindex ab) = Coindex $ \la -> slab $ \sl -> ab (la . sl) 

--TODO helpful to use grate ops w/ cotraverse1
--instance a ~ b => Coapply (Coindex a b) where
--  coapply (Coindex eab) = undefined 

instance a ~ b => Applicative (Coindex a b) where
  pure s = Coindex ($s)
  (<*>) = (<.>)

trivial :: Coindex a b b -> a
trivial (Coindex f) = f id
{-# INLINE trivial #-}

-- | Lift a regular function into a coindexed function.
--
-- For example, to traverse two layers, keeping only the first index:
--
-- @
--  Coindex 'Data.Map.mapWithKey' .#. noindex 'Data.Map.map'
--    :: Monoid k =>
--       Coindex (a -> b) (Map k (Map j a) -> Map k (Map j b)) k
-- @
--
noindex :: Monoid s => (b -> a) -> Coindex a b s
noindex f = Coindex $ \a -> f (a mempty)

coindex :: Functor f => s -> (b -> a) -> Coindex (f a) (f b) s
coindex s ab = Coindex $ \sfa -> fmap ab (sfa s)
{-# INLINE coindex #-}

infixr 9 <<<<

-- | Compose two coindexes.
--
-- When /s/ is a 'Monoid', 'Coindex' can be used to compose indexed traversals, folds, etc.
--
-- For example, to keep track of only the first index seen, use @Data.Monoid.First@:
--
-- @
--  fmap (First . pure) :: Coindex a b c -> Coindex a b (First c)
-- @
--
-- or keep track of all indices using a list:
--
-- @
--  fmap (:[]) :: Coindex a b c -> Coindex a b [c]
-- @
--
-- @since 0.0.3
(<<<<) :: Semigroup s => Coindex c b s -> Coindex b a s -> Coindex c a s
Coindex f <<<< Coindex g = Coindex $ \b -> f $ \s1 -> g $ \s2 -> b (s1 <> s2)

---------------------------------------------------------------------
-- Conjoin
---------------------------------------------------------------------

-- '(->)' is simultaneously both indexed and co-indexed.
newtype Conjoin j a b = Conjoin { unConjoin :: j -> a -> b }

instance Functor (Conjoin j a) where
  fmap g (Conjoin f) = Conjoin $ \j a -> g (f j a)
  {-# INLINE fmap #-}

instance Apply (Conjoin j a) where
  Conjoin f <.> Conjoin g = Conjoin $ \j a -> f j a (g j a)
  {-# INLINE (<.>) #-}

instance Applicative (Conjoin j a) where
  pure b = Conjoin $ \_ _ -> b
  {-# INLINE pure #-}
  Conjoin f <*> Conjoin g = Conjoin $ \j a -> f j a (g j a)
  {-# INLINE (<*>) #-}

instance Monad (Conjoin j a) where
  return = pure
  {-# INLINE return #-}
  Conjoin f >>= k = Conjoin $ \j a -> unConjoin (k (f j a)) j a
  {-# INLINE (>>=) #-}

instance MonadFix (Conjoin j a) where
  mfix f = Conjoin $ \ j a -> let o = unConjoin (f o) j a in o
  {-# INLINE mfix #-}

instance Profunctor (Conjoin j) where
  dimap ab cd jbc = Conjoin $ \j -> cd . unConjoin jbc j . ab
  {-# INLINE dimap #-}
  lmap ab jbc = Conjoin $ \j -> unConjoin jbc j . ab
  {-# INLINE lmap #-}
  rmap bc jab = Conjoin $ \j -> bc . unConjoin jab j
  {-# INLINE rmap #-}

instance Closed (Conjoin j) where
  closed (Conjoin jab) = Conjoin $ \j xa x -> jab j (xa x)

instance Costrong (Conjoin j) where
  unfirst (Conjoin jadbd) = Conjoin $ \j a -> let
      (b, d) = jadbd j (a, d)
    in b

instance Sieve (Conjoin j) ((->) j) where
  sieve = flip . unConjoin
  {-# INLINE sieve #-}

instance Representable (Conjoin j) where
  type Rep (Conjoin j) = (->) j
  tabulate = Conjoin . flip
  {-# INLINE tabulate #-}

instance Cosieve (Conjoin j) ((,) j) where
  cosieve = uncurry . unConjoin
  {-# INLINE cosieve #-}

instance Corepresentable (Conjoin j) where
  type Corep (Conjoin j) = (,) j
  cotabulate = Conjoin . curry
  {-# INLINE cotabulate #-}

instance Choice (Conjoin j) where
  right' = A.right
  {-# INLINE right' #-}

instance Strong (Conjoin j) where
  second' = A.second
  {-# INLINE second' #-}

instance Category (Conjoin j) where
  id = Conjoin (const id)
  {-# INLINE id #-}
  Conjoin f . Conjoin g = Conjoin $ \j -> f j . g j
  {-# INLINE (.) #-}

instance A.Arrow (Conjoin j) where
  arr f = Conjoin (\_ -> f)
  {-# INLINE arr #-}
  first f = Conjoin (A.first . unConjoin f)
  {-# INLINE first #-}
  second f = Conjoin (A.second . unConjoin f)
  {-# INLINE second #-}
  Conjoin f *** Conjoin g = Conjoin $ \j -> f j A.*** g j
  {-# INLINE (***) #-}
  Conjoin f &&& Conjoin g = Conjoin $ \j -> f j A.&&& g j
  {-# INLINE (&&&) #-}

instance A.ArrowChoice (Conjoin j) where
  left f = Conjoin (A.left . unConjoin f)
  {-# INLINE left #-}
  right f = Conjoin (A.right . unConjoin f)
  {-# INLINE right #-}
  Conjoin f +++ Conjoin g = Conjoin $ \j -> f j A.+++ g j
  {-# INLINE (+++)  #-}
  Conjoin f ||| Conjoin g = Conjoin $ \j -> f j A.||| g j
  {-# INLINE (|||) #-}

instance A.ArrowApply (Conjoin j) where
  app = Conjoin $ \k (f, b) -> unConjoin f k b
  {-# INLINE app #-}

instance A.ArrowLoop (Conjoin j) where
  loop (Conjoin f) = Conjoin $ \j b -> let (c,d) = f j (b, d) in c
  {-# INLINE loop #-}
