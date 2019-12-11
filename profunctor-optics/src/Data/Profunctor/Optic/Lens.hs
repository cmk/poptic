{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Optic.Lens (
    -- * Lens & Ixlens
    Lens
  , Ixlens
  , Lens'
  , Ixlens'
  , lens
  , ilens
  , lensVl
  , ilensVl
  , matching
  , cloneLens
    -- * Colens & Cxlens
  , Colens
  , Cxlens
  , Colens'
  , Cxlens'
  , colens
  --, klens
  , colensVl
  , comatching
  --, cloneColens
    -- * Optics
  , united
  , voided
    -- * Indexed optics
  , ifirst
  , isecond
    -- * Primitive operators
  , withLens
  , withLensVl
  , withIxlens
  --, withColens
    -- * Operators
  , toPastro
  , toTambara
    -- * Carriers
  , ALens
  , ALens'
  , AIxlens
  , AIxlens'
  , LensRep(..)
  , IxlensRep(..)
 -- , AColens
 -- , AColens'
  --, ColensRep(..)
    -- * Classes
  , Strong(..)
  , Costrong(..)
) where

import Data.Profunctor.Strong
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Index
import Data.Profunctor.Optic.Types
import qualified Data.Bifunctor as B

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> import Data.Int.Instance
-- >>> :load Data.Profunctor.Optic

---------------------------------------------------------------------
-- 'Lens' & 'Ixlens'
---------------------------------------------------------------------

-- | Obtain a 'Lens' from a getter and setter.
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input functions satisfy the following
-- properties:
--
-- * @sa (sbt s a) ≡ a@
--
-- * @sbt s (sa s) ≡ s@
--
-- * @sbt (sbt s a1) a2 ≡ sbt s a2@
--
-- See 'Data.Profunctor.Optic.Property'.
--
lens :: (s -> a) -> (s -> b -> t) -> Lens s t a b
lens sa sbt = dimap (id &&& sa) (uncurry sbt) . second'
{-# INLINE lens #-}

-- | Obtain an indexed 'Lens' from an indexed getter and a setter.
--
-- Compare 'lens' and 'Data.Profunctor.Optic.Traversal.itraversal'.
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input functions constitute a legal 
-- indexed lens:
--
-- * @snd . sia (sbt s a) ≡ a@
--
-- * @sbt s (snd $ sia s) ≡ s@
--
-- * @sbt (sbt s a1) a2 ≡ sbt s a2@
--
-- See 'Data.Profunctor.Optic.Property'.
--
ilens :: (s -> (i , a)) -> (s -> b -> t) -> Ixlens i s t a b
ilens sia sbt = ilensVl $ \iab s -> sbt s <$> uncurry iab (sia s)
{-# INLINE ilens #-}

-- | Transform a Van Laarhoven lens into a profunctor lens.
--
-- Compare 'Data.Profunctor.Optic.Grate.grateVl' and 'Data.Profunctor.Optic.Traversal.traversalVl'.
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input satisfies the following properties:
--
-- * @abst Identity ≡ Identity@
--
-- * @fmap (abst f) . (abst g) ≡ getCompose . abst (Compose . fmap f . g)@
--
-- More generally, a profunctor optic must be monoidal as a natural 
-- transformation:
-- 
-- * @o id ≡ id@
--
-- * @o ('Data.Profunctor.Composition.Procompose' p q) ≡ 'Data.Profunctor.Composition.Procompose' (o p) (o q)@
--
lensVl :: (forall f. Functor f => (a -> f b) -> s -> f t) -> Lens s t a b
lensVl abst = dimap ((info &&& vals) . abst (flip Index id)) (uncurry id . swap) . first'
{-# INLINE lensVl #-}

-- | Transform an indexed Van Laarhoven lens into an indexed profunctor 'Lens'.
--
-- An 'Ixlens' is a valid 'Lens' and a valid 'IxTraversal'. 
--
-- Compare 'lensVl' & 'Data.Profunctor.Optic.Traversal.itraversalVl'.
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input satisfies the following properties:
--
-- * @iabst (const Identity) ≡ Identity@
--
-- * @fmap (iabst $ const f) . (iabst $ const g) ≡ getCompose . iabst (const $ Compose . fmap f . g)@
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
ilensVl :: (forall f. Functor f => (i -> a -> f b) -> s -> f t) -> Ixlens i s t a b
ilensVl f = lensVl $ \iab -> f (curry iab) . snd
{-# INLINE ilensVl #-}

-- | Obtain a 'Lens' from its free tensor representation.
--
matching :: (s -> (c , a)) -> ((c , b) -> t) -> Lens s t a b
matching sca cbt = dimap sca cbt . second'

-- | TODO: Document
--
cloneLens :: ALens s t a b -> Lens s t a b
cloneLens o = withLens o lens 

---------------------------------------------------------------------
-- 'Colens' & 'Cxlens'
---------------------------------------------------------------------

-- | Obtain a 'Colens' from a getter and setter. 
--
-- @
-- 'colens' f g ≡ \\f g -> 're' ('lens' f g)
-- 'colens' bsia bt ≡ 'colensVl' '$' \\ts b -> bsia b '<$>' (ts . bt '$' b)
-- 'review' $ 'colens' f g ≡ f
-- 'set' . 're' $ 're' ('lens' f g) ≡ g
-- @
--
-- /Caution/: Colenses are recursive, similar to < http://hackage.haskell.org/package/base-4.12.0.0/docs/Control-Arrow.html#t:ArrowLoop ArrowLoop >. 
-- In addition to the normal optic laws, the input functions must have 
-- the correct < https://wiki.haskell.org/Lazy_pattern_match laziness > annotations.
--
-- For example, this is a perfectly valid 'Colens':
--
-- @
-- ct21 :: Colens a b (a, c) (b, c)
-- ct21 = flip colens fst $ \ ~(_,c) b -> (b,c)
-- @
--
-- However removing the annotation will result in a faulty optic.
-- 
-- See 'Data.Profunctor.Optic.Property'.
--
colens :: (b -> s -> a) -> (b -> t) -> Colens s t a b
colens bsa bt = unsecond . dimap (uncurry bsa) (id &&& bt)

-- | Transform a Van Laarhoven colens into a profunctor colens.
--
-- Compare 'Data.Profunctor.Optic.Grate.grateVl'.
--
-- /Caution/: In addition to the normal optic laws, the input functions
-- must have the correct laziness annotations.
--
-- For example, this is a perfectly valid 'Colens':
--
-- @ 
-- ct21 = colensVl $ \f ~(a,b) -> (,b) <$> f a
-- @
--
-- However removing the annotation will result in a faulty optic.
-- 
colensVl :: (forall f. Functor f => (t -> f s) -> b -> f a) -> Colens s t a b
colensVl o = unfirst . dimap (uncurry id . swap) ((info &&& vals) . o (flip Index id))

-- | Obtain a 'Colens' from its free tensor representation.
--
comatching :: ((c , s) -> a) -> (b -> (c , t)) -> Colens s t a b
comatching csa bct = unsecond . dimap csa bct

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

-- | Extract the two functions that characterize a 'Lens'.
--
withLens :: ALens s t a b -> ((s -> a) -> (s -> b -> t) -> r) -> r
withLens o f = case o (LensRep id (flip const)) of LensRep x y -> f x y

-- | Extract the higher order function that characterizes a 'Lens'.
--
-- The lens laws can be stated in terms of 'withLens':
-- 
-- Identity:
-- 
-- @
-- withLensVl o Identity ≡ Identity
-- @
-- 
-- Composition:
-- 
-- @ 
-- Compose . fmap (withLensVl o f) . withLensVl o g ≡ withLensVl o (Compose . fmap f . g)
-- @
--
-- See 'Data.Profunctor.Optic.Property'.
--
withLensVl :: Functor f => ALens s t a b -> (a -> f b) -> s -> f t
withLensVl o ab s = withLens o $ \sa sbt -> sbt s <$> ab (sa s)

---------------------------------------------------------------------
-- Optics 
---------------------------------------------------------------------

-- | TODO: Document
--
-- >>> ilists (ix @Int traversed . ix first' . ix traversed) [("foo",1), ("bar",2)]
-- [(0,'f'),(1,'o'),(2,'o'),(0,'b'),(1,'a'),(2,'r')]
--
-- >>> ilists (ix @Int traversed . ifirst . ix traversed) [("foo",1), ("bar",2)]
-- [(0,'f'),(1,'o'),(2,'o'),(0,'b'),(1,'a'),(2,'r')]
--
-- >>> ilists (ix @Int traversed % ix first' % ix traversed) [("foo",1), ("bar",2)]
-- [(0,'f'),(1,'o'),(2,'o'),(1,'b'),(2,'a'),(3,'r')]
--
-- >>> ilists (ix @Int traversed % ifirst % ix traversed) [("foo",1), ("bar",2)]
-- [(0,'f'),(1,'o'),(2,'o'),(2,'b'),(3,'a'),(4,'r')]
--
ifirst :: Ixlens i (a , c) (b , c) a b
ifirst = lmap assocl . first'

-- | TODO: Document
--
isecond :: Ixlens i (c , a) (c , b) a b
isecond = lmap (\(i, (c, a)) -> (c, (i, a))) . second'

-- | There is a '()' in everything.
--
-- >>> "hello" ^. united
-- ()
-- >>> "hello" & united .~ ()
-- "hello"
--
united :: Lens' a ()
united = lens (const ()) const

-- | There is everything in a 'Void'.
--
-- >>> [] & fmapped . voided <>~ "Void" 
-- []
-- >>> Nothing & fmapped . voided ..~ abs
-- Nothing
--
voided :: Lens' Void a
voided = lens absurd const

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- | Use a 'Lens' to construct a 'Pastro'.
--
toPastro :: ALens s t a b -> p a b -> Pastro p s t
toPastro o p = withLens o $ \sa sbt -> Pastro (uncurry sbt . swap) p (\s -> (sa s, s))

-- | Use a 'Lens' to construct a 'Tambara'.
--
toTambara :: Strong p => ALens s t a b -> p a b -> Tambara p s t
toTambara o p = withLens o $ \sa sbt -> Tambara (first' . lens sa sbt $ p)

---------------------------------------------------------------------
-- LensRep
---------------------------------------------------------------------

-- | The `LensRep` profunctor precisely characterizes a 'Lens'.
--
data LensRep a b s t = LensRep (s -> a) (s -> b -> t)

type ALens s t a b = Optic (LensRep a b) s t a b

type ALens' s a = ALens s s a a

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

data IxlensRep i a b s t = IxlensRep (s -> (i , a)) (s -> b -> t)

type AIxlens i s t a b = IndexedOptic (IxlensRep i a b) i s t a b

type AIxlens' i s a = AIxlens i s s a a

instance Profunctor (IxlensRep i a b) where
  dimap f g (IxlensRep sia sbt) = IxlensRep (sia . f) (\s -> g . sbt (f s))

instance Strong (IxlensRep i a b) where
  first' (IxlensRep sia sbt) =
    IxlensRep (\(a, _) -> sia a) (\(s, c) b -> (sbt s b, c))

  second' (IxlensRep sia sbt) =
    IxlensRep (\(_, a) -> sia a) (\(c, s) b -> (c, sbt s b))

-- | Extract the two functions that characterize a 'Lens'.
--
withIxlens :: Monoid i => AIxlens i s t a b -> ((s -> (i , a)) -> (s -> b -> t) -> r) -> r
withIxlens o f = case o (IxlensRep id $ flip const) of IxlensRep x y -> f (x . (mempty,)) (\s b -> y (mempty, s) b)
