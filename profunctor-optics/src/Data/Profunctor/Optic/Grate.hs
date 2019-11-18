{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Optic.Grate  (
    -- * Types
    Closed(..)
  , Grate
  , Grate'
  , Cxgrate
  , Cxgrate'
  , AGrate
  , AGrate'
    -- * Constructors
  , grate
  , cxgrate
  , grateVl
  , cxgrateVl
  , inverting
  , cloneGrate
    -- * Representatives
  , GrateRep(..)
    -- * Primitive operators
  , withGrate 
  , constOf
  , zipWithOf
  , zipWith3Of
  , zipWith4Of 
  , zipWithFOf 
    -- * Optics
  --, closed
  , cxclosed
  , cxfirst
  , cxsecond
  , distributed
  , connected
  , forwarded
  , continued
  , unlifted
    -- * Operators
  , toEnvironment
  , toClosure
) where

import Control.Monad.Reader
import Control.Monad.Cont
import Control.Monad.IO.Unlift
import Data.Distributive
import Data.Connection (Conn(..))
import Data.Profunctor.Closed
import Data.Profunctor.Optic.Iso
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Indexed
import Data.Profunctor.Rep (unfirstCorep)

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> :set -XTupleSections
-- >>> import Control.Exception
-- >>> import Control.Monad.Reader
-- >>> import Data.Connection.Int
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
-- isomorphic to a fixed length vector (e.g. 'V2 a').
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
-- * @sabt (\k -> h (k . sabt)) ≡ sabt (\k -> h ($ k))@
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

-- | TODO: Document
--
cxgrate :: (((s -> a) -> k -> b) -> t) -> Cxgrate k s t a b
cxgrate f = grate $ \sakb _ -> f sakb

-- | Transform a Van Laarhoven grate into a profunctor grate.
--
-- Compare 'Data.Profunctor.Optic.Lens.vlens' & 'Data.Profunctor.Optic.Traversal.cotraversalVl'.
--
grateVl :: (forall f. Functor f => (f a -> b) -> f s -> t) -> Grate s t a b 
grateVl o = dimap (curry eval) ((o trivial) . Coindex) . closed

-- | TODO: Document
--
cxgrateVl :: (forall f. Functor f => (k -> f a -> b) -> f s -> t) -> Cxgrate k s t a b
cxgrateVl f = grateVl $ \kab -> const . f (flip kab) 

-- | Construct a 'Grate' from a pair of inverses.
--
inverting :: (s -> a) -> (b -> t) -> Grate s t a b
inverting sa bt = grate $ \sab -> bt (sab sa)

-- | TODO: Document
--
cloneGrate :: AGrate s t a b -> Grate s t a b
cloneGrate k = withGrate k grate

---------------------------------------------------------------------
-- 'GrateRep'
---------------------------------------------------------------------

-- | The 'GrateRep' profunctor precisely characterizes 'Grate'.
--
newtype GrateRep a b s t = GrateRep { unGrateRep :: ((s -> a) -> b) -> t }

type AGrate s t a b = Optic (GrateRep a b) s t a b

type AGrate' s a = AGrate s s a a

instance Profunctor (GrateRep a b) where
  dimap f g (GrateRep z) = GrateRep $ \d -> g (z $ \k -> d (k . f))

instance Closed (GrateRep a b) where
  closed (GrateRep sabt) = GrateRep $ \xsab x -> sabt $ \sa -> xsab $ \xs -> sa (xs x)

instance Costrong (GrateRep a b) where
  unfirst = unfirstCorep

instance Cosieve (GrateRep a b) (Coindex a b) where
  cosieve (GrateRep f) (Coindex g) = f g

instance Corepresentable (GrateRep a b) where
  type Corep (GrateRep a b) = Coindex a b

  cotabulate f = GrateRep $ f . Coindex

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

-- | Extract the function that characterizes a 'Lens'.
--
withGrate :: AGrate s t a b -> ((((s -> a) -> b) -> t) -> r) -> r
withGrate o k = case o (GrateRep $ \f -> f id) of GrateRep sabt -> k sabt

-- | Set all fields to the given value.
--
constOf :: AGrate s t a b -> b -> t
constOf o b = withGrate o $ \sabt -> sabt (const b)

-- | Zip over a 'Grate'. 
--
-- @\f -> 'zipWithOf' 'closed' ('zipWithOf' 'closed' f) ≡ 'zipWithOf' ('closed' . 'closed')@
--
zipWithOf :: AGrate s t a b -> (a -> a -> b) -> s -> s -> t
zipWithOf o comb s1 s2 = withGrate o $ \sabt -> sabt $ \get -> comb (get s1) (get s2)

-- | Zip over a 'Grate' with 3 arguments.
--
zipWith3Of :: AGrate s t a b -> (a -> a -> a -> b) -> (s -> s -> s -> t)
zipWith3Of o comb s1 s2 s3 = withGrate o $ \sabt -> sabt $ \get -> comb (get s1) (get s2) (get s3)

-- | Zip over a 'Grate' with 4 arguments.
--
zipWith4Of :: AGrate s t a b -> (a -> a -> a -> a -> b) -> (s -> s -> s -> s -> t)
zipWith4Of o comb s1 s2 s3 s4 = withGrate o $ \sabt -> sabt $ \get -> comb (get s1) (get s2) (get s3) (get s4)

-- | Transform a profunctor grate into a Van Laarhoven grate.
--
-- This is a more restricted version of 'Data.Profunctor.Optic.Repn.corepnOf'
--
zipWithFOf :: Functor f => AGrate s t a b -> (f a -> b) -> f s -> t
zipWithFOf o comb fs = withGrate o $ \sabt -> sabt $ \get -> comb (fmap get fs)

---------------------------------------------------------------------
-- Optics 
---------------------------------------------------------------------

-- | Access the contents of a distributive functor.
--
distributed :: Distributive f => Grate (f a) (f b) a b
distributed = grate (`cotraverse` id)
{-# INLINE distributed #-}

-- | Lift a Galois connection into a 'Grate'. 
--
-- Useful for giving precise semantics to numerical computations.
--
-- This is an example of a 'Grate' that would not be a legal 'Iso',
-- as Galois connections are not in general inverses.
--
-- >>> zipWithOf (connected i08i16) (+) 126 1
-- 127
-- >>> zipWithOf (connected i08i16) (+) 126 2
-- 127
--
connected :: Conn s a -> Grate' s a
connected (Conn f g) = inverting f g
{-# INLINE connected #-}

-- | Lift an action into a 'MonadReader'.
--
forwarded :: Distributive m => MonadReader r m => Grate (m a) (m b) a b
forwarded = distributed
{-# INLINE forwarded #-}

-- | Lift an action into a continuation.
--
-- @
-- 'zipWithOf' 'continued' :: (r -> r -> r) -> s -> s -> Cont r s
-- @
--
continued :: Grate a (Cont r a) r r
continued = grate cont
{-# INLINE continued #-}

-- | Unlift an action into an 'IO' context.
--
-- @
-- 'liftIO' ≡ 'constOf' 'unlifted'
-- @
--
-- >>> let catchA = catch @ArithException
-- >>> zipWithOf unlifted (flip catchA . const) (throwIO Overflow) (print "caught") 
-- "caught" 
--
unlifted :: MonadUnliftIO m => Grate (m a) (m b) (IO a) (IO b)
unlifted = grate withRunInIO
{-# INLINE unlifted #-}

-- >>> cxover cxclosed (,) (*2) 5
-- ((),10)
--
cxclosed :: Cxgrate k (c -> a) (c -> b) a b
cxclosed = rmap flip . closed
{-# INLINE cxclosed #-}

-- | TODO: Document
--
cxfirst :: Cxgrate k a b (a , c) (b , c)
cxfirst = rmap (unfirst . uncurry . flip) . curry'
{-# INLINE cxfirst #-}

-- | TODO: Document
--
cxsecond :: Cxgrate k a b (c , a) (c , b)
cxsecond = rmap (unsecond . uncurry) . curry' . lmap swap
{-# INLINE cxsecond #-}

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- | Use a 'Grate' to construct an 'Environment'.
--
toEnvironment :: Closed p => AGrate s t a b -> p a b -> Environment p s t
toEnvironment o p = withGrate o $ \sabt -> Environment sabt p (curry eval)
{-# INLINE toEnvironment #-}

-- | Use a 'Grate' to construct a 'Closure'.
--
toClosure :: Closed p => AGrate s t a b -> p a b -> Closure p s t
toClosure o p = withGrate o $ \sabt -> Closure (closed . grate sabt $ p)
{-# INLINE toClosure #-}
