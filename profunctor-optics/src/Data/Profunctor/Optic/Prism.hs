{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Optic.Prism (
    -- * Prism & Cxprism
    Choice(..)
  , Prism
  , Prism'
  , Cxprism
  , Cxprism'
  , APrism
  , APrism'
  , prism
  , prism'
  , cxprism
  , handling
  , clonePrism
    -- * Coprism & Ixprism
  , Cochoice(..)
  , Coprism
  , Coprism'
  , Ixprism
  , Ixprism'
  , ACoprism
  , ACoprism'
  , coprism
  , coprism'
  , ixprism
  , ixprism'
  , rehandling
  , cloneCoprism
    -- * Carriers
  , PrismRep(..)
  , CoprismRep(..)
    -- * Primitive operators
  , withPrism
  , withCoprism
    -- * Optics
  , left
  , right
  , l1
  , r1
  , coleft
  , coright
  , ixleft
  , ixright
  , just
  , cxjust
  , nothing
  , keyed
  , filtered
  , compared
  , prefixed
  , only
  , nearly
  , nthbit
  , sync
  , async
  , exception
  , asyncException
    -- * Operators
  , aside
  , without
  , below
  , toPastroSum
  , toTambaraSum
) where

import Control.Exception
import Control.Monad (guard)
import Data.Bifunctor as B
import Data.Bits (Bits, bit, testBit)
import Data.List (stripPrefix)
import Data.Prd
import Data.Profunctor.Choice
import Data.Profunctor.Optic.Iso
import Data.Profunctor.Optic.Import 
import Data.Profunctor.Optic.Type

import GHC.Generics hiding (from, to)

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> :set -XRankNTypes
-- >>> :load Data.Profunctor.Optic
-- >>> let catchOn :: Int -> Cxprism' Int (Maybe String) String ; catchOn n = cxjust $ \k -> if k==n then Just "caught" else Nothing

---------------------------------------------------------------------
-- 'Prism' & 'Cxprism'
---------------------------------------------------------------------

-- | Obtain a 'Prism' from a constructor and a matcher function.
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input functions satisfy the following
-- properties:
--
-- * @sta (bt b) ≡ Right b@
--
-- * @(id ||| bt) (sta s) ≡ s@
--
-- * @left sta (sta s) ≡ left Left (sta s)@
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
prism :: (s -> t + a) -> (b -> t) -> Prism s t a b
prism sta bt = dimap sta (id ||| bt) . right'

-- | Obtain a 'Prism'' from a reviewer and a matcher function that produces a 'Maybe'.
--
prism' :: (s -> Maybe a) -> (a -> s) -> Prism' s a
prism' sa as = flip prism as $ \s -> maybe (Left s) Right (sa s)

-- | Obtain a 'Cxprism'' from a reviewer and a matcher function that returns either a match or a failure handler.
--
cxprism :: (s -> (k -> t) + a) -> (b -> t) -> Cxprism k s t a b
cxprism skta bt = prism skta (bt .)

-- | Obtain a 'Prism' from its free tensor representation.
--
-- Useful for constructing prisms from try and handle functions.
--
handling :: (s -> c + a) -> (c + b -> t) -> Prism s t a b
handling sca cbt = dimap sca cbt . right'

-- | TODO: Document
--
clonePrism :: APrism s t a b -> Prism s t a b
clonePrism o = withPrism o prism

---------------------------------------------------------------------
-- 'Coprism' & 'Ixprism'
---------------------------------------------------------------------

-- | Obtain a 'Cochoice' optic from a constructor and a matcher function.
--
-- @
-- coprism f g ≡ \f g -> re (prism f g)
-- @
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input functions satisfy the following
-- properties:
--
-- * @bat (bt b) ≡ Right b@
--
-- * @(id ||| bt) (bat b) ≡ b@
--
-- * @left bat (bat b) ≡ left Left (bat b)@
--
-- A 'Coprism' is a 'View', so you can specialise types to obtain:
--
-- @ view :: 'Coprism'' s a -> s -> a @
--
coprism :: (s -> a) -> (b -> a + t) -> Coprism s t a b
coprism sa bat = unright . dimap (id ||| sa) bat

-- | Create a 'Coprism' from a reviewer and a matcher function that produces a 'Maybe'.
--
coprism' :: (s -> a) -> (a -> Maybe s) -> Coprism' s a
coprism' tb bt = coprism tb $ \b -> maybe (Left b) Right (bt b)

-- | Obtain an 'Ixprism' from an indexed reviewer and a matcher function.
--
ixprism :: Monoid r => (r -> s -> a) -> (b -> a + t) -> Ixprism r s t a b
ixprism rsa bat = coprism (const mempty &&& uncurry rsa) (B.first (mempty,) . bat)

-- | Obtain an 'Ixprism'' from an indexed reviewer and a matcher function that produces a 'Maybe'.
--
ixprism' :: Monoid r => (r -> s -> a) -> (a -> Maybe s) -> Ixprism' r s a
ixprism' rsa = coprism' (rsa mempty)

-- | Obtain a 'Coprism' from its free tensor representation.
--
rehandling :: (c + s -> a) -> (b -> c + t) -> Coprism s t a b
rehandling csa bct = unright . dimap csa bct

-- | TODO: Document
--
cloneCoprism :: ACoprism s t a b -> Coprism s t a b
cloneCoprism o = withCoprism o coprism

---------------------------------------------------------------------
-- 'PrismRep' & 'CoprismRep'
---------------------------------------------------------------------

type APrism s t a b = Optic (PrismRep a b) s t a b

type APrism' s a = APrism s s a a

-- | The 'PrismRep' profunctor precisely characterizes a 'Prism'.
--
data PrismRep a b s t = PrismRep (s -> t + a) (b -> t)

instance Functor (PrismRep a b s) where
  fmap f (PrismRep sta bt) = PrismRep (first f . sta) (f . bt)
  {-# INLINE fmap #-}

instance Profunctor (PrismRep a b) where
  dimap f g (PrismRep sta bt) = PrismRep (first g . sta . f) (g . bt)
  {-# INLINE dimap #-}

  lmap f (PrismRep sta bt) = PrismRep (sta . f) bt
  {-# INLINE lmap #-}

  rmap = fmap
  {-# INLINE rmap #-}

instance Choice (PrismRep a b) where
  left' (PrismRep sta bt) = PrismRep (either (first Left . sta) (Left . Right)) (Left . bt)
  {-# INLINE left' #-}

  right' (PrismRep sta bt) = PrismRep (either (Left . Left) (first Right . sta)) (Right . bt)
  {-# INLINE right' #-}

type ACoprism s t a b = Optic (CoprismRep a b) s t a b

type ACoprism' s a = ACoprism s s a a

data CoprismRep a b s t = CoprismRep (s -> a) (b -> a + t) 

instance Functor (CoprismRep a b s) where
  fmap f (CoprismRep sa bat) = CoprismRep sa (second f . bat)
  {-# INLINE fmap #-}

instance Profunctor (CoprismRep a b) where
  lmap f (CoprismRep sa bat) = CoprismRep (sa . f) bat
  {-# INLINE lmap #-}

  rmap = fmap
  {-# INLINE rmap #-}

instance Cochoice (CoprismRep a b) where
  unleft (CoprismRep sca batc) = CoprismRep (sca . Left) (forgetr $ either (eassocl . batc) Right)
  {-# INLINE unleft #-}

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

-- | Extract the two functions that characterize a 'Prism'.
--
withPrism :: APrism s t a b -> ((s -> t + a) -> (b -> t) -> r) -> r
withPrism o f = case o (PrismRep Right id) of PrismRep g h -> f g h

-- | Extract the two functions that characterize a 'Coprism'.
--
withCoprism :: ACoprism s t a b -> ((s -> a) -> (b -> a + t) -> r) -> r
withCoprism o f = case o (CoprismRep id Right) of CoprismRep g h -> f g h

---------------------------------------------------------------------
-- Common 'Prism's and 'Coprism's
---------------------------------------------------------------------

-- | 'Prism' into the `Left` constructor of `Either`.
--
left :: Prism (a + c) (b + c) a b
left = left'

-- | 'Prism' into the `Right` constructor of `Either`.
--
right :: Prism (c + a) (c + b) a b
right = right'

l1 :: Prism ((a :+: c) t) ((b :+: c) t) (a t) (b t)
l1 = prism sta L1
  where
  sta (L1 v) = Right v
  sta (R1 v) = Left (R1 v)
{-# INLINE l1 #-}

r1 :: Prism ((c :+: a) t) ((c :+: b) t) (a t) (b t)
r1 = prism sta R1
  where
  sta (R1 v) = Right v
  sta (L1 v) = Left (L1 v)
{-# INLINE r1 #-}

-- | 'Coprism' out of the `Left` constructor of `Either`.
--
coleft :: Coprism a b (a + c) (b + c)
coleft = unleft

-- | 'Coprism' out of the `Right` constructor of `Either`.
--
coright :: Coprism a b (c + a) (c + b)
coright = unright

-- | Indexed 'Ixprism' out of the `Left` constructor of `Either`.
--
-- >>> ixview ixleft 7
-- (Just (),Left 7)
--
ixleft :: Monoid r => Ixprism r a b (a + c) (b + c)
ixleft = unleft . lmap (either (fmap Left) ((mempty,) . Right))

-- | Indexed 'Ixprism' out of the `Right` constructor of `Either`.
--
ixright :: Monoid r => Ixprism r a b (c + a) (c + b)
ixright = unright . lmap (either ((mempty,) . Left) (fmap Right))

-- | 'Prism' into the `Just` constructor of `Maybe`.
--
just :: Prism (Maybe a) (Maybe b) a b
just = flip prism Just $ maybe (Left Nothing) Right

-- | 'Cxprism' into the `Just` constructor of `Maybe`.
--
-- cxmatches (catchOn 0) Nothing 0
-- Left (Just "caught")
--
cxjust :: (k -> Maybe b) -> Cxprism k (Maybe a) (Maybe b) a b
cxjust kb = flip cxprism Just $ maybe (Left $ kb) Right

-- | 'Prism' into the `Nothing` constructor of `Maybe`.
--
nothing :: Prism (Maybe a) (Maybe b) () ()
nothing = flip prism  (const Nothing) $ maybe (Right ()) (const $ Left Nothing)

-- | Match a given key to obtain the associated value. 
--
keyed :: Eq a => a -> Prism' (a , b) b
keyed x = flip prism ((,) x) $ \kv@(k,v) -> branch (==x) kv v k

-- | Filter another optic.
--
-- >>> [1..10] ^.. folded . filtered even
-- [2,4,6,8,10]
--
filtered :: (a -> Bool) -> Prism' a a
filtered f = iso (branch' f) join . right 

-- | Focus on comparability to a given element of a partial order.
--
compared :: Eq a => Prd a => a -> Prism' a Ordering
compared x = flip prism' (const x) (pcompare x)

-- | 'Prism' into the remainder of a list with a given prefix.
--
prefixed :: Eq a => [a] -> Prism' [a] [a]
prefixed ps = prism' (stripPrefix ps) (ps ++)

-- | Focus not just on a case, but a specific value of that case.
--
only :: Eq a => a -> Prism' a ()
only x = nearly x (x==)

-- | Create a 'Prism' from a value and a predicate.
--
nearly :: a -> (a -> Bool) -> Prism' a ()
nearly x f = prism' (guard . f) (const x)

-- | Focus on the truth value of the nth bit in a bit array.
--
nthbit :: Bits s => Int -> Prism' s ()
nthbit n = prism' (guard . (flip testBit n)) (const $ bit n)

-- | Check whether an exception is synchronous.
--
sync :: Exception e => Prism' e e 
sync = filtered $ \e -> case fromException (toException e) of
  Just (SomeAsyncException _) -> False
  Nothing -> True

-- | Check whether an exception is asynchronous.
--
async :: Exception e => Prism' e e 
async = filtered $ \e -> case fromException (toException e) of
  Just (SomeAsyncException _) -> True
  Nothing -> False

-- | TODO: Document
--
exception :: Exception e => Prism' SomeException e
exception = prism' fromException toException

-- | TODO: Document
--
asyncException :: Exception e => Prism' SomeException e
asyncException = prism' asyncExceptionFromException asyncExceptionToException

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- | Use a 'Prism' to lift part of a structure.
--
aside :: APrism s t a b -> Prism (e , s) (e , t) (e , a) (e , b)
aside k =
  withPrism k $ \sta bt ->
    flip prism (fmap bt) $ \(e,s) ->
      case sta s of
        Left t  -> Left  (e,t)
        Right a -> Right (e,a)
{-# INLINE aside #-}

-- | Given a pair of prisms, project sums.
without :: APrism s t a b -> APrism u v c d -> Prism (s + u) (t + v) (a + c) (b + d)
without k =
  withPrism k $ \sta bt k' ->
    withPrism k' $ \uevc dv ->
      flip prism (bimap bt dv) $ \su ->
        case su of
          Left s  -> bimap Left Left (sta s)
          Right u -> bimap Right Right (uevc u)
{-# INLINE without #-}

-- | Lift a 'Prism' through a 'Traversable' functor.
-- 
-- Returns a 'Prism' that matches only if each element matches the original 'Prism'.
--
-- >>> [Left 1, Right "foo", Left 4, Right "woot"] ^.. below right
-- []
--
-- >>> [Right "hail hydra!", Right "foo", Right "blah", Right "woot"] ^.. below right
-- [["hail hydra!","foo","blah","woot"]]
--
below :: Traversable f => APrism' s a -> Prism' (f s) (f a)
below k =
  withPrism k $ \sta bt ->
    flip prism (fmap bt) $ \s ->
      case traverse sta s of
        Left _  -> Left s
        Right t -> Right t
{-# INLINE below #-}

-- | Use a 'Prism' to construct a 'PastroSum'.
--
toPastroSum :: APrism s t a b -> p a b -> PastroSum p s t
toPastroSum o p = withPrism o $ \sta bt -> PastroSum (join . B.first bt) p (eswap . sta)

-- | Use a 'Prism' to construct a 'TambaraSum'.
--
toTambaraSum :: Choice p => APrism s t a b -> p a b -> TambaraSum p s t
toTambaraSum o p = withPrism o $ \sta bt -> TambaraSum (left . prism sta bt $ p)
