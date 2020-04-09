{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
module Data.Profunctor.Optic.Iso (
    -- * Types
    Equality
  , Equality'
  , Iso
  , Iso'
  , iso
  , isoVl
  , cloneIso
  , fmapping
  , contramapping
  , dimapping
  , toYoneda 
  , toCoyoneda
  , invert
    -- * Optics
  , equaled
  , coerced
  , wrapped
  , rewrapped
  , rewrapped'
  , generic
  , generic1
  , adjuncted
  , tabulated
  , sieved
  , cosieved
  , unzipped
  , cozipped
  , pair'
  , maybe'
  , either'
  , swapped 
  , coswapped 
  , associated 
  , coassociated
  , excised
  , flipped 
  , involuted
  , uncurried
  , strict
  , chunked
  , unpacked
  , reversed
    -- * Operators
  , op
  , au 
  , aup
  , ala
  , reover
  , reixes
  , recxes
    -- * Re
  , Re(..)
    -- * Classes
  , Profunctor(..)
) where

import Control.Newtype.Generics (Newtype(..), op)
import Data.Coerce
import Data.Functor.Adjunction hiding (adjuncted)
import Data.Maybe (fromMaybe)
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Combinator
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Types
import Data.Profunctor.Yoneda (Coyoneda(..), Yoneda(..))
import Data.Sequences (IsSequence, LazySequence(..))
import Data.MonoTraversable (Element)
import qualified Data.Functor.Rep as F
import qualified Data.Sequences as S
import qualified Data.Strict.Either as E'
import qualified Data.Strict.Maybe as M'
import qualified Data.Strict.Tuple as T'
import qualified Control.Monad as M (join)
import qualified GHC.Generics as G

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XAllowAmbiguousTypes
-- >>> import Data.Monoid
-- >>> import Data.List.Index
-- >>> import Data.Semiring
-- >>> import Data.Function ((&))
-- >>> import Data.Functor.Identity
-- >>> import Data.Functor.Const
-- >>> import Data.Profunctor.Types
-- >>> :load Data.Profunctor.Optic

---------------------------------------------------------------------
-- 'Iso' 
---------------------------------------------------------------------

-- | Obtain an 'Iso' from two inverses.
--
-- @
-- o . 're' o ≡ 'id'
-- 're' o . o ≡ 'id'
-- 'Data.Profunctor.Optic.View.view' o ('Data.Profunctor.Optic.View.review' o b) ≡ b
-- 'Data.Profunctor.Optic.View.review' o ('Data.Profunctor.Optic.View.view' o s) ≡ s
-- @
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input functions satisfy the following
-- properties:
--
-- * @sa . bt ≡ id@
--
-- * @bt . sa ≡ id@
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
iso :: (s -> a) -> (b -> t) -> Iso s t a b
iso = dimap
{-# INLINE iso #-}

-- | Transform a Van Laarhoven 'Iso' into a profunctor 'Iso'.
--
isoVl :: (forall f g. Functor f => Functor g => (g a -> f b) -> g s -> f t) -> Iso s t a b
isoVl abst = iso f g
  where f = getConst . (abst (Const . runIdentity)) . Identity
        g = runIdentity . (abst (Identity . getConst)) . Const
{-# INLINE isoVl #-}

-- | Lift an 'Iso' into a pair of functors.
--
fmapping :: Functor f => Functor g => AIso s t a b -> Iso (f s) (g t) (f a) (g b)
fmapping l = withIso l $ \sa bt -> iso (fmap sa) (fmap bt)
{-# INLINE fmapping #-}

-- | Lift an 'Iso' into a pair of 'Contravariant' functors.
--
contramapping :: Contravariant f => Contravariant g => AIso s t a b -> Iso (f a) (g b) (f s) (g t)
contramapping f = withIso f $ \sa bt -> iso (contramap sa) (contramap bt)
{-# INLINE contramapping #-}

-- | Lift a pair of 'Iso's into a pair of profunctors. 
--
dimapping :: Profunctor p => Profunctor q => AIso s1 t1 a1 b1 -> AIso s2 t2 a2 b2 -> Iso (p a1 s2) (q b1 t2) (p s1 a2) (q t1 b2)
dimapping f g = withIso f $ \sa1 bt1 -> withIso g $ \sa2 bt2 -> iso (dimap sa1 sa2) (dimap bt1 bt2)
{-# INLINE dimapping #-}

-- | Lift an 'Iso' into a 'Yoneda'.
--
toYoneda :: Profunctor p => Iso s t a b -> p a b -> Yoneda p s t
toYoneda o p = withIso o $ \sa bt -> Yoneda $ \f g -> dimap (sa . f) (g . bt) p 
{-# INLINE toYoneda #-}

-- | Lift an 'Iso' into a 'Coyoneda'.
--
toCoyoneda :: Iso s t a b -> p a b -> Coyoneda p s t
toCoyoneda o p = withIso o $ \sa bt -> Coyoneda sa bt p
{-# INLINE toCoyoneda #-}

-- | Invert an isomorphism.
--
-- @
-- 'invert' ('invert' o) ≡ o
-- @
--
invert :: AIso s t a b -> Iso b a t s
invert o = withIso o $ \sa bt -> iso bt sa
{-# INLINE invert #-}

-- | Convert from 'AIso' back to any 'Iso'.
--
cloneIso :: AIso s t a b -> Iso s t a b
cloneIso k = withIso k iso
{-# INLINE cloneIso #-}

---------------------------------------------------------------------
-- Optics
---------------------------------------------------------------------

-- | Obtain an 'Iso'' directly from type equality constraints.
--
-- >>> :t (^. equaled)
-- (^. equaled) :: b -> b
--
equaled :: s ~ a => t ~ b => Iso s t a b
equaled = id
{-# INLINE equaled #-}

-- | Obtain an 'Iso' from data types that are representationally equal.
--
-- >>> view coerced 'x' :: Identity Char
-- Identity 'x'
--
coerced :: Coercible s a => Coercible t b => Iso s t a b
coerced = dimap coerce coerce
{-# INLINE coerced #-}

-- | Obtain an 'Iso' from a newtype.
--
-- @
-- 'Data.Profunctor.Optic.View.view' 'wrapped' f '.' f ≡ 'id'
-- f '.' 'Data.Profunctor.Optic.View.view' 'wrapped' f ≡ 'id'
-- @
--
-- >>> view wrapped $ Identity 'x'
-- 'x'
--
-- >>> view wrapped (Const "hello")
-- "hello"
--
wrapped :: Newtype s => Iso' s (O s)
wrapped = dimap unpack pack
{-# INLINE wrapped #-}

-- | An 'Iso' between newtype wrappers.
--
-- >>> Const "hello" & rewrapped ..~ Prelude.length & getConst
-- 5
--
rewrapped :: Newtype s => Newtype t => Iso s t (O s) (O t)
rewrapped = withIso wrapped $ \ sa _ -> withIso wrapped $ \ _ bt -> iso sa bt
{-# INLINE rewrapped #-}

-- | A variant of 'rewrapped' that ignores its argument.
--
rewrapped' :: Newtype s => Newtype t => (O s -> s) -> Iso s t (O s) (O t)
rewrapped' _ = rewrapped
{-# INLINE rewrapped' #-}

-- | An 'Iso' between 'Generic' representations.
--
-- >>> view (generic . re generic) "hello" :: String
-- "hello"
--
generic :: G.Generic a => G.Generic b => Iso a b (G.Rep a c) (G.Rep b c)
generic = iso G.from G.to
{-# INLINE generic #-}

-- | An 'Iso' between 'Generic1' representations.
--
generic1 :: G.Generic1 f => G.Generic1 g => Iso (f a) (g b) (G.Rep1 f a) (G.Rep1 g b)
generic1 = iso G.from1 G.to1
{-# INLINE generic1 #-}

-- | An 'Iso' between a functor and its adjoint.
--
-- Useful for converting between lens-like optics and grate-like optics:
--
-- @
-- 'Data.Profunctor.Optic.Setter.over' 'adjuncted' :: 'Adjunction' f u => ((a -> u b) -> s -> u t) -> (f a -> b) -> f s -> t
-- @
--
adjuncted :: Adjunction f u => Iso (f a -> b) (f s -> t) (a -> u b) (s -> u t)
adjuncted = iso leftAdjunct rightAdjunct
{-# INLINE adjuncted #-}

-- | An 'Iso' between a functor and its Yoneda representation.
--
tabulated :: F.Representable f => F.Representable g => Iso (f a) (g b) (F.Rep f -> a) (F.Rep g -> b)
tabulated = iso F.index F.tabulate
{-# INLINE tabulated #-}

-- | TODO: Document
--
sieved :: ((a -> b) -> s -> t) -> Iso s t (Index s x x) (Index s a b)
sieved abst = iso (flip Index id) (\(Index s ab) -> abst ab s) 
{-# INLINE sieved #-}

-- | TODO: Document
--
cosieved :: ((a -> b) -> s -> t) -> Iso s t (Coindex t b a) (Coindex t x x)
cosieved abst = iso (\s -> Coindex $ \ab -> abst ab s) trivial
{-# INLINE cosieved #-}

-- | A right adjoint admits an intrinsic notion of zipping.
--
unzipped :: Adjunction f u => Iso (u a , u b) (u c , u d) (u (a , b)) (u (c , d)) 
unzipped = iso zipR unzipR
{-# INLINE unzipped #-}

-- | A left adjoint must be inhabited by exactly one element.
--
cozipped :: Adjunction f u => Iso ((f a) + (f b)) ((f c) + (f d)) (f (a + b)) (f (c + d))
cozipped = iso uncozipL cozipL
{-# INLINE cozipped #-}

-- | An 'Iso' between strict & lazy variants of /(,)/.
--
-- @since 0.0.3
pair' :: Iso (a , b) (c , d) (T'.Pair a b) (T'.Pair c d)
pair' = iso (uncurry (T'.:!:)) (T'.fst &&& T'.snd)
{-# INLINE pair' #-}

-- | An 'Iso' between strict & lazy variants of /Maybe/.
--
-- @since 0.0.3
maybe' :: Iso (Maybe a) (Maybe b) (M'.Maybe a) (M'.Maybe b)
maybe' = iso (maybe M'.Nothing M'.Just) (M'.maybe Nothing Just)
{-# INLINE maybe' #-}

-- | An 'Iso' between strict & lazy variants of /Either/.
--
-- @since 0.0.3
either' :: Iso (Either a b) (Either c d) (E'.Either a b) (E'.Either c d)
either' = iso (either E'.Left E'.Right) (E'.either Left Right)
{-# INLINE either' #-}

-- | Swap sides of a product.
--
swapped :: Iso (a , b) (c , d) (b , a) (d , c)
swapped = iso swap swap
{-# INLINE swapped #-}

-- | Swap sides of a sum.
--
coswapped :: Iso (a + b) (c + d) (b + a) (d + c)
coswapped = iso eswap eswap
{-# INLINE coswapped #-}

-- | An 'Iso' defined by left-association of nested tuples.
--
associated :: Iso (a , (b , c)) (d , (e , f)) ((a , b) , c) ((d , e) , f)
associated = iso assocl assocr
{-# INLINE associated #-}

-- | An 'Iso' defined by left-association of nested tuples.
--
coassociated :: Iso (a + (b + c)) (d + (e + f)) ((a + b) + c) ((d + e) + f)
coassociated = iso eassocl eassocr
{-# INLINE coassociated #-}

-- | Excise a single value from a type.
--
-- >>> review (excised "foo") "foo"
-- Nothing
-- >>> review (excised "foo") "foobar"
-- Just "foobar"
--
excised :: Eq a => a -> Iso' (Maybe a) a
excised a = iso (fromMaybe a) g
  where g a1 | a1 == a = Nothing
             | otherwise = Just a1
{-# INLINE excised #-}

-- | Flip two arguments of a function.
--
-- >>> (view flipped (,)) 1 2
-- (2,1)
--
flipped :: Iso (a -> b -> c) (d -> e -> f) (b -> a -> c) (e -> d -> f)
flipped = iso flip flip
{-# INLINE flipped #-}

-- | An 'Iso' defined by a function that is its own inverse.
--
-- @
-- 'involuted' ≡ 'Control.Monad.join' 'iso'
-- @
--
-- >>> "live" ^. involuted reverse
-- "evil"
--
-- >>> "live" & involuted reverse ..~ ('d':) 
-- "lived"
--
involuted :: (s -> a) -> Iso s a a s
involuted = M.join iso
{-# INLINE involuted #-}

-- | Uncurry a function.
--
-- >>> (fst ^. invert uncurried) 3 4
-- 3
--
uncurried :: Iso (a -> b -> c) (d -> e -> f) ((a , b) -> c) ((d , e) -> f)
uncurried = iso uncurry curry
{-# INLINE uncurried #-}

-- | An 'Iso' between strict & lazy variants of a sequence.
--
strict :: LazySequence l s => Iso' l s
strict = iso S.toStrict S.fromStrict
{-# INLINE strict #-}

-- | TODO: Document
--
chunked :: LazySequence l s => Iso' l [s]
chunked = iso S.toChunks S.fromChunks
{-# INLINE chunked #-}

-- | TODO: Document
--
unpacked :: IsSequence s => Iso' s [Element s]
unpacked = iso S.unpack S.pack 
{-# INLINE unpacked #-}

-- | Reverse a sequence.
--
reversed :: IsSequence s => Iso' s s
reversed = iso S.reverse S.reverse
{-# INLINE reversed #-}

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- | Based on /ala/ from Conor McBride's work on Epigram.
--
-- This version is generalized to accept any 'Iso', not just a @newtype@.
--
-- >>> au (rewrapped' Sum) foldMap [1,2,3,4]
-- 10
--
-- You may want to think of this combinator as having the following, simpler type:
--
-- @
-- 'au' :: 'AIso' s t a b -> ((b -> t) -> e -> s) -> e -> a
-- @
--
au :: Functor f => AIso s t a b -> ((b -> t) -> f s) -> f a
au k = withIso k $ \ sa bt f -> fmap sa (f bt)
{-# INLINE au #-}

-- | Variant of 'au' for profunctors. 
--
-- @
-- 'flip' 'aup' 'runStar' :: Functor f => AIso s t a (f a) -> Star f c s -> c -> t
-- @
--
aup :: Profunctor p => Functor f => AIso s t a b -> (p c a -> f b) -> p c s -> f t
aup o = withIso o $ \sa bt f g -> fmap bt (f (rmap sa g))
{-# INLINE aup #-}

-- | This combinator is based on @ala@ from Conor McBride's work on Epigram.
--
-- As with 'rewrapped'', the user supplied function for the newtype is /ignored/.
--
-- >>> ala Sum foldMap [1,2,3,4]
-- 10
-- >>> ala All foldMap [True,True]
-- True
-- >>> ala All foldMap [True,False]
-- False
-- >>> ala Any foldMap [False,False]
-- False
-- >>> ala Any foldMap [True,False]
-- True
-- >>> ala Product foldMap [1,2,3,4]
-- 24
--
-- @
-- 'ala' :: 'Newtype' s => 'Newtype' t => ('O' s -> s) -> (('O' t -> t) -> e -> s) -> e -> O s
-- @
--
ala :: Newtype s => Newtype t => Functor f => (O s -> s) -> ((O t -> t) -> f s) -> f (O s) 
ala = au . rewrapped'
{-# INLINE ala #-}

-- | Given a conversion on one side of an 'Iso', recover the other.
--
-- @
-- 'reover' ≡ 'over' '.' 're'
-- @
--
-- Compare 'Data.Profunctor.Optic.Setter.over'.
--
reover :: AIso s t a b -> (t -> s) -> b -> a
reover o = withIso o $ \sa bt ts -> sa . ts . bt
{-# INLINE reover #-}

-- | Remap the indices of an indexed optic.
--
reixes :: Profunctor p => AIso' k1 k2 -> Ixoptic p k1 s t a b -> Ixoptic p k2 s t a b
reixes o = withIso o reix
{-# INLINE reixes #-}

-- | Remap the indices of a coindexed optic.
--
recxes :: Profunctor p => AIso' k1 k2 -> Cxoptic p k1 s t a b -> Cxoptic p k2 s t a b
recxes o = withIso o recx
{-# INLINE recxes #-}
