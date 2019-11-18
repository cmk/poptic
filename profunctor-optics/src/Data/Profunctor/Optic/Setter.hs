{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Optic.Setter (
    -- * Types
    Setter
  , Setter'
  , ASetter
  , ASetter'
  , Resetter
  , Resetter'
  , AResetter
  , AResetter'
    -- * Constructors
  , setter
  , ixsetter
  , resetter
  , cxsetter
  , closing
  , toSemiring
  , fromSemiring
    -- * Primitive operators
  , over
  , ixover
  , under
  , cxover
    -- * Common optics
  , zero
  , one
  , (<~>)
  , cod
  , dom
  , bound 
  , fmapped
  , contramapped
  , foldMapped
  , liftedA
  , liftedM
  , locally
  , zipped
  , modded
  , branched
  , reviewed
  , composed
  , exmapped
    -- * Derived operators
  , assignA
  , set
  , ixset
  , reset
  , cxset
  , (.~)
  , (..~)
  , (@~)
  , (@@~)
  , (/~)
  , (//~)
  , (#~)
  , (##~)
  , (?~)
  , (<>~)
  , (><~)
  , (+~)
  , (*~)
  , (-~)
  , (||~)
  , (&&~)
) where

import Control.Applicative (liftA)
import Control.Exception (Exception(..))
import Control.Monad.Reader as Reader
import Control.Monad.State as State
import Control.Monad.Writer as Writer
import Data.Foldable (Foldable, foldMap)
import Data.Profunctor.Arrow
import Data.Profunctor.Optic.Import hiding ((&&&))
import Data.Profunctor.Optic.Indexed (Index(..), Coindex(..), trivial)
import Data.Profunctor.Optic.Repn
import Data.Profunctor.Optic.Type
import Data.Semiring
import Prelude (Num(..))
import qualified Control.Exception as Ex

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> :set -XRankNTypes
-- >>> import Control.Category ((>>>))
-- >>> import Control.Arrow (Kleisli(..))
-- >>> import Control.Exception
-- >>> import Control.Monad.State
-- >>> import Control.Monad.Reader
-- >>> import Control.Monad.Writer
-- >>> import Data.Functor.Identity
-- >>> import Data.Functor.Contravariant
-- >>> import Data.List.Index
-- >>> :load Data.Profunctor.Optic
-- >>> let catchOn :: Int -> Cxprism' Int (Maybe String) String ; catchOn n = cxjust $ \k -> if k==n then Just "caught" else Nothing

---------------------------------------------------------------------
-- Setter
---------------------------------------------------------------------

-- | Obtain a 'Setter' from a <http://conal.net/blog/posts/semantic-editor-combinators SEC>.
--
-- To demote an optic to a semantic edit combinator, use the section @(l ..~)@ or @over l@.
--
-- >>> [("The",0),("quick",1),("brown",1),("fox",2)] & setter map . first ..~ length
-- [(3,0),(5,1),(5,1),(3,2)]
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input function satisfies the following
-- properties:
--
-- * @abst id ≡ id@
--
-- * @abst f . abst g ≡ abst (f . g)@
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
setter :: ((a -> b) -> s -> t) -> Setter s t a b
setter abst = dimap (flip Index id) (\(Index s ab) -> abst ab s) . repn collect
{-# INLINE setter #-}

-- | Build an 'Ixsetter' from an indexed function.
--
-- @
-- 'ixsetter' '.' 'ixover' ≡ 'id'
-- 'ixover' '.' 'ixsetter' ≡ 'id'
-- @
--
-- Your supplied function @f@ is required to satisfy:
--
-- @
-- f 'id' ≡ 'id'
-- f g '.' f h ≡ f (g '.' h)
-- @
--
ixsetter :: ((i -> a -> b) -> s -> t) -> Ixsetter i s t a b
ixsetter f = setter $ \iab -> f (curry iab) . snd 
{-# INLINE ixsetter #-}

-- | Obtain a 'Resetter' from a <http://conal.net/blog/posts/semantic-editor-combinators SEC>.
--
resetter :: ((a -> t) -> s -> t) -> Resetter s t a t
resetter abst = dimap (\s -> Coindex $ \ab -> abst ab s) trivial . corepn (\f -> fmap f . sequenceA)
{-# INLINE resetter #-}

-- | TODO: Document
--
cxsetter :: ((k -> a -> t) -> s -> t) -> Cxsetter k s t a t
cxsetter f = resetter $ \kab -> const . f (flip kab)
{-# INLINE cxsetter #-}

-- | Every valid 'Grate' is a 'Setter'.
--
closing :: (((s -> a) -> b) -> t) -> Setter s t a b
closing sabt = setter $ \ab s -> sabt $ \sa -> ab (sa s)
{-# INLINE closing #-}

-- | Lower a semiring value to its concrete analog.
--
-- @ 
-- 'toSemiring' . 'fromSemiring' ≡ 'id'
-- 'fromSemiring' . 'toSemiring' ≡ 'id'
-- @
--
toSemiring :: Monoid a => Semiring a => Setter' a a -> a
toSemiring a = over a (unit <>) mempty

-- | Lift a semiring value to its double Cayley analog.
--
-- @ 
-- 'toSemiring' . 'fromSemiring' ≡ 'id'
-- 'fromSemiring' . 'toSemiring' ≡ 'id'
-- @
--
fromSemiring :: Monoid a => Semiring a => a -> Setter' a a
fromSemiring a = setter $ \f y -> a >< f mempty <> y

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

-- | Extract a SEC from a 'Setter'.
--
-- Used to modify the target of a 'Lens' or all the targets of a 'Setter' 
-- or 'Traversal'.
--
-- @
-- 'over' o 'id' ≡ 'id' 
-- 'over' o f '.' 'over' o g ≡ 'over' o (f '.' g)
-- 'setter' '.' 'over' ≡ 'id'
-- 'over' '.' 'setter' ≡ 'id'
-- @
--
-- >>> over fmapped (+1) (Just 1)
-- Just 2
--
-- >>> over fmapped (*10) [1,2,3]
-- [10,20,30]
--
-- >>> over first (+1) (1,2)
-- (2,2)
--
-- >>> over first show (10,20)
-- ("10",20)
--
-- @
-- over :: Setter s t a b -> (a -> r) -> s -> r
-- over :: Monoid r => Fold s t a b -> (a -> r) -> s -> r
-- @
--
over :: ASetter s t a b -> (a -> b) -> s -> t
over o = (runIdentity #.) #. runStar #. o .# Star .# (Identity #. ) 
{-# INLINE over #-}

-- >>> ixover (ixat 1) (+) [1,2,3 :: Int]
-- [1,3,3]
--
-- >>> ixover (ixat 5) (+) [1,2,3 :: Int]
-- [1,2,3]
--
ixover :: Monoid i => Ixsetter i s t a b -> (i -> a -> b) -> s -> t
ixover o f = curry (over o (uncurry f)) mempty
{-# INLINE ixover #-}

-- | Extract a SEC from a 'Resetter'.
--
-- @
-- 'under' o 'id' ≡ 'id' 
-- 'under' o f '.' 'under' o g ≡ 'under' o (f '.' g)
-- 'resetter' '.' 'under' ≡ 'id'
-- 'under' '.' 'resetter' ≡ 'id'
-- @
--
-- Note that 'under' (more properly co-/over/) is distinct from 'Data.Profunctor.Optic.Iso.reover':
--
-- >>> :t under $ wrapped @(Identity Int)
-- under $ wrapped @(Identity Int)
--   :: (Int -> Int) -> Identity Int -> Identity Int
-- >>> :t over $ wrapped @(Identity Int)
-- over $ wrapped @(Identity Int)
--   :: (Int -> Int) -> Identity Int -> Identity Int
-- >>> :t over . re $ wrapped @(Identity Int)
-- over . re $ wrapped @(Identity Int)
--   :: (Identity Int -> Identity Int) -> Int -> Int
-- >>> :t reover $ wrapped @(Identity Int)
-- reover $ wrapped @(Identity Int)
--   :: (Identity Int -> Identity Int) -> Int -> Int
--
-- Compare to the /lens-family/ <http://hackage.haskell.org/package/lens-family-2.0.0/docs/Lens-Family2.html#v:under version>.
--
under :: AResetter s t a b -> (a -> b) -> s -> t
under o = (.# Identity) #. runCostar #. o .# Costar .# (.# runIdentity)
{-# INLINE under #-}

-- >>> cxover (catchOn 42) (\k msg -> show k ++ ": " ++ msg) $ Just "foo"
-- Just "0: foo"
--
-- >>> cxover (catchOn 42) (\k msg -> show k ++ ": " ++ msg) Nothing
-- Nothing
--
-- >>> cxover (catchOn 0) (\k msg -> show k ++ ": " ++ msg) Nothing
-- Just "caught"
--
cxover :: Monoid k => Cxsetter k s t a b -> (k -> a -> b) -> s -> t 
cxover o f = flip (under o (flip f)) mempty
{-# INLINE cxover #-}

---------------------------------------------------------------------
-- Optics 
---------------------------------------------------------------------

-- | The zero 'Setter'.
--
-- @
-- 'zero'  .  'one' ≡ 'zero'
-- 'zero' <~> 'one' ≡ 'one'
-- @
--
-- >>> toSemiring $ zero <~> one :: Int
-- 1
-- >>> toSemiring $ zero  .  one :: Int
-- 0
--
zero :: Setter' a a
zero = setter $ const id
{-# INLINE zero #-}

-- | The unit 'Setter'.
--
-- @
-- 'zero'  .  'one' ≡ 'zero'
-- 'zero' <~> 'one' ≡ 'one'
-- @
--
-- >>> toSemiring $ zero <~> one :: Int
-- 1
-- >>> toSemiring $ zero  .  one :: Int
-- 0
--
one :: Setter' a a 
one = setter id
{-# INLINE one #-}

infixl 6 <~>

-- | Sum two monomorphic 'Setter's.
--
(<~>) :: Setter' a a -> Setter' a a -> Setter' a a
(<~>) f g = setter $ \h -> (f ..~ h) . (g ..~ h)
{-# INLINE (<~>) #-}

-- | Map covariantly over the output of a 'Profunctor'.
--
-- The most common profunctor to use this with is @(->)@.
--
-- @
-- (dom ..~ f) g x ≡ f (g x)
-- cod @(->) ≡ 'Data.Profunctor.Optic.Grate.withGrate' 'Data.Profunctor.Closed.closed' 'Data.Profunctor.Optic.Setter.closing'
-- @
--
-- >>> (cod ..~ show) length [1,2,3]
-- "3"
--
cod :: Profunctor p => Setter (p r a) (p r b) a b
cod = setter rmap
{-# INLINE cod #-}

-- | Map contravariantly over the input of a 'Profunctor'.
--
-- The most common profunctor to use this with is @(->)@.
--
-- @
-- (dom ..~ f) g x ≡ g (f x)
-- @
--
-- >>> (dom ..~ show) length [1,2,3]
-- 7
--
dom :: Profunctor p => Setter (p b r) (p a r) a b
dom = setter lmap
{-# INLINE dom #-}

-- | 'Setter' for monadically transforming a monadic value.
--
bound :: Monad m => Setter (m a) (m b) a (m b)
bound = setter (=<<)
{-# INLINE bound #-}

-- | 'Setter' on each value of a functor.
--
fmapped :: Functor f => Setter (f a) (f b) a b
fmapped = setter fmap
{-# INLINE fmapped #-}

-- | This 'Setter' can be used to map over all of the inputs to a 'Contravariant'.
--
-- @
-- 'contramap' ≡ 'over' 'contramapped'
-- @
--
-- >>> getPredicate (over contramapped (*2) (Predicate even)) 5
-- True
--
-- >>> getOp (over contramapped (*5) (Op show)) 100
-- "500"
--
contramapped :: Contravariant f => Setter (f b) (f a) a b
contramapped = setter contramap
{-# INLINE contramapped #-}

-- | TODO: Document
--
foldMapped :: Foldable f => Monoid m => Setter (f a) m a m
foldMapped = setter foldMap
{-# INLINE foldMapped #-}

-- | This 'setter' can be used to modify all of the values in an 'Applicative'.
--
-- @
-- 'liftA' ≡ 'setter' 'liftedA'
-- @
--
-- >>> setter liftedA Identity [1,2,3]
-- [Identity 1,Identity 2,Identity 3]
--
-- >>> set liftedA 2 (Just 1)
-- Just 2
--
liftedA :: Applicative f => Setter (f a) (f b) a b
liftedA = setter liftA
{-# INLINE liftedA #-}

-- | TODO: Document
--
liftedM :: Monad m => Setter (m a) (m b) a b
liftedM = setter liftM
{-# INLINE liftedM #-}

-- | Modify the local environment of a 'Reader'. 
--
-- Use to lift reader actions into a larger environment:
--
-- >>> runReader ( ask & locally ..~ fst ) (1,2)
-- 1
--
locally :: Setter (ReaderT r2 m a) (ReaderT r1 m a) r1 r2
locally = setter withReaderT
{-# INLINE locally #-}

-- | TODO: Document
--
zipped :: Setter (u -> v -> a) (u -> v -> b) a b
zipped = setter ((.)(.)(.))
{-# INLINE zipped #-}

-- | TODO: Document
--
modded :: (a -> Bool) -> Setter' (a -> b) b
modded p = setter $ \mods f a -> if p a then mods (f a) else f a
{-# INLINE modded #-}

-- | Apply a function only when the given predicate holds.
--
-- See also 'Data.Profunctor.Optic.Affine.predicated' & 'Data.Profunctor.Optic.Prism.filtered'.
--
branched :: (a -> Bool) -> Setter' a a
branched p = setter $ \f a -> if p a then f a else a
{-# INLINE branched #-}

-- | TODO: Document
--
reviewed :: Setter (b -> t) (((s -> a) -> b) -> t) s a
reviewed = setter $ \sa bt sab -> bt (sab sa)
{-# INLINE reviewed #-}

-- | TODO: Document
--
composed :: Setter (s -> a) ((a -> b) -> s -> t) b t
composed = setter between
{-# INLINE composed #-}

-- | Map one exception into another as proposed in the paper "A semantics for imprecise exceptions".
--
-- >>> handles (only Overflow) (\_ -> return "caught") $ assert False (return "uncaught") & (exmapped ..~ \ (AssertionFailed _) -> Overflow)
-- "caught"
--
-- @
-- exmapped :: Exception e => Setter s s SomeException e
-- @
--
exmapped :: Exception e1 => Exception e2 => Setter s s e1 e2
exmapped = setter Ex.mapException
{-# INLINE exmapped #-}

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------


-- | Run a profunctor arrow command and set the optic targets to the result.
--
-- Similar to 'assign', except that the type of the object being modified can change.
--
-- >>> getVal1 = Right 3
-- >>> getVal2 = Right False
-- >>> action = assignA first (Kleisli (const getVal1)) >>> assignA second (Kleisli (const getVal2))
-- >>> runKleisli action ((), ())
-- Right (3,False)
--
-- @
-- 'assignA' :: 'Category' p => 'Iso' s t a b       -> 'Lenslike' p s t s b
-- 'assignA' :: 'Category' p => 'Lens' s t a b      -> 'Lenslike' p s t s b
-- 'assignA' :: 'Category' p => 'Grate' s t a b     -> 'Lenslike' p s t s b
-- 'assignA' :: 'Category' p => 'Setter' s t a b    -> 'Lenslike' p s t s b
-- 'assignA' :: 'Category' p => 'Traversal' s t a b -> 'Lenslike' p s t s b
-- @
--
assignA :: Category p => Strong p => ASetter s t a b -> Optic p s t s b 
assignA o p = arr (flip $ set o) &&& p >>> arr (uncurry id)
{-# INLINE assignA #-}

-- | Set all referenced fields to the given value.
--
-- @ 'set' l y ('set' l x a) ≡ 'set' l y a @
--
set :: ASetter s t a b -> b -> s -> t
set o b = over o (const b)
{-# INLINE set #-}

-- | Set with index. Equivalent to 'ixover' with the current value ignored.
--
-- When you do not need access to the index, then 'set' is more liberal in what it can accept.
--
-- @
-- 'set' o ≡ 'ixset' o '.' 'const'
-- @
--
-- >>> ixset (ixat 2) (2-) [1,2,3 :: Int]
-- [1,2,0]
--
-- >>> ixset (ixat 5) (const 0) [1,2,3 :: Int]
-- [1,2,3]
--
ixset :: Monoid i => Ixsetter i s t a b -> (i -> b) -> s -> t
ixset o = ixover o . (const .)
{-# INLINE ixset #-}

-- | Set all referenced fields to the given value.
--
-- @
-- 'reset' ≡ 'set' '.' 're'
-- @
-- 
reset :: AResetter s t a b -> b -> s -> t
reset o b = under o (const b)
{-# INLINE reset #-}

-- | Dual set with index. Equivalent to 'cxover' with the current value ignored.
--
-- >>> cxset (catchOn 42) show $ Just "foo"
-- Just "0"
--
-- >>> cxset (catchOn 42) show Nothing
-- Nothing
--
-- >>> cxset (catchOn 0) show Nothing
-- Just "caught"
--
cxset :: Monoid k => Cxsetter k s t a b -> (k -> b) -> s -> t 
cxset o kb = cxover o $ flip (const kb)
{-# INLINE cxset #-}

infixr 4 .~, ..~

-- | TODO: Document
--
(.~) :: ASetter s t a b -> b -> s -> t
(.~) = set
{-# INLINE (.~) #-}

-- | TODO: Document
--
-- >>> Nothing & just ..~ (+1)
-- Nothing
--
(..~) :: ASetter s t a b -> (a -> b) -> s -> t
(..~) = over
{-# INLINE (..~) #-}

infixr 4 @~, @@~ 

-- | An infix variant of 'ixset'. Dual to '#~'.
--
(@~) :: Monoid i => Ixsetter i s t a b -> (i -> b) -> s -> t
(@~) = ixset
{-# INLINE (@~) #-}

-- | An infix variant of 'ixover'. Dual to '##~'.
--
(@@~) :: Monoid i => Ixsetter i s t a b -> (i -> a -> b) -> s -> t
(@@~) = ixover
{-# INLINE (@@~) #-}

infixr 4 /~, //~

-- | An infix variant of 'reset'. Dual to '.~'.
--
(/~) :: AResetter s t a b -> b -> s -> t
(/~) = reset
{-# INLINE (/~) #-}

-- | An infix variant of 'under'. Dual to '..~'.
--
(//~) :: AResetter s t a b -> (a -> b) -> s -> t
(//~) = under
{-# INLINE (//~) #-}

infixr 4 #~, ##~

-- | An infix variant of 'cxset'. Dual to '@~'.
--
(#~) :: Monoid k => Cxsetter k s t a b -> (k -> b) -> s -> t 
(#~) = cxset
{-# INLINE (#~) #-}

-- | An infix variant of 'cxover'. Dual to '@@~'.
--
-- >>> Just "foo" & catchOn 0 ##~ (\k msg -> show k ++ ": " ++ msg)
-- Just "0: foo"
--
-- >>> Nothing & catchOn 0 ##~ (\k msg -> show k ++ ": " ++ msg)
-- Just "caught"
--
(##~) :: Monoid k => Cxsetter k s t a b -> (k -> a -> b) -> s -> t 
(##~) = cxover
{-# INLINE (##~) #-}

infixr 4 ?~

-- | Set the target of a settable optic to 'Just' a value.
--
-- @
-- l '?~' t ≡ 'set' l ('Just' t)
-- @
--
-- >>> Nothing & id ?~ 1
-- Just 1
--
-- '?~' can be used type-changily:
--
-- >>> ('a', ('b', 'c')) & second . both ?~ 'x'
-- ('a',(Just 'x',Just 'x'))
--
-- @
-- ('?~') :: 'Iso' s t a ('Maybe' b)       -> b -> s -> t
-- ('?~') :: 'Lens' s t a ('Maybe' b)      -> b -> s -> t
-- ('?~') :: 'Grate' s t a ('Maybe' b)     -> b -> s -> t
-- ('?~') :: 'Setter' s t a ('Maybe' b)    -> b -> s -> t
-- ('?~') :: 'Traversal' s t a ('Maybe' b) -> b -> s -> t
-- @
--
(?~) :: ASetter s t a (Maybe b) -> b -> s -> t
o ?~ b = set o (Just b)
{-# INLINE (?~) #-}

infixr 4 <>~

-- | Modify the target by adding another value.
--
-- >>> both <>~ False $ (False,True)
-- (False,True)
--
-- >>> both <>~ "!!!" $ ("hello","world")
-- ("hello!!!","world!!!")
--
-- @
-- ('<>~') :: 'Semigroup' a => 'Iso' s t a a       -> a -> s -> t
-- ('<>~') :: 'Semigroup' a => 'Lens' s t a a      -> a -> s -> t
-- ('<>~') :: 'Semigroup' a => 'Grate' s t a a     -> a -> s -> t
-- ('<>~') :: 'Semigroup' a => 'Setter' s t a a    -> a -> s -> t
-- ('<>~') :: 'Semigroup' a => 'Traversal' s t a a -> a -> s -> t
-- @
--
(<>~) :: Semigroup a => ASetter s t a a -> a -> s -> t
l <>~ n = over l (<> n)
{-# INLINE (<>~) #-}

infixr 4 ><~

-- | Modify the target by multiplying by another value.
--
-- >>> both ><~ False $ (False,True)
-- (False,False)
--
-- @
-- ('><~') :: 'Semiring' a => 'Iso' s t a a       -> a -> s -> t
-- ('><~') :: 'Semiring' a => 'Lens' s t a a      -> a -> s -> t
-- ('><~') :: 'Semiring' a => 'Grate' s t a a     -> a -> s -> t
-- ('><~') :: 'Semiring' a => 'Setter' s t a a    -> a -> s -> t
-- ('><~') :: 'Semiring' a => 'Traversal' s t a a -> a -> s -> t
-- @
--
(><~) :: Semiring a => ASetter s t a a -> a -> s -> t
l ><~ n = over l (>< n)
{-# INLINE (><~) #-}

infixr 4 +~

-- | Increment the target(s) of a numerically valued 'Lens', 'Setter' or 'Traversal'.
--
-- >>> (1,2) & second +~ 1
-- (1,3)
--
-- >>> [(1,2),(3,4)] & traversed . both +~ 5
-- [(6,7),(8,9)]
--
-- @
-- ('+~') :: 'Num' a => 'Iso'' s a       -> a -> s -> s
-- ('+~') :: 'Num' a => 'Lens'' s a      -> a -> s -> s
-- ('+~') :: 'Num' a => 'Grate'' s a     -> a -> s -> s
-- ('+~') :: 'Num' a => 'Setter'' s a    -> a -> s -> s
-- ('+~') :: 'Num' a => 'Traversal'' s a -> a -> s -> s
-- @
--
(+~) :: Num a => ASetter s t a a -> a -> s -> t
l +~ n = over l (+ n)
{-# INLINE (+~) #-}

infixr 4 *~

-- | Multiply the target(s) of a numerically valued 'Lens', 'Iso', 'Setter' or 'Traversal'.
--
-- >>> (1,2) & second *~ 4
-- (1,8)
--
-- >>> Just 24 & fmapped *~ 2
-- Just 48
--
-- @
-- ('*~') :: 'Num' a => 'Iso'' s a       -> a -> s -> s
-- ('*~') :: 'Num' a => 'Lens'' s a      -> a -> s -> s
-- ('*~') :: 'Num' a => 'Grate'' s a     -> a -> s -> s
-- ('*~') :: 'Num' a => 'Setter'' s a    -> a -> s -> s
-- ('*~') :: 'Num' a => 'Traversal'' s a -> a -> s -> s
-- @
(*~) :: Num a => ASetter s t a a -> a -> s -> t
l *~ n = over l (* n)
{-# INLINE (*~) #-}

infixr 4 -~

-- | Decrement the target(s) of a numerically valued 'Lens', 'Iso', 'Setter' or 'Traversal'.
--
-- >>> first -~ 2 $ (1,2)
-- (-1,2)
--
-- >>> fmapped . fmapped -~ 1 $ [[4,5],[6,7]]
-- [[3,4],[5,6]]
--
-- @
-- ('-~') :: 'Num' a => 'Iso'' s a       -> a -> s -> s
-- ('-~') :: 'Num' a => 'Lens'' s a      -> a -> s -> s
-- ('-~') :: 'Num' a => 'Grate'' s a     -> a -> s -> s
-- ('-~') :: 'Num' a => 'Setter'' s a    -> a -> s -> s
-- ('-~') :: 'Num' a => 'Traversal'' s a -> a -> s -> s
-- @
(-~) :: Num a => ASetter s t a a -> a -> s -> t
l -~ n = over l (subtract n)
{-# INLINE (-~) #-}

infixr 4 ||~

-- | Logically '||' the target(s) of a 'Bool'-valued 'Lens' or 'Setter'.
--
-- >>> both ||~ True $ (False,True)
-- (True,True)
--
-- >>> both ||~ False $ (False,True)
-- (False,True)
--
-- @
-- ('||~') :: 'Iso'' s 'Bool'       -> 'Bool' -> s -> s
-- ('||~') :: 'Lens'' s 'Bool'      -> 'Bool' -> s -> s
-- ('||~') :: 'Grate'' s 'Bool'     -> 'Bool' -> s -> s
-- ('||~') :: 'Setter'' s 'Bool'    -> 'Bool' -> s -> s
-- ('||~') :: 'Traversal'' s 'Bool' -> 'Bool' -> s -> s
-- @
(||~):: ASetter s t Bool Bool -> Bool -> s -> t
l ||~ n = over l (|| n)
{-# INLINE (||~) #-}

infixr 4 &&~

-- | Logically '&&' the target(s) of a 'Bool'-valued 'Lens' or 'Setter'.
--
-- >>> both &&~ True $ (False, True)
-- (False,True)
--
-- >>> both &&~ False $ (False, True)
-- (False,False)
--
-- @
-- ('&&~') :: 'Iso'' s 'Bool'       -> 'Bool' -> s -> s
-- ('&&~') :: 'Lens'' s 'Bool'      -> 'Bool' -> s -> s
-- ('&&~') :: 'Grate'' s 'Bool'     -> 'Bool' -> s -> s
-- ('&&~') :: 'Setter'' s 'Bool'    -> 'Bool' -> s -> s
-- ('&&~') :: 'Traversal'' s 'Bool' -> 'Bool' -> s -> s
-- @
(&&~) :: ASetter s t Bool Bool -> Bool -> s -> t
l &&~ n = over l (&& n)
{-# INLINE (&&~) #-}
