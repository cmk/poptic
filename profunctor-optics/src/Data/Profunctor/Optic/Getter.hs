module Data.Profunctor.Optic.Getter where

import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Prelude
import Data.Profunctor.Optic.Prism (_Just)
import Control.Monad.Reader as Reader
import Control.Monad.Writer as Writer hiding (Sum(..))
import Control.Monad.State as State hiding (StateT(..))
import Control.Monad.Trans.State.Strict (StateT(..))


---------------------------------------------------------------------
-- 'Getter'
---------------------------------------------------------------------

-- | Build a 'Getter' from an arbitrary function.
--
-- @
-- 'to' f '.' 'to' g ≡ 'to' (g '.' f)
-- @
--
-- @
-- a '^.' 'to' f ≡ f a
-- @
--
-- >>> ("hello","world") ^. to snd
-- "world"
--
-- >>> 5 ^. to succ
-- 6
--
-- >>> (0, -5) ^. _2 . to abs
-- 5
--
-- @
-- 'to' :: (s -> a) -> 'Getter' s a
-- @
--
to :: (s -> a) -> PrimGetter s t a b
to f = rcoerce . lmap f
{-# INLINE to #-}

-- @
-- 'get' :: 'AGetter' s a -> 'Getter' s a
-- 'get' :: 'Monoid' a => 'AGetter' s a -> 'Fold' s a
-- @
get :: AGetter s a -> PrimGetter s t a b
get = to . view

-- @
-- 'toBoth' :: 'AGetter' s a -> 'AGetter' s b -> 'Getter' s (a, b)
-- @
toBoth :: AGetter s a1 -> AGetter s a2 -> PrimGetter s t (a1 , a2) b
toBoth l r = to (view l &&& view r)

-- | TODO: Document
--
toEither :: AGetter s1 a -> AGetter s2 a -> PrimGetter (s1 + s2) t a b
toEither l r = to (view l ||| view r)

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

-- | Map each part of a structure viewed through a 'Lens', 'Getter',
-- 'Fold' or 'Traversal' to a monoid and combine the results.
--
-- >>> viewOf both id (["foo"], ["bar", "baz"])
-- ["foo","bar","baz"]
--
-- @
-- 'Data.Foldable.foldMap' = 'viewOf' 'folded'
-- @
--
-- @
-- 'viewOf' ≡ 'views'
-- @
--
-- @
-- 'viewOf' ::                  'Iso'' s a        -> (a -> r) -> s -> r
-- 'viewOf' ::                  'Lens'' s a       -> (a -> r) -> s -> r
-- 'viewOf' :: 'Monoid' r    => 'Prism'' s a      -> (a -> r) -> s -> r
-- 'viewOf' :: 'Monoid' r    => 'Traversal'' s a  -> (a -> r) -> s -> r
-- 'viewOf' :: 'Monoid' r    => 'Traversal0'' s a -> (a -> r) -> s -> r
-- 'viewOf' :: 'Semigroup' r => 'Traversal1'' s a -> (a -> r) -> s -> r
-- 'viewOf' :: 'Monoid' r    => 'Fold' s a        -> (a -> r) -> s -> r
-- 'viewOf' :: 'Semigroup' r => 'Fold1' s a       -> (a -> r) -> s -> r
-- 'viewOf' ::                  'AGetter' s a       -> (a -> r) -> s -> r
-- @
--
viewOf :: Optic' (FoldRep r) s a -> (a -> r) -> s -> r
viewOf = between (dstar getConst) (ustar Const)

---------------------------------------------------------------------
-- Common getters
---------------------------------------------------------------------

-- | TODO: Document
--
_1' :: PrimGetter (a , c) (b , c) a b
_1' = to fst

-- | TODO: Document
--
_2' :: PrimGetter (c , a) (c , b) a b
_2' = to snd

-- | Build a constant-valued (index-preserving) 'PrimGetter' from an arbitrary value.
--
-- @
-- 'like' a '.' 'like' b ≡ 'like' b
-- a '^.' 'like' b ≡ b
-- a '^.' 'like' b ≡ a '^.' 'to' ('const' b)
-- @
--
-- This can be useful as a second case 'failing' a 'Fold'
-- e.g. @foo `failing` 'like' 0@
--
like :: a -> PrimGetter s t a b
like = to . const

-- | TODO: Document
--
rcoerced :: Getter a a 
rcoerced = rcoerce

---------------------------------------------------------------------
-- Derived operators
---------------------------------------------------------------------

infixl 8 ^.

-- | TODO: Document
--
(^.) :: s -> AGetter s a -> a
(^.) = flip view

-- ^ @
-- 'view o ≡ foldMapOf o id'
-- @
view :: MonadReader s m => AGetter s a -> m a
view = (`views` id)
{-# INLINE view #-}

-- ^ @
-- 'views o f ≡ foldMapOf o f'
-- @
views :: MonadReader s m => Optic' (FoldRep r) s a -> (a -> r) -> m r
views o f = Reader.asks $ viewOf o f
{-# INLINE views #-}

-- | TODO: Document
--
use :: MonadState s m => AGetter s a -> m a
use o = State.gets (view o)

-- | Extracts the portion of a log that is focused on by a 'Getter'. 
--
-- Given a 'Fold' or a 'Traversal', then a monoidal summary of the parts 
-- of the log that are visited will be returned.
--
-- @
-- 'listening' :: 'MonadWriter' w m             => 'Getter' w u     -> m a -> m (a, u)
-- 'listening' :: 'MonadWriter' w m             => 'Lens'' w u      -> m a -> m (a, u)
-- 'listening' :: 'MonadWriter' w m             => 'Iso'' w u       -> m a -> m (a, u)
-- 'listening' :: ('MonadWriter' w m, 'Monoid' u) => 'Fold' w u       -> m a -> m (a, u)
-- 'listening' :: ('MonadWriter' w m, 'Monoid' u) => 'Traversal'' w u -> m a -> m (a, u)
-- 'listening' :: ('MonadWriter' w m, 'Monoid' u) => 'Prism'' w u     -> m a -> m (a, u)
-- @
listening :: MonadWriter w m => AGetter w u -> m a -> m (a, u)
listening l m = do
  (a, w) <- Writer.listen m
  return (a, view l w)
{-# INLINE listening #-}

-- | TODO: Document
--
listenings :: MonadWriter w m => Optic' (FoldRep v) w u -> (u -> v) -> m a -> m (a, v)
listenings l uv m = do
  (a, w) <- listen m
  return (a, views l uv w)
{-# INLINE listenings #-}

-- ^ @
-- zoom :: Functor m => Lens' ta a -> StateT a m c -> StateT ta m c
-- zoom :: (Monoid c, Applicative m) => Traversal' ta a -> StateT a m c -> StateT ta m c
-- @
zoom :: Functor m => Optic' (Star (Compose m ((,) c))) ta a  -> StateT a m c -> StateT ta m c
zoom l (StateT m) = StateT . zoomOut . l . zoomIn $ m
 where
  zoomIn f = Star (Compose . f)
  zoomOut (Star f) = getCompose . f