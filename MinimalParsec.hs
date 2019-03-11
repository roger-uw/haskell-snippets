{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}

module MinimalParsec where

import Data.Either
import Data.Monoid
import Control.Arrow
import Control.Monad
import Control.Applicative
import Control.Monad.Trans
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Except
import Control.Monad.Identity
import qualified Control.Monad.Fail as Fail

-- | Stream of tokens
class Stream s t | s -> t where
  uncons :: s -> Maybe (t, s)

instance Stream [a] a where
  uncons [] = Nothing
  uncons (x : xs) = Just (x, xs)

-- | Backtracking Parser
-- @s -> m (a, s)@
newtype BTParsecT s m a = BTParsecT (StateT s m a)
  deriving (Functor, Applicative, Monad, MonadTrans, MonadPlus, Alternative, Fail.MonadFail, MonadState s)

runBTParsecT :: BTParsecT s m a -> s -> m (a, s)
runBTParsecT (BTParsecT p) = runStateT p

evalBTParsecT :: (Monad m) => BTParsecT s m a -> s -> m a
evalBTParsecT p = fmap fst . runBTParsecT p

itemBT :: (Fail.MonadFail m, Stream s t) => (t -> Maybe a) -> BTParsecT s m a
itemBT f = do
  s <- get
  case uncons s of
    Nothing -> Fail.fail "unexpected end of input"
    Just (t, s') -> case f t of
      Nothing -> Fail.fail "mismatched token"
      Just a -> put s' >> return a

eofBT :: (Fail.MonadFail m, Stream s t) => BTParsecT s m ()
eofBT = do
  s <- get
  case uncons s of
    Nothing -> return ()
    _ -> Fail.fail "unexpected token"

-- | Predictive Parser
-- @s -> m (Either String (a, s), Any)@
-- 
-- Reference: LEIJEN, D., AND MEIJER, E. Parsec: Direct style monadic parser combinators for the real world. Tech. rep., July 2001.
newtype PDParsecT s m a = PDParsecT (StateT s (ExceptT String (WriterT Any m)) a)
  deriving (Functor, Applicative, Monad, MonadState s, MonadWriter Any)

runPDParsecT :: PDParsecT s m a -> s -> m (Either String (a, s), Any)
runPDParsecT (PDParsecT p) = runWriterT . runExceptT . runStateT p 

evalPDParsecT :: (Monad m) => PDParsecT s m a -> s -> m (Either String a)
evalPDParsecT p = fmap (either (Left . id) (Right . fst) . fst) . runPDParsecT p

isConsumed = getAny . snd
isFailed = isLeft . fst
isSucc = isRight . fst

instance (Monad m) => Alternative (PDParsecT s m) where
  empty = PDParsecT empty
  pA <|> pB = PDParsecT . StateT $ \s -> ExceptT . WriterT $ do
    rA <- runPDParsecT pA s
    if isConsumed rA then return rA else do
      rB <- runPDParsecT pB s
      return $ if | isConsumed rB -> rB
                  | isSucc rA -> rA
                  | otherwise -> case fst rB of {Left "" -> rA; _ -> rB}

instance (Monad m) => MonadPlus (PDParsecT s m) where
  mzero = empty
  mplus = (<|>)
  
instance (Monad m) => Fail.MonadFail (PDParsecT s m) where
  fail = PDParsecT . StateT . const . ExceptT . return . Left

instance MonadTrans (PDParsecT s) where
  lift m = PDParsecT . StateT $ \s -> ExceptT . WriterT $ do
    a <- m
    return (Right (a, s), mempty)

itemPD :: (Monad m, Stream s t) => (t -> Maybe a) -> PDParsecT s m a
itemPD f = do
  s <- get
  case uncons s of
    Nothing -> Fail.fail "unexpected end of input"
    Just (t, s') -> case f t of
      Nothing -> Fail.fail "mismatched token"
      Just a -> put s' >> tell (Any True) >> return a

tryPD :: (Monad m) => PDParsecT s m a -> PDParsecT s m a
tryPD p = PDParsecT . StateT $ \s -> ExceptT . WriterT $ do
  r @ (e, consumed) <- runPDParsecT p s
  return (if getAny consumed && isLeft e then (e, Any False) else r)

eofPD :: (Monad m, Stream s t) => PDParsecT s m ()
eofPD = do
  s <- get
  case uncons s of
    Nothing -> return ()
    _ -> Fail.fail "unexpected token"

-- | Sample parser combinators
charBT :: (Fail.MonadFail m, Stream s Char) => Char -> BTParsecT s m Char
charBT c = itemBT (\t -> if t == c then Just c else Nothing)

charPD :: (Monad m, Stream s Char) => Char -> PDParsecT s m Char
charPD c = itemPD (\t -> if t == c then Just c else Nothing)

stringBT :: (Fail.MonadFail m, Stream s Char) => String -> BTParsecT s m String
stringBT = mapM charBT

stringPD :: (Monad m, Stream s Char) => String -> PDParsecT s m String
stringPD = mapM charPD

testBT :: BTParsecT String Maybe String
testBT = stringBT "abc" <|> stringBT "abd" <|> stringBT "xyz"

testPD :: PDParsecT String Identity String
testPD = stringPD "abc" <|> stringPD "abd" <|> stringPD "xyz"