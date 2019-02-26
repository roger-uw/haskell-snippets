{- a naive imitation of Text.Parsec -}

module Parsec where

import Control.Arrow
import Control.Monad.Identity
import Control.Monad
import Control.Applicative hiding (many, some)
import Control.Monad.Trans.Class
import Data.Char (isDigit, isAlpha, isAlphaNum)
import Data.List

data Pos = Pos {lineNum :: Int, colNum :: Int} deriving (Eq)

instance Ord Pos where
  (Pos xl xc) <= (Pos yl yc) = (xl < yl) || ((xl == yl) && (xc <= yc))

data ErrorMsg = ErrorMsg Pos String [String]

data Parsing t = Parsing {getPos :: Pos, getRest :: [t]} deriving (Show)

newtype Parsed t a = Parsed {unParsed :: (Either ErrorMsg a, Parsing t)}

newtype ParserT t m a = ParserT {runParserT :: Parsing t -> m (Parsed t a)}

type Parser t a = ParserT t Identity a

type PosUpdate t = Pos -> t -> Pos

instance Show Pos where
  show (Pos l c) = "Line: " ++ show l ++ "  " ++ "Column: " ++ show c

instance Show ErrorMsg where
  show (ErrorMsg pos t tE) = "Error => " ++ show pos ++ "\n" ++
    (if null t then "Unknow error\n" else ("Unexpected " ++ t ++ "\n")) ++ 
    (if null tE then [] else (showExpecting (nub tE) ++ "\n"))
    where showExpecting [x] = "Expecting " ++ x
          showExpecting xs = "Expecting " ++ 
            drop 2 (foldr (\now acc -> ", " ++ now ++ acc) " or " (init xs)) ++ last xs

instance (Show a, Show t) => Show (Parsed t a) where
  show (Parsed (result, parsing)) =
    case result of
      Left err -> show err ++ show parsing
      Right a -> "Successfully parsed => " ++ show (getPos parsing) ++ "\n" ++ show a ++ "\n" ++ show parsing

instance (Functor m) => Functor (ParserT t m) where
  fmap f (ParserT p) = ParserT $ \s -> (Parsed . first (f <$>) . unParsed) <$> p s

instance (Monad m) => Applicative (ParserT t m) where
  pure = return
  (<*>) = ap

instance (Monad m) => Monad (ParserT t m) where
  return a = ParserT $ \s -> return (Parsed (Right a, s))
  ParserT x >>= f = ParserT $ \s0 -> do
    Parsed (r, s1) <- x s0
    case r of
      Left err -> return (Parsed (Left err, s1))
      Right a -> runParserT (f a) s1

instance MonadTrans (ParserT t) where
  lift m = ParserT $ \s -> do
    a <- m
    return (Parsed (Right a, s))

instance (Monad m) => Alternative (ParserT t m) where
  empty = mzero
  (<|>) = mplus

mergeErrorMsg _ _ (ErrorMsg _ "" []) eq = eq
mergeErrorMsg _ _ ep (ErrorMsg _ "" []) = ep
mergeErrorMsg psp psq (ep @ (ErrorMsg pep tep etep)) (eq @ (ErrorMsg peq teq eteq)) = 
  case psp == psq of
    True
      | pep == peq -> ErrorMsg peq teq (etep ++ eteq)
      | pep > peq -> ep
      | otherwise -> eq
    _ -> eq

instance (Monad m) => MonadPlus (ParserT t m) where
  mzero = ParserT $ \s -> return (Parsed (Left (ErrorMsg (getPos s) "" []), s))
  mplus (ParserT p) (ParserT q) = ParserT $ \s -> do
    k @ (Parsed (rp, sp)) <- p s
    case rp of
      Left ep -> 
        if getPos s == getPos sp then
          do g @ (Parsed (rq, sq)) <- q s
             case rq of
              Left eq -> return (Parsed (Left (mergeErrorMsg (getPos sp) (getPos sq) ep eq), sq))
              Right _ -> return g
        else return k
      Right _ -> return k

parse p s = runIdentity $ runParserT p (Parsing (Pos 0 0) s)

unexpected :: (Monad m) => String -> ParserT t m a
unexpected err = ParserT $ \s -> return (Parsed (Left (ErrorMsg (getPos s) err []), s))

eof :: (Monad m, Show t) => ParserT t m ()
eof = ParserT $ \s @ (Parsing n xs) ->
  case xs of
    [] -> runParserT (return ()) s
    (x : rest) -> runParserT (unexpected (show x) <?> "end of input") s

getPosition :: (Monad m) => ParserT t m Pos
getPosition = ParserT $ \s @ (Parsing n xs) -> return (Parsed (Right n, s))

label :: (Monad m) => ParserT t m a -> String -> ParserT t m a
label (ParserT p) msg = 
  let modifyExpecting (ErrorMsg pos t tE) tE' = ErrorMsg pos t [tE']
  in ParserT $ \s -> do
      k @ (Parsed (rp, sp)) <- p s
      case rp of
        Left ep -> 
          if getPos s == getPos sp then
            return (Parsed (Left (modifyExpecting ep msg), sp))
          else return k
        Right _ -> return k

infix 0 <?>
(<?>) :: (Monad m) => ParserT t m a -> String -> ParserT t m a
p <?> msg = label p msg

item :: (Monad m) => (t -> String) -> (t -> Maybe a) -> PosUpdate t -> ParserT t m a
item showToken f u = ParserT $ \s @ (Parsing n xs) -> return $
  case xs of
    [] -> Parsed (Left (ErrorMsg n "end of input" []), s)
    (x : rest) -> 
      case f x of
        Nothing -> Parsed (Left (ErrorMsg n (showToken x) []), s)
        Just a -> Parsed (Right a, Parsing (u n x) rest)

try :: (Monad m) => ParserT t m a -> ParserT t m a
try (ParserT p) = ParserT $ \s0 -> do
  k @ (Parsed (r, _)) <- p s0
  case r of
    Left err -> return (Parsed (Left err, s0))
    Right _ -> return k

lookAhead :: (Monad m) => ParserT t m a -> ParserT t m a
lookAhead (ParserT p) = ParserT $ \s0 -> do
  k @ (Parsed (r, _)) <- p s0
  case r of
    Left _ -> return k
    Right a -> return (Parsed (r, s0))

peek :: (Monad m) => ParserT t m a -> ParserT t m a
peek (ParserT p) = ParserT $ \s0 -> do
  k @ (Parsed (r, _)) <- p s0
  case r of
    Left (ErrorMsg _ at atE) -> return (Parsed (Left (ErrorMsg (getPos s0) at atE), s0))
    Right a -> return (Parsed (r, s0))

choice :: (Monad m) => [ParserT t m a] -> ParserT t m a
choice = foldr (<|>) mzero

manyOp :: (Monad m) => (a -> [a] -> [a]) -> ParserT t m a -> ParserT t m [a]
manyOp f p = manyP
  where someP = liftA2 f p manyP
        manyP = someP <|> pure []

someOp :: (Monad m) => (a -> [a] -> [a]) -> ParserT t m a -> ParserT t m [a]
someOp f p = someP
  where someP = liftA2 f p manyP
        manyP = someP <|> pure []

many :: (Monad m) => ParserT t m a -> ParserT t m [a]
many = manyOp (:)

some :: (Monad m) => ParserT t m a -> ParserT t m [a]
some = someOp (:)

skipMany :: (Monad m) => ParserT t m a -> ParserT t m [a]
skipMany = manyOp (const (const []))

skipSome :: (Monad m) => ParserT t m a -> ParserT t m [a]
skipSome = someOp (const (const []))

someSepBy :: (Monad m) => ParserT t m a -> ParserT t m sep -> ParserT t m [a]
someSepBy a sep = liftA2 (:) a (many (sep >> a))

manySepBy :: (Monad m) => ParserT t m a -> ParserT t m sep -> ParserT t m [a]
manySepBy a sep = someSepBy a sep <|> pure []

manyTill :: (Monad m) => ParserT t m a -> ParserT t m end -> ParserT t m [a]
manyTill p end = (end >> return []) <|> liftA2 (:) p (manyTill p end)

followedBy :: (Monad m) => ParserT t m a -> ParserT t m b -> ParserT t m a
followedBy a b = do
  x <- a
  lookAhead (try b)
  return x

notFollowedBy :: (Monad m, Show b) => ParserT t m a -> ParserT t m b -> ParserT t m a
notFollowedBy a b = do
  x <- a
  peek $ (do 
    y <- try b
    unexpected (show y)) <|> return ()
  return x

posUpdateChar :: PosUpdate Char
posUpdateChar (Pos l c) x
  | x == '\n' = Pos (l + 1) 0
  | otherwise = Pos l (c + 1)

satisfy :: (Monad m) => (Char -> Bool) -> ParserT Char m Char
satisfy f = item show (\x -> if f x then Just x else Nothing) posUpdateChar

oneOf :: (Monad m) => String -> ParserT Char m Char
oneOf s = satisfy (\x -> x `elem` s)

noneOf :: (Monad m) => String -> ParserT Char m Char
noneOf s = satisfy (\x -> not (x `elem` s))

char :: (Monad m) => Char -> ParserT Char m Char
char x = satisfy (== x) <?> show x

anyChar :: (Monad m) => ParserT Char m Char
anyChar = satisfy (const True)

space :: (Monad m) => ParserT Char m Char
space = char ' ' <?> "space"

whitespace :: (Monad m) => ParserT Char m Char
whitespace = oneOf " \t\n" <?> "whitespace character"

spaces :: (Monad m) => ParserT Char m String
spaces = skipMany space

whitespaces :: (Monad m) => ParserT Char m String
whitespaces = skipMany whitespace

digit :: (Monad m) => ParserT Char m Char
digit = satisfy isDigit <?> "digit"

letter :: (Monad m) => ParserT Char m Char
letter = satisfy isAlpha <?> "letter"

alphaNum :: (Monad m) => ParserT Char m Char
alphaNum = satisfy isAlphaNum <?> "letter or digit"

string :: (Monad m) => String -> ParserT Char m String
string s = mapM char s <?> ("\"" ++ s ++ "\"")

clean :: (Monad m) => ParserT Char m a -> ParserT Char m a
clean p = do
  x <- p
  whitespaces
  return x
