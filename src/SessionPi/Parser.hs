module SessionPi.Parser where

import Data.Void (Void)
import Data.Text (Text, pack)

import Control.Monad (void, join)

import Text.Megaparsec (Parsec, choice, some, MonadParsec (notFollowedBy), try, empty, (<|>), between, parse)
import qualified Text.Megaparsec.Error as E
import qualified Text.Megaparsec.Char as C
import qualified Text.Megaparsec.Char.Lexer as L

import SessionPi.Language (Proc (Snd, Rec, Par, Brn, Nil, Bnd), Val (Var, Lit))

-- Parser :: * -> *
type Parser = Parsec
    Void -- No custom errors
    Text -- Parse Text

parseProcess :: String -> String -> Either (E.ParseErrorBundle Text Void) Proc
parseProcess fileName content = parse process fileName (pack content)

symbols :: [Text]
symbols =
    [ "<<"  -- send operator
    , ">>"  -- receive operator
    , "><"  -- declare and bind channels operator
    , "."   -- action operator
    , "|"   -- parallel composition operator
    ]

keywords :: [Text]
keywords =
    [ "if"
    , "then"
    , "else"
    , "0"
    , "true"
    , "false"
    ]


process :: Parser Proc
process = processExpr

processLeaves :: [Parser Proc]
processLeaves =
    [ inaction
    , send
    , receive
    , branch
    , bind
    , betweenCurly process
    ]

processExpr :: Parser Proc
processExpr = do
    p1 <- parseLeaf
    do
        symbol "|"
        Par p1 <$> processExpr
        <|>
        return p1

parseLeaf :: Parser Proc
parseLeaf = choice $ try <$> processLeaves

send :: Parser Proc
send = do
    chn <- variable
    symbol "<<"
    val <- value
    symbol "."
    Snd chn val <$> process

receive :: Parser Proc
receive = do
    chn <- variable
    symbol ">>"
    var <- variable
    symbol "."
    Rec chn var <$> process

branch :: Parser Proc
branch = do
    keyword "if"
    guard <- value
    keyword "then"
    p1 <- process
    keyword "else"
    Brn guard p1 <$> process

inaction :: Parser Proc
inaction = do
    keyword "0"
    return Nil

bind :: Parser Proc
bind = do
    ch1 <- variable
    symbol "><"
    ch2 <- variable
    symbol "."
    Bnd ch1 ch2 <$> process

value :: Parser Val
value = choice $ try <$>
    [ Lit <$> literal
    , Var <$> variable
    ]

literal :: Parser Bool
literal = choice
    [ True  <$ keyword "true"
    , False <$ keyword "false"
    ]

anyKeyword :: Parser ()
anyKeyword = choice $ keyword <$> keywords

variable :: Parser String
variable = join (empty <$ try anyKeyword) <|> lexeme (some C.lowerChar)


symbol :: Text -> Parser ()
symbol sy = void (L.symbol sc sy)

keyword :: Text -> Parser ()
keyword kwd = void $ lexeme (C.string kwd <* notFollowedBy C.alphaNumChar)

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

sc :: Parser ()
sc = L.space
    C.space1 -- consume as many spaces as possible
    (L.skipLineComment "--")
    (L.skipBlockCommentNested "{-" "-}") -- allows nested comments

betweenRound :: Parser a -> Parser a
betweenRound = between (symbol "(") (symbol ")")

betweenCurly :: Parser a -> Parser a
betweenCurly = between (symbol "{") (symbol "}")

betweenSquare :: Parser a -> Parser a
betweenSquare = between (symbol "[") (symbol "]")




