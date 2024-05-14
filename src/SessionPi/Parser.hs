module SessionPi.Parser where

import Data.Void (Void)
import Data.Text (Text, pack)

import Control.Monad (void, join)

import Text.Megaparsec (Parsec, choice, some, MonadParsec (notFollowedBy), try, empty, (<|>), between, parse, many)
import qualified Text.Megaparsec.Error as E
import qualified Text.Megaparsec.Char as C
import qualified Text.Megaparsec.Char.Lexer as L

import SessionPi.Language (Proc (Snd, Rec, Par, Brn, Nil, Bnd), Val (Var, Lit), BoundVar, dualType, SpiType (Boolean, End, Qualified), Qualifier (Lin, Un), Pretype (Sending, Receiving))

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
    , "end"
    , "bool"
    , "lin"
    , "un"
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

branch :: Parser Proc
branch = do
    keyword "if"
    guard <- value
    keyword "then"
    p1 <- process
    keyword "else"
    Brn guard p1 <$> parseLeaf

inaction :: Parser Proc
inaction = do
    keyword "0"
    return Nil

bind :: Parser Proc
bind = do
    var1 <- variable
    symbol "><"
    cl2@(_, t2) <- claim
    symbol "."
    let t1 = dualType <$> t2
    Bnd (var1, t1) cl2 <$> parseLeaf

send :: Parser Proc
send = do
    chn <- variable
    symbol "<<"
    val <- value
    symbol "."
    Snd chn val <$> parseLeaf

receive :: Parser Proc
receive = do
    chn <- variable
    symbol ">>"
    var <- claim
    symbol "."
    Rec chn var <$> parseLeaf

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

spiType :: Parser SpiType
spiType = choice
    [ boolType
    , inactionType
    , qualifiedPretype
    , betweenRound spiType
    ]

boolType :: Parser SpiType
boolType = Boolean <$ keyword "bool"

inactionType :: Parser SpiType
inactionType = End <$ keyword "end"

qualifiedPretype :: Parser SpiType
qualifiedPretype = do
    qual <- qualifier
    Qualified qual <$> pretype

qualifier :: Parser Qualifier
qualifier = choice
    [ Lin <$ keyword "lin"
    , Un  <$ keyword "un"
    ]

pretype :: Parser Pretype
pretype = do
    oper <- choice
        [ Sending <$ symbol "!"
        , Receiving <$ symbol "?"
        ]
    valt <- choice
        [ boolType
        , inactionType
        , betweenRound spiType
        ]
    symbol "."
    oper valt <$> spiType


claim :: Parser BoundVar
claim = do
    var <- variable
    typ <- try $ do
        symbol ":"
        Just <$> spiType
        <|>
        return Nothing
    return (var, typ)

variable :: Parser String
variable = join (empty <$ try anyKeyword) <|> variable'

variable' :: Parser String
variable' = lexeme $ do
    c <- C.lowerChar
    (c:) <$> many (C.alphaNumChar <|> C.char '_')

anyKeyword :: Parser ()
anyKeyword = choice $ keyword <$> keywords

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




