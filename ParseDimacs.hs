{-# OPTIONS_GHC -Wall #-}

module ParseDimacs ( parseDimacsFile
                   ) where

import Types

import Control.Monad (liftM)
import Data.Sequence (fromList)
import Text.Parsec( ParseError )
import Text.Parsec.Char
import Text.Parsec.Combinator
import Text.Parsec.Prim
import qualified Text.Parsec.Token as T

type Parser a = Parsec String () a

parseDimacsFile :: FilePath -> IO (Either ParseError Formula)
parseDimacsFile fileName = do
    input <- readFile fileName
    return (parse cnf fileName input)

cnf :: Parser Formula
cnf = cnfHeader >> many clause >>= return . fromList

clause :: Parser Clause
clause = liftM fromList $ lexeme int `manyTill` try (symbol "0")

-- Parses into `(numVars, numClauses)'.
cnfHeader :: Parser (Int, Int)
cnfHeader = parseSyms >> natural >>= \numVars -> natural >>= \numClauses -> return (numVars, numClauses)
  where parseSyms = whiteSpace >> char 'p' >> many1 space >> symbol "cnf"

-- token parser
tokenizer :: T.TokenParser ()
tokenizer = T.makeTokenParser T.LanguageDef
   { T.commentStart = ""
   , T.commentEnd = ""
   , T.commentLine = "c"
   , T.nestedComments = False
   , T.identStart = unexpected "ParseDIMACS bug: shouldn't be parsing identifiers..."
   , T.identLetter = unexpected "ParseDIMACS bug: shouldn't be parsing identifiers..."
   , T.opStart = unexpected "ParseDIMACS bug: shouldn't be parsing operators..."
   , T.opLetter = unexpected "ParseDIMACS bug: shouldn't be parsing operators..."
   , T.reservedNames = ["p", "cnf"]
   , T.reservedOpNames = []
   , T.caseSensitive = True
   }

natural :: Parser Int
natural = liftM fromIntegral $ T.natural tokenizer

int :: Parser Int
int = liftM fromIntegral $ T.integer tokenizer

symbol :: String -> Parser String
symbol = T.symbol tokenizer

whiteSpace :: Parser ()
whiteSpace = T.whiteSpace tokenizer

lexeme :: Parser a -> Parser a
lexeme = T.lexeme tokenizer
