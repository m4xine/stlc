module Parser
  ( parseExpr
  ) where

import  Control.Applicative             ((<|>), Alternative (..))
import  Control.Applicative.Combinators (choice)
import  Control.Monad.Combinators.Expr  (makeExprParser, Operator (Postfix, InfixL))
import  Control.Comonad.Cofree          (Cofree ((:<)))
import  Control.Category.Unicode        ((∘))
import  Data.Void                       (Void)
import  Data.Composition                ((.:))
import  Text.Megaparsec                 (Parsec, between, ParseErrorBundle, MonadParsec (eof), parse)
import  Text.Megaparsec.Char.Lexer      (lexeme)
import  Text.Megaparsec.Char            (space, char, letterChar, digitChar)
import  Expr                            (Expr, ExprF (..))

type Parser = Parsec Void String

l ∷ Parser α → Parser α
l = lexeme space

lchar ∷ Char → Parser Char
lchar = l . char 

name ∷ Parser String
name =
    (:) <$> head <*> many tail
  where
    head = letterChar
    tail = head <|> digitChar <|> char '\''

expr ∷ Parser (Expr ())
expr =
    makeExprParser term table
  where
    wrap = fmap (() :<)
    wrap2 = fmap ((() :<) .:)
    parens = between (lchar '(') (char ')')
    abs = wrap $ EAbs
      <$> do lchar '\\' *> l name
      <*> do lchar '.' *> expr
    var = wrap $ EVar <$> name
    term = l $ choice [abs, var, parens expr]
    table = [[InfixL ∘ wrap2 $ pure EApp]]

parseExpr 
  ∷ FilePath 
  → String 
  → Either (ParseErrorBundle String Void) (Expr ())
parseExpr = parse $ space *> l expr <* eof