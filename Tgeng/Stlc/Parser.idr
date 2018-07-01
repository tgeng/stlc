module Tgeng.Stlc.Parser

import Tgeng.Stlc.Core
import Lightyear
import Lightyear.Strings
import Lightyear.Char
import Control.Monad.State

identifier : Parser String
identifier = map pack $ map (::) letter <*> many (alphaNum <|> char '\'') <?> "identifier"

app_terms : List Term -> Maybe Term
app_terms [] = Nothing
app_terms (x :: []) = Just x
app_terms (x :: (y :: xs)) = do let t = App x y
                                app_terms (t :: xs)

var : Parser Term
var = map Var identifier <?> "var"

mutual
  abs : Parser Term
  abs = (do char '\\' <* spaces
            i <- commitTo identifier
            spaces *> char '.' <* spaces
            t <- commitTo expr
            pure $ Abs i t) <?> "abs"

  group : Parser Term
  group = char '(' *> spaces *!> expr <* spaces <* char ')' <?> "group"

  single : Parser Term
  single = var <|>| abs <|>| group <?> "single"

  expr : Parser Term
  expr = do app_t <- map app_terms (single `sepBy` spaces)
            case app_t of
              Just t => pure t
              Nothing => fail "not enough term to form an expression"
         <?> "expr"

statement : Parser Term
statement = expr <* eof

echo : IO ()
echo = do input <- getLine
          let Right t = parse statement input
            | Left error => do putStrLn error
                               echo
          putStrLn $ show t
          echo

