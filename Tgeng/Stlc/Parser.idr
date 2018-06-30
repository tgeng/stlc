module Tgeng.Stlc.Parser

import Tgeng.Stlc.Core
import Lightyear
import Lightyear.Strings
import Lightyear.Char

identifier : Parser String
identifier = map pack $ map (::) letter <*> many (alphaNum <|> char '\'') <?> "identifier"

app_terms : List Term -> Term
app_terms (x :: []) = x
app_terms (x :: (y :: xs)) = let t = App x y in
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
  expr = map app_terms (single `sepBy` spaces) <?> "expr"

main : IO ()
main = do input <- getLine
          let Right t = parse expr input
            | Left error => do putStrLn error
                               main
          putStrLn $ show t
          main

