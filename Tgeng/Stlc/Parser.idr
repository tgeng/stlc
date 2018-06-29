module Tgeng.Stlc.Parser

import Tgeng.Stlc.Core
import Lightyear
import Lightyear.Strings
import Lightyear.Char

identifier : Parser String
identifier = map pack $ map (::) letter <*> many (alphaNum <|> char '\'') <?> "identifier"

mutual
  var : Parser Term
  var = map Var identifier <?> "var"

  abs : Parser Term
  abs = (do char '\\'
            i <- commitTo identifier
            char '.'
            t <- commitTo term
            pure $ Abs i t) <?> "abs"

  app : Parser Term
  app = (do char '('
            t1 <- commitTo term
            space
            t2 <- commitTo term
            char ')'
            pure $ App t1 t2) <?> "app"

  term : Parser Term
  term = var <|>| abs <|>| app <?> "term"
