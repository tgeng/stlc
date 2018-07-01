module Tgeng.Stlc.Parser

import Tgeng.Stlc.Core
import Lightyear
import Lightyear.Strings
import Lightyear.Char
import Control.Monad.State

identifier : Parser String
identifier = map pack $ map (::) letter <*> many (alphaNum <|> char '\'') <?> "identifier"

appTerms : List Term -> Maybe Term
appTerms [] = Nothing
appTerms (x :: []) = Just x
appTerms (x :: (y :: xs)) = do let t = App x y
                               appTerms (t :: xs)

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
  expr = do app_t <- map appTerms (single `sepBy` spaces)
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

mutual
  usePrevInput : StateT (Maybe DbTerm) IO ()
  usePrevInput = do Just t <- get
                    | Nothing => simpleEval
                    let t' = evaluate' t
                    put $ Just t'
                    let Right st = toTerm [] t'
                    | Left msg => do lift $ putStrLn msg
                                     simpleEval
                    lift $ putStrLn $ show st
                    simpleEval

  handleNewInput : String -> StateT (Maybe DbTerm) IO ()
  handleNewInput input = do let Right st = parse statement input
                            | Left error => do lift $ putStrLn error
                                               simpleEval
                            lift $ putStrLn $ show st
                            let Right t = toDbTerm [] st
                            | Left error => do lift $ putStrLn error
                                               simpleEval
                            put $ Just t
                            simpleEval

  simpleEval : StateT (Maybe DbTerm) IO ()
  simpleEval = do input <- lift getLine
                  if input == ""
                     then usePrevInput
                     else handleNewInput input

eval : IO ()
eval = map fst $ runStateT simpleEval Nothing
