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

record Scientific where
  constructor MkScientific
  coefficient : Integer
  exponent : Integer

scientificToDouble : Scientific -> Double
scientificToDouble (MkScientific c e) = fromInteger c * exp
  where exp = if e < 0 then 1 / pow 10 (fromIntegerNat (- e))
                       else pow 10 (fromIntegerNat e)

parseScientific : Parser Scientific
parseScientific = do sign <- maybe 1 (const (-1)) `map` opt (char '-')
                     digits <- some digit
                     hasComma <- isJust `map` opt (char '.')
                     decimals <- if hasComma then some digit else pure Prelude.List.Nil
                     hasExponent <- isJust `map` opt (char 'e')
                     exponent <- if hasExponent then integer else pure 0
                     pure $ MkScientific (sign * fromDigits (digits ++ decimals))
                                         (exponent - cast (length decimals))
  where fromDigits : List (Fin 10) -> Integer
        fromDigits = foldl (\a, b => 10 * a + cast b) 0

number : Parser Term
number = map (Num . scientificToDouble) parseScientific

add : Parser Op
add = char '+' *!> pure Add

sub : Parser Op
sub = char '-' *!> pure Sub

mul : Parser Op
mul = char '*' *!> pure Mul

div : Parser Op
div = char '/' *!> pure Div

var : Parser Term
var = map Var identifier <?> "var"

partialBinop : Parser Op -> Parser Term -> Parser (Term -> Term)
partialBinop opParser termParser = do op <- opParser
                                      t <- termParser
                                      pure $ \t' => Binop op t' t

mutual
  abs : Parser Term
  abs = do char '\\' <* spaces
           i <- commitTo identifier
           spaces *> char '.' <* spaces
           t <- commitTo expr
           pure $ Abs i t
        <?> "abs"

  group : Parser Term
  group = char '(' *> spaces *!> expr <* spaces <* char ')' <?> "group"

  single : Parser Term
  single = number <|> var <|>| abs <|>| group <?> "single"

  appExpr : Parser Term
  appExpr = do Just t <- map appTerms (single `sepBy` spaces)
               | Nothing => fail "not enough term to form an expression"
               pure t
            <?> "appExpr"

  level9Expr : Parser Term
  level9Expr = do t <- appExpr
                  pts <- many $ partialBinop (spaces *> (mul <|> div) <* spaces) appExpr
                  pure $ foldl (\t => \pt => pt t) t pts
               <?> "level9Expr"

  level8Expr : Parser Term
  level8Expr = do t <- level9Expr
                  pts <- many $ partialBinop (spaces *> (add <|> sub) <* spaces) level9Expr
                  pure $ foldl (\t => \pt => pt t) t pts
               <?> "level8Expr"

  expr : Parser Term
  expr = level8Expr <?> "expr"

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
