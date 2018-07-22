module Tgeng.Stlc.Parser

import Data.Fuel
import Data.List
import Data.SortedMap
import Tgeng.Stlc.Core
import Lightyear
import Lightyear.Strings
import Lightyear.Char
import Control.Monad.State

spacesAround  : Parser t -> Parser t
spacesAround p = spaces *> p <* spaces

keywords : List String
keywords = ["let", "in", "letrec", "match", "fix", "true", "false"]

reserved : String -> Parser ()
reserved kw = string kw *> requireFailure alphaNum

identifier : Parser String
identifier = do name <- map pack $ map (::) letter <*> many (alphaNum <|> char '\'')
                case isElem name keywords of
                     (Yes prf) => fail $ "Keyword " ++ name ++ " cannot be an identifier."
                     (No contra) => pure name
             <?> "identifier"

tyPrimitive : Parser Ty
tyPrimitive = reserved "Bool" *> pure (TyPrimitive PrimTyBool)
         <|> reserved "Integer" *> pure (TyPrimitive PrimTyInteger)
         <|> reserved "Double" *> pure (TyPrimitive PrimTyDouble)
         <|> reserved "String" *> pure (TyPrimitive PrimTyString)

tyBottom : Parser Ty
tyBottom = reserved "Bottom" *!> pure TyBottom

tyAny : Parser Ty
tyAny = reserved "Any" *!> pure TyAny

mutual
  tyAttribute : Parser (String, Ty)
  tyAttribute = do l <- identifier
                   spacesAround $ char ':'
                   ty <- tyExpr
                   pure (l, ty)

  tyRecord : Parser Ty
  tyRecord = do char '{'
                attributes <- tyAttribute `sepBy` spacesAround (char ',')
                char '}'
                pure $ TyRecord $ fromList attributes

  tyVariant : Parser Ty
  tyVariant = do char '<'
                 attributes <- tyAttribute `sepBy` spacesAround (char ',')
                 char '>'
                 pure $ TyVariant $ fromList attributes

  tySingle : Parser Ty
  tySingle = tyPrimitive
           <|> tyBottom
           <|> tyAny
           <|>| tyRecord
           <|>| tyVariant
           <|>| (char '(' *!> spacesAround tyExpr <* char ')')
           <?> "tySingle"

  tyExpr : Parser Ty
  tyExpr = do tys <- tySingle `sepBy` (spacesAround $ string "->" )
              let Just ty = foldr combine Nothing tys
              | Nothing => fail "Not enough type for type expression"
              pure ty
           where combine : Ty -> Maybe Ty -> Maybe Ty
                 combine ty maybeTy = case maybeTy of
                                           Nothing => Just ty
                                           (Just accTy) => Just $ TyArrow ty accTy

appTerms : List Term -> Maybe Term
appTerms [] = Nothing
appTerms (x :: []) = Just x
appTerms (x :: (y :: xs)) = do let t = App x y
                               appTerms (t :: xs)

parseBool : Parser Bool
parseBool = reserved "true" *> pure True
            <|> reserved "false" *> pure False

-- double parser --
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

-- string parser --
hex : Parser Int
hex = do
  c <- map (ord . toUpper) $ satisfy isHexDigit
  pure $ if c >= ord '0' && c <= ord '9' then c - ord '0'
                                         else 10 + c - ord 'A'

hexQuad : Parser Int
hexQuad = do
  a <- hex
  b <- hex
  c <- hex
  d <- hex
  pure $ a * 4096 + b * 256 + c * 16 + d

specialChar : Parser Char
specialChar = do
  c <- anyChar
  case c of
    '"'  => pure '"'
    '\\' => pure '\\'
    '/'  => pure '/'
    'b'  => pure '\b'
    'f'  => pure '\f'
    'n'  => pure '\n'
    'r'  => pure '\r'
    't'  => pure '\t'
    'u'  => map chr hexQuad
    _    => fail "expected special char"

parseString' : Parser (List Char)
parseString' = (char '"' *!> pure Prelude.List.Nil) <|> do
  c <- satisfy (/= '"')
  if (c == '\\') then map (::) specialChar <*> parseString'
                 else map (c ::) parseString'

parseString : Parser String
parseString = char '"' *> map pack parseString' <?> "JSON string"

primVal : Parser PrimVal
primVal = map PrimValBool (parseBool)
          <|> map (PrimValDouble . scientificToDouble) parseScientific <* oneOf "dD"
          <|> map PrimValInteger integer
          <|> map PrimValString parseString

primitive : Parser Term
primitive = map Prim primVal

add : Parser Op
add = char '+' *!> pure Add

sub : Parser Op
sub = char '-' *!> pure Sub

mul : Parser Op
mul = char '*' *!> pure Mul

div : Parser Op
div = char '/' *!> pure Div

equal : Parser Op
equal = string "==" *!> pure Equal

and : Parser Op
and = string "&&" *!> pure And

or : Parser Op
or = string "||" *!> pure Or

parseNot : Parser Mod
parseNot = char '!' *!> pure Not

parseNegate : Parser Mod
parseNegate = char '-' *!> pure Negate

var : Parser Term
var = map Var identifier <?> "var"

partialBinop : Parser Op -> Parser Term -> Parser (Term -> Term)
partialBinop opParser termParser = do op <- opParser
                                      t <- termParser
                                      pure $ \t' => Binop op t' t

levelXExpr : Nat -> Parser Op -> Parser Term -> Parser Term
levelXExpr n opParser tParser = do t <- tParser
                                   pts <- many $ partialBinop (spacesAround opParser) tParser
                                   pure $ foldl (\t => \pt => pt t) t pts
                                <?> ("level" ++ show n ++ "Expr")
mutual
  abs : Parser Term
  abs = do char '\\' <* spaces
           i <- commitTo identifier
           spacesAround $ char ':'
           ty <- commitTo tyExpr
           spacesAround $ char '.'
           t <- commitTo expr
           pure $ Abs i t ty
        <?> "abs"

  letBinding : Parser Term
  letBinding = do reserved "let"
                  name <- spaces *!> identifier
                  spacesAround $ char '='
                  s <- commitTo expr
                  spacesAround $ reserved "in"
                  t <- commitTo expr
                  pure $ Let name s t
               <?> "letBinding"
  fix : Parser Term
  fix = do reserved "fix"
           name <- spaces *!> identifier
           spacesAround $ char ':'
           ty <- tyExpr
           spacesAround $ char '.'
           t <- commitTo expr
           pure $ Fix name ty t

  letrecBinding : Parser Term
  letrecBinding = do reserved "letrec"
                     name <- spaces *!> identifier
                     spacesAround $ char ':'
                     ty <- commitTo tyExpr
                     spacesAround $ char '='
                     s <- commitTo expr
                     spacesAround $ reserved "in"
                     t <- commitTo expr
                     pure $ Let name (Fix name ty s) t


  record_ : Parser Term
  record_ = map (Record . fromList) $
              char '{' *!> spacesAround (attribute `sepBy` (spacesAround $ char ',')) <* char '}'
            where attribute : Parser (String, Term)
                  attribute = do l <- identifier
                                 spaces
                                 t <- expr
                                 pure (l, t)

  variant : Parser Term
  variant = do char '<'
               l <- commitTo identifier
               spaces
               t <- expr
               char '>'
               pure $ Variant l t

  variantMatch : Term -> Parser Term
  variantMatch t = do firstBranch <- branch
                      branches <- many (spacesAround (char ',') *!> branch)
                      pure $ VariantMatch t $ fromList (firstBranch :: branches)
                   where branch : Parser (String, (String, Term))
                         branch = do l <- identifier
                                     spaces
                                     x <- identifier
                                     spacesAround $ string "=>"
                                     t <- expr
                                     pure (l, (x, t))

  primitiveMatch : Term -> Parser Term
  primitiveMatch t = do firstBranch <- branch
                        branches <- many (spacesAround (char ',') *!> branch)
                        pure $ PrimMatch t $ fromList (firstBranch :: branches)
                     where branch : Parser (PrimVal, Term)
                           branch = do pv <- primVal
                                       spacesAround $ string "=>"
                                       t <- expr
                                       pure (pv, t)

  match : Parser Term
  match = do reserved "match" <* spaces
             t <- single
             spacesAround $ char '{'
             (primitiveMatch t <|> variantMatch t) <* spaces <* char '}'

  group : Parser Term
  group = char '(' *!> spacesAround expr <* char ')' <?> "group"

  proj : Parser Term
  proj = do t <- var <|>| record_ <|>| group
            projections <- many $ char '.' *!> identifier
            pure $ foldl RecordProj t projections

  single : Parser Term
  single = primitive
           <|>| proj
           <|>| abs
           <|>| letBinding
           <|>| fix
           <|>| letrecBinding
           <|>| variant
           <|>| match
           <?> "single"

  appExpr : Parser Term
  appExpr = do Just t <- map appTerms (single `sepBy` some space)
               | Nothing => fail "not enough term to form an expression"
               pure t
            <?> "appExpr"

  modExpr : Parser Term
  modExpr = do m <- opt (parseNot <|> parseNegate)
               spaces
               t <- commitTo appExpr
               case m of
                    Just m' => pure $ Modop m' t
                    Nothing => pure t

  level9Expr : Parser Term
  level9Expr = levelXExpr 9 (mul <|> div) modExpr

  level8Expr : Parser Term
  level8Expr = levelXExpr 8 (add <|> sub) level9Expr

  level6Expr : Parser Term
  level6Expr = levelXExpr 6 equal level8Expr

  level5Expr : Parser Term
  level5Expr = levelXExpr 5 and level6Expr

  level4Expr : Parser Term
  level4Expr = levelXExpr 4 or level5Expr

  expr : Parser Term
  expr = level4Expr <?> "expr"

program : Parser Term
program = expr <* spaces <* eof

echo : IO ()
echo = do input <- getLine
          let Right t = parse program input
            | Left error => do putStrLn error
                               echo
          putStrLn $ show t
          echo

mutual
  usePrevInput : StateT (Maybe DbTerm) IO ()
  usePrevInput = do Just t <- get
                    | Nothing => smallEval
                    let t' = evaluate' t
                    put $ Just t'
                    let Right st = toTerm [] t'
                    | Left msg => do lift $ putStrLn msg
                                     smallEval
                    let eitherTy = findType [] t
                    let tyMsg = case eitherTy of
                                     Right ty => show ty
                                     Left msg => msg
                    lift $ putStrLn $ show st ++ " : " ++ tyMsg
                    smallEval

  handleNewInput : String -> StateT (Maybe DbTerm) IO ()
  handleNewInput input = do let Right st = parse program input
                            | Left error => do lift $ putStrLn error
                                               smallEval
                            let Right t = toDbTerm [] st
                            | Left error => do lift $ putStrLn error
                                               smallEval
                            let eitherTy = findType [] t
                            let tyMsg = case eitherTy of
                                             Right ty => show ty
                                             Left msg => msg
                            lift $ putStrLn $ show st ++ " : " ++ tyMsg
                            put $ Just t
                            smallEval

  smallEval : StateT (Maybe DbTerm) IO ()
  smallEval = do input <- lift getLine
                 if input == ""
                    then usePrevInput
                    else handleNewInput input

eval : IO ()
eval = map fst $ runStateT smallEval Nothing

bigEval : Fuel -> DbTerm -> DbTerm
bigEval Dry t = t
bigEval (More f) t = if isNormal t
                        then t
                        else let t' = evaluate [] t in bigEval f t'

parseAndRun : String -> Either String String
parseAndRun str =
  do t <- parse program str
     dt <- toDbTerm [] t
     ty <- findType [] dt
     let dt = bigEval (limit 10000000) dt
     t <- toTerm [] dt
     pure $ show t ++ " : " ++ show ty

getLines : String -> IO String
getLines str = do eof <- fEOF stdin
                  if eof
                  then pure str
                  else do line <- getLine
                          getLines $ str ++ line ++ "\n"

export
parseStdInAndRun : IO ()
parseStdInAndRun = do lines <- getLines ""
                      let Right result = parseAndRun lines
                      | Left error => putStrLn error
                      putStrLn result
