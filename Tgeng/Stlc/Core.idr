module Tgeng.Stlc.Core

import Decidable.Order
import Data.Fuel

%default total

public export
data Op = Add | Sub | Mul | Div

public export
data Term = Var String
          | Abs String Term
          | App Term Term
          | Num Double
          | Binop Op Term Term

public export
data DbTerm = DbVar Nat
          | DbAbs DbTerm String
          | DbApp DbTerm DbTerm
          | DbNum Double
          | DbBinop Op DbTerm DbTerm

lookUp : List (String, DbTerm) -> String -> Maybe DbTerm
lookUp [] name = Nothing
lookUp ((name', dt) :: xs) name = if name' == name then Just dt else lookUp xs name

raise : Nat -> DbTerm -> DbTerm
raise threshold dbVar@(DbVar i) = if i >= threshold then DbVar (S i) else dbVar
raise threshold (DbAbs t str) = DbAbs (raise (S threshold) t) str
raise threshold (DbApp t1 t2) = DbApp (raise threshold t1) (raise threshold t2)
raise threshold dbNum@(DbNum i) = dbNum
raise threshold (DbBinop op t1 t2) = DbBinop op (raise threshold t1) (raise threshold t2)

raiseEnv : List (String, DbTerm) -> List (String, DbTerm)
raiseEnv = map (\(name, dt) => (name, raise Z dt))

export
toDbTerm : List (String, DbTerm) -> Term -> Either String DbTerm
toDbTerm env (Var name) = case lookUp env name of
                               Nothing => Left $ "Cannot find binding for '"++ name ++"'."
                               (Just dt) => Right dt
toDbTerm env (Abs name t) = do dt <- toDbTerm ((name, DbVar Z)::(raiseEnv env)) t
                               Right $ DbAbs dt name
toDbTerm env (App t1 t2) = do dt1 <- toDbTerm env t1
                              dt2 <- toDbTerm env t2
                              Right $ DbApp dt1 dt2
toDbTerm env (Num i) = Right $ DbNum i
toDbTerm env (Binop op t1 t2) = do dt1 <- toDbTerm env t1
                                   dt2 <- toDbTerm env t2
                                   Right $ DbBinop op dt1 dt2

reduceVar : (contra : LTE k i -> Void) -> DbTerm
reduceVar {k = Z} contra = void $ contra $ LTEZero
reduceVar {k = (S k)} contra = DbVar k

reduce : Nat -> DbTerm -> DbTerm
reduce i dbVar@(DbVar k) = case decideLTE k i of
                        (Yes prf) => dbVar
                        (No contra) => reduceVar contra
reduce i (DbAbs t str) = DbAbs (reduce (S i) t) str
reduce i (DbApp t1 t2) = DbApp (reduce i t1) (reduce i t2)
reduce i dbNum@(DbNum _) = dbNum
reduce i (DbBinop op t1 t2) = DbBinop op (reduce i t1) (reduce i t2)

substitute : Nat -> DbTerm -> DbTerm -> DbTerm
substitute i s dbVar@(DbVar k) = if i == k then s else dbVar
substitute i s (DbAbs t str) = DbAbs (substitute (S i) (raise Z s) t) str
substitute i s (DbApp t1 t2) = DbApp (substitute i s t1) (substitute i s t2)
substitute i s dbNum@(DbNum _) = dbNum
substitute i s (DbBinop op t1 t2) = DbBinop op (substitute i s t1) (substitute i s t2)

public export
data IsNormal : DbTerm -> Type where
  MkAbs : IsNormal $ DbAbs x y
  MkNum : IsNormal $ DbNum i

dbVarNotNormal : IsNormal (DbVar _) -> Void
dbVarNotNormal MkAbs impossible
dbVarNotNormal MkNum impossible

dbAppNotNormal : IsNormal (DbApp _ _) -> Void
dbAppNotNormal MkAbs impossible
dbAppNotNormal MkNum impossible

DbBinopNotNormal : IsNormal (DbBinop _ _ _) -> Void
DbBinopNotNormal MkAbs impossible
DbBinopNotNormal MkNum impossible

decNormal : (t: DbTerm) -> Dec (IsNormal t)
decNormal (DbVar _) = No dbVarNotNormal
decNormal (DbAbs _ _) = Yes MkAbs
decNormal (DbApp _ _) = No dbAppNotNormal
decNormal (DbNum _) = Yes MkNum
decNormal (DbBinop _ _ _) = No DbBinopNotNormal

evaluate_app : (prf : IsNormal t) -> DbTerm -> DbTerm
evaluate_app {t = (DbAbs t' _)} MkAbs s = reduce Z $ substitute Z s t'
evaluate_app {t = t@(DbNum _)} MkNum s = DbApp t s


evaluate_binop : (op : Op) -> (prf1 : IsNormal t1) -> (prf2 : IsNormal t2) -> DbTerm
evaluate_binop {t1 = (DbNum i1)} {t2 = (DbNum i2)} op MkNum MkNum =
  case op of
    Add => DbNum $ i1 + i2
    Sub => DbNum $ i1 - i2
    Mul => DbNum $ i1 * i2
    Div => DbNum $ i1 / i2
evaluate_binop {t1} {t2} op _ _  = DbBinop op t1 t2

export
evaluate : List DbTerm -> (t :DbTerm) -> Not (IsNormal t) -> DbTerm
evaluate env dbVar@(DbVar k) _ = fromMaybe dbVar $ index' k env
evaluate env (DbAbs _ _) notNormal = void $ notNormal MkAbs
evaluate env (DbApp t1 t2) _ =
  case decNormal t1 of
    (No contra) => DbApp (evaluate env t1 contra) t2
    (Yes prf) => case decNormal t2 of
                       (No contra) => DbApp t1 (evaluate env t2 contra)
                       (Yes _) => evaluate_app prf t2
evaluate env dbNum@(DbNum _) notNormal = void $ notNormal MkNum
evaluate env (DbBinop op t1 t2) notNormal =
  case decNormal t1 of
    (No contra) => DbBinop op (evaluate env t1 contra) t2
    (Yes prf1) => case decNormal t2 of
                      (No contra) => DbBinop op t1 (evaluate env t2 contra)
                      (Yes prf2) => evaluate_binop op prf1 prf2

export
evaluate' : DbTerm -> DbTerm
evaluate' t = case decNormal t of
                   (Yes prf) => t
                   (No contra) => evaluate [] t contra

findNewName : List String -> String -> String
findNewName names name =
  let similarNames = sort $ filter isSimilar names in
      findGap Z similarNames
      where isSimilar : String -> Bool
            isSimilar n = isPrefixOf name n &&
                          let suffix = drop (length name) $ unpack n in
                              all (== ''') suffix
            findGap : Nat -> List String -> String
            findGap l [] = name ++ (pack (replicate l '\''))
            findGap l (n :: ns) = if l + (length name) == (length n)
                                     then findGap (S l) ns
                                     else name ++ (pack (replicate l '\''))

export
toTerm : List String -> DbTerm -> Either String Term
toTerm env (DbVar k) = case index' k env of
                            Nothing => Left ("Index " ++ (show k) ++ " cannot be found.")
                            (Just name) => Right $ Var name
toTerm env (DbAbs dt str) = do let name = findNewName env str
                               subTerm <- (toTerm (name :: env) dt)
                               Right $ Abs name subTerm
toTerm env (DbApp dt1 dt2) = do t1 <- toTerm env dt1
                                t2 <- toTerm env dt2
                                Right $ App t1 t2
toTerm env (DbNum i) = Right $ Num i
toTerm env (DbBinop op dt1 dt2) = do t1 <- toTerm env dt1
                                     t2 <- toTerm env dt2
                                     Right $ Binop op t1 t2

export
Show Op where
  show Add = "+"
  show Sub = "-"
  show Mul = "*"
  show Div = "/"

export
Show Term where
  show (Var n) = n
  show (Abs n t) = "\\" ++ n ++ "." ++ show t
  show (App t1 t2) = "(" ++ show t1 ++ " " ++ show t2 ++ ")"
  show (Num i) = show i
  show (Binop op t1 t2) = "(" ++ show t1 ++ show op ++ show t2 ++ ")"

export
Show DbTerm where
  show (DbVar i) = "#" ++ show i
  show (DbAbs t str) = "\\0" ++ "%" ++ str ++". " ++ show t
  show (DbApp t1 t2) = "(" ++ show t1 ++ show t2 ++")"
  show (DbNum i) = show i
  show (DbBinop op t1 t2) = "(" ++ show t1 ++ show op ++ show t2 ++ ")"
