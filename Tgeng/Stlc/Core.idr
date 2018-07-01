module Tgeng.Stlc.Core

import Decidable.Order
import Data.Fuel

%default total

public export
data Term = Var String
          | Abs String Term
          | App Term Term

public export
data DbTerm = DbVar Nat
          | DbAbs DbTerm String
          | DbApp DbTerm DbTerm

lookUp : List (String, DbTerm) -> String -> Maybe DbTerm
lookUp [] name = Nothing
lookUp ((name', dt) :: xs) name = if name' == name then Just dt else lookUp xs name

raise : Nat -> DbTerm -> DbTerm
raise threshold ori@(DbVar i) = if i >= threshold then DbVar (S i) else ori
raise threshold (DbAbs t str) = DbAbs (raise (S threshold) t) str
raise threshold (DbApp t1 t2) = DbApp (raise threshold t1) (raise threshold t2)

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

reduceVar : (contra : LTE k i -> Void) -> DbTerm
reduceVar {k = Z} contra = void $ contra $ LTEZero
reduceVar {k = (S k)} contra = DbVar k

reduce : Nat -> DbTerm -> DbTerm
reduce i ori@(DbVar k) = case decideLTE k i of
                        (Yes prf) => ori
                        (No contra) => reduceVar contra
reduce i (DbAbs t str) = DbAbs (reduce (S i) t) str
reduce i (DbApp t1 t2) = DbApp (reduce i t1) (reduce i t2)

substitute : Nat -> DbTerm -> DbTerm -> DbTerm
substitute i s ori@(DbVar k) = if i == k then s else ori
substitute i s (DbAbs t str) = DbAbs (substitute (S i) (raise Z s) t) str
substitute i s (DbApp t1 t2) = DbApp (substitute i s t1) (substitute i s t2)

public export
data IsNormal : DbTerm -> Type where
  Mk : IsNormal $ DbAbs x y

dbVarNotNormal : IsNormal (DbVar k) -> Void
dbVarNotNormal Mk impossible

dbAppNotNormal : IsNormal (DbApp x y) -> Void
dbAppNotNormal Mk impossible

decNormal : (t: DbTerm) -> Dec (IsNormal t)
decNormal (DbVar k) = No dbVarNotNormal
decNormal (DbAbs x y) = Yes Mk
decNormal (DbApp x y) = No dbAppNotNormal

evaluate_app : (prf : IsNormal t) -> DbTerm -> DbTerm
evaluate_app {t = (DbAbs t' _)} Mk s = reduce Z $ substitute Z s t'

export
evaluate : List DbTerm -> (t :DbTerm) -> Not (IsNormal t) -> DbTerm
evaluate env ori@(DbVar k) _ = fromMaybe ori $ index' k env
evaluate env (DbAbs _ _) notNormal = void $ notNormal Mk
evaluate env ori@(DbApp t1 t2) _ = case decNormal t1 of
                                    (No contra) => DbApp (evaluate env t1 contra) t2
                                    (Yes prf) => case decNormal t2 of
                                                       (No contra) => DbApp t1 (evaluate env t2 contra)
                                                       (Yes _) => evaluate_app prf t2

export
evaluate' : DbTerm -> DbTerm
evaluate' t = case decNormal t of
                   (Yes prf) => t
                   (No contra) => evaluate [] t contra

findNewName : List String -> String -> String
findNewName names name = let similarNames = sort $ filter isSimilar names in
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

export
Show Term where
  show (Var n) = n
  show (Abs n t) = "\\" ++ n ++ "." ++ show t
  show (App t1 t2) = "(" ++ show t1 ++ " " ++ show t2 ++ ")"

export
Show DbTerm where
  show (DbVar i) = show i
  show (DbAbs t str) = "\\0" ++ ":" ++ str ++". " ++ show t
  show (DbApp t1 t2) = "(" ++ show t1 ++ show t2 ++")"

