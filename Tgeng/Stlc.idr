module Tgeng.Stlc

import Decidable.Order
import Data.Fuel

%default total

public export
data Term = Var String
          | Abs String Term
          | App Term Term

export
data DbTerm = DbVar Nat
          | DbAbs DbTerm String
          | DbApp DbTerm DbTerm

lookUp : List (String, DbTerm) -> String -> Maybe DbTerm
lookUp [] name = Nothing
lookUp ((name', dt) :: xs) name = if name' == name then Just dt else Nothing

raise : Nat -> DbTerm -> DbTerm
raise threshold ori@(DbVar i) = if i >= threshold then DbVar (S i) else ori
raise threshold (DbAbs t str) = DbAbs (raise (S threshold) t) str
raise threshold (DbApp t1 t2) = DbApp (raise threshold t1) (raise threshold t2)

raiseEnv : List (String, DbTerm) -> List (String, DbTerm)
raiseEnv = map (\(name, dt) => (name, raise Z dt))

export
toDbTerm : List (String, DbTerm) -> Term -> Either String DbTerm
toDbTerm env (Var name) = case lookUp env name of
                               Nothing => Left $ "Cannot find bining for '"++ name ++"'."
                               (Just dt) => Right dt
toDbTerm env (Abs name t) = do dt <- toDbTerm ((name, DbVar Z)::(raiseEnv env)) t
                               Right $ DbAbs dt name
toDbTerm env (App t1 t2) = do dt1 <- toDbTerm env t1
                              dt2 <- toDbTerm env t2
                              Right $ DbApp dt1 dt2

reductVar : (contra : LTE k i -> Void) -> DbTerm
reductVar {k = Z} contra = void $ contra $ LTEZero
reductVar {k = (S k)} contra = DbVar k

reduce : Nat -> DbTerm -> DbTerm
reduce i ori@(DbVar k) = case decideLTE k i of
                        (Yes prf) => ori
                        (No contra) => reductVar contra
reduce i (DbAbs t str) = DbAbs (reduce (S i) t) str
reduce i (DbApp t1 t2) = DbApp (reduce i t1) (reduce i t2)

substitute : Nat -> DbTerm -> DbTerm -> DbTerm
substitute i s ori@(DbVar k) = if i == k then s else ori
substitute i s (DbAbs t str) = DbAbs (substitute (S i) (raise Z s) t) str
substitute i s (DbApp t1 t2) = DbApp (substitute i s t1) (substitute i s t2)

export
evaluate : Fuel -> DbTerm -> DbTerm
evaluate (More fuel) (DbApp t1 t2) = let t1' = (evaluate fuel t1) in
                                     let t2' = (evaluate fuel t2) in
                                         case t1' of
                                              (DbAbs t str) => reduce Z $ substitute Z t2' t
                                              t1' => DbApp t1' t2'
evaluate fuel t = t

findNewName : List String -> String -> String
findNewName xs x = x ++ (show $ length xs)

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

Show Term where
  show (Var n) = n
  show (Abs n t) = "/" ++ n ++ ". " ++ (show t)
  show (App t1 t2) = "(" ++ (show t1) ++ (show t2) ++")"

Show DbTerm where
  show (DbVar i) = show i
  show (DbAbs t str) = "/0" ++ ":" ++ str ++". " ++ (show t)
  show (DbApp t1 t2) = "(" ++ (show t1) ++ (show t2) ++")"
