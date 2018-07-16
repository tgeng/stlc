module Tgeng.Stlc.Core

import Decidable.Order
import Data.Fuel
import Data.SortedMap

%default total

public export
data Op = Add | Sub | Mul | Div

export
Show Op where
  show Add = "+"
  show Sub = "-"
  show Mul = "*"
  show Div = "/"

public export
data Ty = TyArrow Ty Ty
        | TyDouble
        | TyRecord (SortedMap String Ty)
        | TyVariant (SortedMap String Ty)
        | TyBottom
        | TyAny

export
Eq Ty where
  (==) (TyArrow x y) (TyArrow z w) = x==z && y==w
  (==) TyDouble TyDouble = True
  (==) (TyRecord m1) (TyRecord m2) = assert_total (toList m1 == toList m2)
  (==) (TyVariant m1) (TyVariant m2) = assert_total (toList m1 == toList m2)
  (==) _ TyAny = True
  (==) TyAny _ = True
  (==) _ _ = False

mutual
  containsAllAndSatisfy : SortedMap String Ty -> SortedMap String Ty -> Bool
  containsAllAndSatisfy m1 m2 = assert_total (all satisfy (toList m2))
                                  where satisfy : (String, Ty) -> Bool
                                        satisfy (l, ty2) = case lookup l m1 of
                                                               Nothing => False
                                                               (Just ty1) => isSubType ty1 ty2

  export
  isSubType : Ty -> Ty -> Bool
  isSubType (TyArrow tyA1 tyA2) (TyArrow tyB1 tyB2) = assert_total $ isSubType tyA2 tyB2 && isSubType tyB1 tyA1
  isSubType (TyRecord m1) (TyRecord m2) = containsAllAndSatisfy m1 m2
  isSubType (TyVariant m1) (TyVariant m2) = containsAllAndSatisfy m2 m1
  isSubType ty1 ty2 = ty1 == ty2

joinString : String -> List String -> String
joinString s [] = ""
joinString s (x :: []) = x
joinString s (x :: xs) = x ++ s ++ joinString s xs

showField : Show a => (String, a) -> String
showField (l, ty) = l ++ ":" ++ show ty

export
Show Ty where
  show (TyArrow ty1 ty2) = "(" ++ show ty1 ++ "->" ++ show ty2 ++ ")"
  show TyDouble = "Double"
  show (TyRecord m) = "{" ++ joinString "," (assert_total (map showField $ toList m)) ++ "}"
  show (TyVariant m) = "<" ++ joinString "," (assert_total (map showField $ toList m)) ++ ">"
  show TyBottom = "<Bottom>"
  show TyAny = "<Any>"

intersectionM : (Ord a, Monad m) => (b -> b -> m b) -> SortedMap a b -> SortedMap a b -> m (SortedMap a b)
intersectionM {m} f m1 m2 = foldlM accumulate empty (toList m1)
                        where accumulate : SortedMap a b -> (a, b) -> m (SortedMap a b)
                              accumulate acc (a, b) = case lookup a m2 of
                                                           Nothing => pure acc
                                                           Just b' => do b'' <- f b' b
                                                                         pure $ insert a b'' acc

unionM : (Monad m) => (b -> b -> m b) -> SortedMap a b -> SortedMap a b -> m (SortedMap a b)
unionM {m} f m1 m2 = foldlM accumuate m1 (toList m2)
                     where accumuate : SortedMap a b -> (a, b) -> m (SortedMap a b)
                           accumuate acc (a, b) = case lookup a m1 of
                                                       Nothing => pure $ insert a b acc
                                                       Just b' => do b'' <- f b' b
                                                                     pure $ insert a b'' acc

findSuperType : Ty -> Ty -> Either String Ty
findSuperType (TyRecord m1) (TyRecord m2) = map TyRecord $ assert_total $ intersectionM findSuperType m1 m2
findSuperType (TyVariant m1) (TyVariant m2) = map TyRecord $ assert_total $ unionM findSuperType m1 m2
findSuperType TyBottom ty = Right ty
findSuperType ty TyBottom = Right ty
findSuperType TyAny _ = Right TyAny
findSuperType _ TyAny = Right TyAny
findSuperType ty1 ty2 = Left $ "No super type for " ++ show ty1 ++ " and " ++ show ty2

public export
data Term = Var String
          | Abs String Term Ty
          | App Term Term
          | Let String Term Term
          | Num Double
          | Binop Op Term Term
          | Record (SortedMap String Term)
          | RecordProj Term String
          | Variant String Term
          | VariantMatch Term (SortedMap String (String, Term))

public export
data DbTerm = DbVar Nat
          | DbAbs String DbTerm Ty
          | DbApp DbTerm DbTerm
          | DbLet String DbTerm DbTerm
          | DbNum Double
          | DbBinop Op DbTerm DbTerm
          | DbRecord (SortedMap String DbTerm)
          | DbRecordProj DbTerm String
          | DbVariant String DbTerm
          | DbVariantMatch DbTerm (SortedMap String (String, DbTerm))

lookUp : List (String, DbTerm) -> String -> Maybe DbTerm
lookUp [] name = Nothing
lookUp ((name', dt) :: xs) name = if name' == name then Just dt else lookUp xs name

raise : Nat -> DbTerm -> DbTerm
raise threshold dbVar@(DbVar i) = if i >= threshold then DbVar (S i) else dbVar
raise threshold (DbAbs str t ty) = DbAbs str (raise (S threshold) t) ty
raise threshold (DbApp t1 t2) = DbApp (raise threshold t1) (raise threshold t2)
raise threshold (DbLet name s t) = DbLet name (raise threshold s) (raise (S threshold) t)
raise threshold dbNum@(DbNum i) = dbNum
raise threshold (DbBinop op t1 t2) = DbBinop op (raise threshold t1) (raise threshold t2)
raise threshold (DbRecord m) = DbRecord $ assert_total (map (raise threshold) m)
raise threshold (DbRecordProj t l) = DbRecordProj (raise threshold t) l
raise threshold (DbVariant l t) = DbVariant l $ raise threshold t
raise threshold (DbVariantMatch t m) = DbVariantMatch (raise threshold t) $ assert_total (map (\(l, t') => (l, raise (S threshold) t')) m)

raiseEnv : List (String, DbTerm) -> List (String, DbTerm)
raiseEnv = map (\(name, dt) => (name, raise Z dt))

addNewBindingToEnv : String -> List (String, DbTerm) -> List (String, DbTerm)
addNewBindingToEnv name env = (name, DbVar Z)::raiseEnv env

sequenceSortedMap : (Applicative a, Ord k) => SortedMap k (a t) -> a (SortedMap k t)
sequenceSortedMap m = map fromList $ sequence $ map bringUp $ toList m
                      where bringUp : Applicative a => (s, a t) -> a (s, t)
                            bringUp (s, at) = map (\t => (s, t)) at

export
toDbTerm : List (String, DbTerm) -> Term -> Either String DbTerm
toDbTerm env (Var name) = case lookUp env name of
                               Nothing => Left $ "Cannot find binding for '"++ name ++"'."
                               (Just dt) => Right dt
toDbTerm env (Abs name t ty) = do dt <- toDbTerm (addNewBindingToEnv name env) t
                                  Right $ DbAbs name dt ty
toDbTerm env (App t1 t2) = do dt1 <- toDbTerm env t1
                              dt2 <- toDbTerm env t2
                              Right $ DbApp dt1 dt2
toDbTerm env (Let name s t) = do ds <- toDbTerm env s
                                 dt <- toDbTerm (addNewBindingToEnv name env) t
                                 Right $ DbLet name ds dt
toDbTerm env (Num i) = Right $ DbNum i
toDbTerm env (Binop op t1 t2) = do dt1 <- toDbTerm env t1
                                   dt2 <- toDbTerm env t2
                                   Right $ DbBinop op dt1 dt2
toDbTerm env (Record m) = map DbRecord $ sequenceSortedMap $ assert_total ((map $ toDbTerm env) m)
toDbTerm env (RecordProj t l) = map ((flip DbRecordProj) l) $ toDbTerm env t
toDbTerm env (Variant l t) = map (DbVariant l) $ toDbTerm env t
toDbTerm env (VariantMatch t m) = do dt <- toDbTerm env t
                                     let m' = assert_total (map convert m)
                                     dm <- sequenceSortedMap m'
                                     pure $ DbVariantMatch dt dm
                                  where convert : (String, Term) -> Either String (String, DbTerm)
                                        convert (l, t) = do dt <- toDbTerm (addNewBindingToEnv l env) t
                                                            pure (l, dt)

reduceVar : (contra : LTE k i -> Void) -> DbTerm
reduceVar {k = Z} contra = void $ contra $ LTEZero
reduceVar {k = (S k)} contra = DbVar k

applyToSecond : (a -> b) -> (x, a) -> (x, b)
applyToSecond f (x, a) = (x, f a)

reduce : Nat -> DbTerm -> DbTerm
reduce i dbVar@(DbVar k) = case decideLTE k i of
                        (Yes prf) => dbVar
                        (No contra) => reduceVar contra
reduce i (DbAbs str t ty) = DbAbs str (reduce (S i) t) ty
reduce i (DbApp t1 t2) = DbApp (reduce i t1) (reduce i t2)
reduce i (DbLet name s t) = DbLet name (reduce i s) (reduce (S i) t)
reduce i dbNum@(DbNum _) = dbNum
reduce i (DbBinop op t1 t2) = DbBinop op (reduce i t1) (reduce i t2)
reduce i (DbRecord m) = DbRecord $ assert_total (map (reduce i) m)
reduce i (DbRecordProj t l) = DbRecordProj (reduce i t) l
reduce i (DbVariant l t) = DbVariant l (reduce i t)
reduce i (DbVariantMatch t m) = DbVariantMatch (reduce i t) $ assert_total (map (applyToSecond $ assert_total (reduce $ S i))) m

substitute : Nat -> DbTerm -> DbTerm -> DbTerm
substitute i s dbVar@(DbVar k) = if i == k then s else dbVar
substitute i s (DbAbs str t ty) = DbAbs str (substitute (S i) (raise Z s) t) ty
substitute i s (DbApp t1 t2) = DbApp (substitute i s t1) (substitute i s t2)
substitute i s (DbLet name s' t) = DbLet name (substitute i s s') (substitute (S i) (raise Z s) t)
substitute i s dbNum@(DbNum _) = dbNum
substitute i s (DbBinop op t1 t2) = DbBinop op (substitute i s t1) (substitute i s t2)
substitute i s (DbRecord m) = DbRecord $ assert_total (map (substitute i s) m)
substitute i s (DbRecordProj t l) = DbRecordProj (substitute i s t) l
substitute i s (DbVariant l t) = DbVariant l $ substitute i s t
substitute i s (DbVariantMatch t m) = DbVariantMatch (substitute i s t) $ assert_total (map (applyToSecond (substitute (S i) (raise Z s))) m)

export
isNormal : DbTerm -> Bool
isNormal (DbVar _) = False
isNormal (DbAbs _ _ _) = True
isNormal (DbApp _ _) = False
isNormal (DbLet _ _ _) = False
isNormal (DbNum _) = True
isNormal (DbBinop _ _ _) = False
isNormal (DbRecord m) = assert_total (all isNormal $ values m)
isNormal (DbRecordProj _ _) = False
isNormal (DbVariant _ t) = isNormal t
isNormal (DbVariantMatch _ _) = False

evaluate_binop : (op : Op) -> DbTerm -> DbTerm -> DbTerm
evaluate_binop op (DbNum i1) (DbNum i2) =
  case op of
    Add => DbNum $ i1 + i2
    Sub => DbNum $ i1 - i2
    Mul => DbNum $ i1 * i2
    Div => DbNum $ i1 / i2
evaluate_binop op t1 t2  = DbBinop op t1 t2

export
evaluate : List DbTerm -> DbTerm -> DbTerm
evaluate env dbVar@(DbVar k) = fromMaybe dbVar $ index' k env
evaluate env dbApp@(DbApp t1 t2) =
  if isNormal t1
  then if isNormal t2
       then case t1 of
                 (DbAbs _ t1' _) => reduce Z $ substitute Z t2 t1'
                 _ => dbApp
       else DbApp t1 (evaluate env t2)
  else DbApp (evaluate env t1) t2
evaluate env (DbLet name s t) =
  if isNormal s
  then DbLet name (evaluate env s) t
  else reduce Z $ substitute Z s t
evaluate env (DbBinop op t1 t2) =
  if isNormal t1
  then if isNormal t2
       then evaluate_binop op t1 t2
       else DbBinop op t1 (evaluate env t2)
  else DbBinop op (evaluate env t1) t2
evaluate env (DbRecord m) = DbRecord $ assert_total (map (evaluate env) m)
evaluate env (DbRecordProj t l) = if isNormal t
                                     then case t of
                                          (DbRecord m) => maybe t id (lookup l m)
                                          _ => t
                                     else DbRecordProj (evaluate env t) l
evaluate env (DbVariant l t) = DbVariant l $ evaluate env t
evaluate env (DbVariantMatch t m) =
  if isNormal t
     then case t of
               (DbVariant l s) => case lookup l m of
                                       Nothing => t
                                       (Just (_, t)) => reduce Z $ substitute Z s t
               _ => t
     else DbVariantMatch (evaluate env t) m
evaluate _ t = t

export
evaluate' : DbTerm -> DbTerm
evaluate' t = evaluate [] t

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
toTerm env (DbAbs str dt ty) = do let name = findNewName env str
                                  subTerm <- (toTerm (name :: env) dt)
                                  Right $ Abs name subTerm ty
toTerm env (DbApp dt1 dt2) = do t1 <- toTerm env dt1
                                t2 <- toTerm env dt2
                                Right $ App t1 t2
toTerm env (DbLet name ds dt) = do s <- toTerm env ds
                                   t <- toTerm (name::env) dt
                                   Right $ Let name s t
toTerm env (DbNum i) = Right $ Num i
toTerm env (DbBinop op dt1 dt2) = do t1 <- toTerm env dt1
                                     t2 <- toTerm env dt2
                                     Right $ Binop op t1 t2
toTerm env (DbRecord m) = map Record $ sequenceSortedMap $ assert_total (map (toTerm env) m)
toTerm env (DbRecordProj t l) = [| RecordProj (toTerm env t) (pure l) |]
toTerm env (DbVariant l t) = map (Variant l) $ toTerm env t
toTerm env (DbVariantMatch t m) = [| VariantMatch (toTerm env t) (sequenceSortedMap $ assert_total (map convert m)) |]
                                  where convert : (String, DbTerm) -> Either String (String, Term)
                                        convert (l, dt) = do let name = findNewName env l
                                                             t <- toTerm (name :: env) dt
                                                             pure (l, t)

export
findType : List Ty -> DbTerm -> Either String Ty
findType tys (DbVar k) = case index' k tys of
                              Nothing => Left $ "No binding for " ++ show k
                              Just t => Right t
findType tys (DbAbs _ t ty) = case findType (ty::tys) t of
                                Right bodyTy => Right $ TyArrow ty bodyTy
                                Left msg => Left msg
findType tys (DbApp t1 t2) = do ty1 <- findType tys t1
                                ty2 <- findType tys t2
                                (case ty1 of
                                      TyArrow ty2' ty3 => if isSubType ty2 ty2'
                                                          then Right ty3
                                                          else Left $ "Type mismatch between " ++ show ty2 ++ " and " ++ show ty2'
                                      TyAny => Right TyAny
                                      _ => Left "Can only apply to Arrow or Any")
findType tys (DbLet name s t) = do ty1 <- findType tys s
                                   findType (ty1::tys) t
findType tys (DbNum x) = Right TyDouble
findType tys (DbBinop op t1 t2) = do ty1 <- findType tys t1
                                     ty2 <- findType tys t2
                                     if ty1 == TyDouble && ty2 == TyDouble
                                     then Right TyDouble
                                     else Left $ "Type mismatch for operator " ++ show op
findType tys (DbRecord m) = map TyRecord $ sequenceSortedMap $ assert_total $ map (findType tys) m
findType tys (DbRecordProj t l) = do ty <- findType tys t
                                     case ty of
                                          (TyRecord m) => case lookup l m of
                                                               Nothing => Left $ show ty ++ "does not have field " ++ l
                                                               (Just ty) => Right ty
                                          _ => Left "Projection can only applied on record."
findType tys (DbVariant l t) = [| (TyVariant . fromList . (\ty => [(l, ty)])) (findType tys t) |]
findType tys (DbVariantMatch t bm) = do TyVariant tym <- findType tys t
                                        | _ => Left "Can only match on variant."
                                        btys <-  zipMap bm tym
                                        foldlM findSuperType TyBottom btys
                                     where zipMap : SortedMap String (String, DbTerm) -> SortedMap String Ty -> Either String (List Ty)
                                           -- Here we simply allow additional branches that the matched type does not contain
                                           zipMap bm tym = sequence $ map convert $ toList tym
                                           where convert : (String, Ty) -> Either String Ty
                                                 convert (l, ty) = do let Just (_, t) = lookup l bm
                                                                        | Nothing => Left ("Missing branch for " ++ l)
                                                                      findType (ty::tys) t



export
Show Term where
  show (Var n) = n
  show (Abs n t ty) = "(\\" ++ n ++ ":" ++ show ty ++ "." ++ show t ++ ")"
  show (App t1 t2) = show t1 ++ " " ++ show t2
  show (Let name s t) = "let " ++ name ++ "=" ++ show s ++ " in " ++ show t
  show (Num i) = show i
  show (Binop op t1 t2) = "(" ++ show t1 ++ show op ++ show t2 ++ ")"
  show (Record m) = "{" ++ joinString "," (assert_total (map showField $ toList m)) ++ "}"
                    where showField : (String, Term) -> String
                          showField (l, t) = l ++ " " ++ show t
  show (RecordProj t l) = show t ++ "." ++ l
  show (Variant l t) = "<" ++ l ++ " " ++ show t ++ ">"
  show (VariantMatch t m) = "match " ++ show t ++ " {" ++ joinString "," (assert_total (map showBranch $ toList m)) ++ "}"
                           where showBranch : (String, (String, Term)) -> String
                                 showBranch (l, (x, t)) = l ++ " " ++ x ++ " => " ++ show t

