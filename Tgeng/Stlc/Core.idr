module Tgeng.Stlc.Core

import Decidable.Order
import Data.Fuel
import Data.SortedMap

%default total

public export
data Op = Add | Sub | Mul | Div | Equal | And | Or

export
Show Op where
  show Add = "+"
  show Sub = "-"
  show Mul = "*"
  show Div = "/"
  show Equal = "=="
  show And = "&&"
  show Or = "||"

public export
data Mod = Not | Negate

export
Show Mod where
  show Not = "!"
  show Negate = "-"

public export
data PrimTy = PrimTyBool | PrimTyInteger | PrimTyDouble | PrimTyString

export
Show PrimTy where
  show PrimTyBool = "Bool"
  show PrimTyInteger = "Integer"
  show PrimTyDouble = "Double"
  show PrimTyString = "String"

export
Eq PrimTy where
  (==) PrimTyBool PrimTyBool = True
  (==) PrimTyInteger PrimTyInteger = True
  (==) PrimTyDouble PrimTyDouble = True
  (==) PrimTyString PrimTyString = True
  (==) _ _ = False

public export
data Ty = TyArrow Ty Ty
        | TyPrimitive PrimTy
        | TyRecord (SortedMap String Ty)
        | TyVariant (SortedMap String Ty)
        | TyBottom
        | TyAny

export
Eq Ty where
  (==) (TyArrow x y) (TyArrow z w) = x==z && y==w
  (==) (TyPrimitive pty1) (TyPrimitive pty2) = pty1 == pty2
  (==) (TyRecord m1) (TyRecord m2) = assert_total (toList m1 == toList m2)
  (==) (TyVariant m1) (TyVariant m2) = assert_total (toList m1 == toList m2)
  (==) _ TyAny = True
  (==) TyAny _ = True
  (==) _ _ = False

mutual
  containsAllLabeledTypes : Bool -> SortedMap String Ty -> SortedMap String Ty -> Bool
  containsAllLabeledTypes reverse m1 m2 = assert_total (all satisfy (toList m2))
                                          where satisfy : (String, Ty) -> Bool
                                                satisfy (l, ty2) = case lookup l m1 of
                                                                        Nothing => False
                                                                        (Just ty1) => if reverse
                                                                                         then isSubType ty2 ty1
                                                                                         else isSubType ty1 ty2

  export
  isSubType : Ty -> Ty -> Bool
  isSubType (TyArrow tyA1 tyA2) (TyArrow tyB1 tyB2) = assert_total $ isSubType tyA2 tyB2 && isSubType tyB1 tyA1
  isSubType (TyRecord m1) (TyRecord m2) = containsAllLabeledTypes False m1 m2
  isSubType (TyVariant m1) (TyVariant m2) = containsAllLabeledTypes True m2 m1
  isSubType TyBottom _ = True
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
  show (TyPrimitive pty) = show pty
  show (TyRecord m) = "{" ++ joinString "," (assert_total (map showField $ toList m)) ++ "}"
  show (TyVariant m) = "<" ++ joinString "," (assert_total (map showField $ toList m)) ++ ">"
  show TyBottom = "Bottom"
  show TyAny = "Any"

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
findSuperType ty1 ty2 = if isSubType ty1 ty2
                           then Right ty2
                           else if isSubType ty2 ty1
                                   then Right ty1
                                   else Left $ "No super type for " ++ show ty1 ++ " and " ++ show ty2
public export
data PrimVal = PrimValBool Bool | PrimValInteger Integer | PrimValDouble Double | PrimValString String

Eq PrimVal where
  (==) (PrimValBool x) (PrimValBool y) = x == y
  (==) (PrimValInteger x) (PrimValInteger y) = x == y
  (==) (PrimValDouble x) (PrimValDouble y) = x == y
  (==) (PrimValString x) (PrimValString y) = x == y
  (==) _ _ = False

export
Ord PrimVal where
  compare (PrimValBool x) (PrimValBool y) = compare x y
  compare (PrimValBool _) _ = LT
  compare _ (PrimValBool _) = GT
  compare (PrimValInteger x) (PrimValInteger y) = compare x y
  compare (PrimValInteger _) _ = LT
  compare _ (PrimValInteger _) = GT
  compare (PrimValDouble x) (PrimValDouble y) = compare x y
  compare (PrimValDouble _) _ = LT
  compare _ (PrimValDouble _) = GT
  compare (PrimValString x) (PrimValString y) = compare x y

export
Show PrimVal where
  show (PrimValBool b) = toLower $ show b
  show (PrimValInteger i) = show i
  show (PrimValDouble d) = show d ++ "D"
  show (PrimValString s) = show s

findPrimType : PrimVal -> PrimTy
findPrimType (PrimValBool _) = PrimTyBool
findPrimType (PrimValInteger _) = PrimTyInteger
findPrimType (PrimValDouble _) = PrimTyDouble
findPrimType (PrimValString _) = PrimTyString

public export
data Term = Var String
          | Abs String Term Ty
          | App Term Term
          | Let String Term Term
          | Fix String Ty Term
          | Prim PrimVal
          | Binop Op Term Term
          | Modop Mod Term
          | Record (SortedMap String Term)
          | RecordProj Term String
          | Variant String Term
          | VariantMatch Term (SortedMap String (String, Term))
          | PrimMatch Term (SortedMap PrimVal Term)

public export
data DbTerm = DbVar Nat
          | DbAbs String DbTerm Ty
          | DbApp DbTerm DbTerm
          | DbLet String DbTerm DbTerm
          | DbFix String Ty DbTerm
          | DbPrim PrimVal
          | DbBinop Op DbTerm DbTerm
          | DbModop Mod DbTerm
          | DbRecord (SortedMap String DbTerm)
          | DbRecordProj DbTerm String
          | DbVariant String DbTerm
          | DbVariantMatch DbTerm (SortedMap String (String, DbTerm))
          | DbPrimMatch DbTerm (SortedMap PrimVal DbTerm)

lookUp : List (String, DbTerm) -> String -> Maybe DbTerm
lookUp [] name = Nothing
lookUp ((name', dt) :: xs) name = if name' == name then Just dt else lookUp xs name

raise : Nat -> DbTerm -> DbTerm
raise threshold dbVar@(DbVar i) = if i >= threshold then DbVar (S i) else dbVar
raise threshold (DbAbs str t ty) = DbAbs str (raise (S threshold) t) ty
raise threshold (DbApp t1 t2) = DbApp (raise threshold t1) (raise threshold t2)
raise threshold (DbLet name s t) = DbLet name (raise threshold s) (raise (S threshold) t)
raise threshold (DbFix name ty t) = DbFix name ty (raise (S threshold) t)
raise threshold (DbBinop op t1 t2) = DbBinop op (raise threshold t1) (raise threshold t2)
raise threshold (DbRecord m) = DbRecord $ assert_total (map (raise threshold) m)
raise threshold (DbRecordProj t l) = DbRecordProj (raise threshold t) l
raise threshold (DbVariant l t) = DbVariant l $ raise threshold t
raise threshold (DbVariantMatch t m) = DbVariantMatch (raise threshold t) $ assert_total (map (\(l, t') => (l, raise (S threshold) t')) m)
raise threshold t = t

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
toDbTerm env (Fix name ty t) = do dt <- toDbTerm (addNewBindingToEnv name env) t
                                  Right $ DbFix name ty dt
toDbTerm env (Prim pv) = Right $ DbPrim pv
toDbTerm env (Binop op t1 t2) = do dt1 <- toDbTerm env t1
                                   dt2 <- toDbTerm env t2
                                   Right $ DbBinop op dt1 dt2
toDbTerm env (Modop mod t) = map (DbModop mod) (toDbTerm env t)
toDbTerm env (Record m) = map DbRecord $ sequenceSortedMap $ assert_total ((map $ toDbTerm env) m)
toDbTerm env (RecordProj t l) = map ((flip DbRecordProj) l) $ toDbTerm env t
toDbTerm env (Variant l t) = map (DbVariant l) $ toDbTerm env t
toDbTerm env (VariantMatch t m) = do dt <- toDbTerm env t
                                     let m' = assert_total $ map convert m
                                     dm <- sequenceSortedMap m'
                                     pure $ DbVariantMatch dt dm
                                  where convert : (String, Term) -> Either String (String, DbTerm)
                                        convert (l, t) = do dt <- toDbTerm (addNewBindingToEnv l env) t
                                                            pure (l, dt)
toDbTerm env (PrimMatch t m) = do dt <- toDbTerm env t
                                  let m' = assert_total $ map (toDbTerm env) m
                                  dm <- sequenceSortedMap m'
                                  pure $ DbPrimMatch dt dm

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
reduce i (DbFix name ty t) = DbFix name ty (reduce (S i) t)
reduce i (DbBinop op t1 t2) = DbBinop op (reduce i t1) (reduce i t2)
reduce i (DbRecord m) = DbRecord $ assert_total (map (reduce i) m)
reduce i (DbRecordProj t l) = DbRecordProj (reduce i t) l
reduce i (DbVariant l t) = DbVariant l (reduce i t)
reduce i (DbVariantMatch t m) = DbVariantMatch (reduce i t) $ assert_total (map (applyToSecond $ assert_total (reduce $ S i))) m
reduce i (DbPrimMatch t m) = DbPrimMatch (reduce i t) $ assert_total $ map (reduce i) m
reduce i t = t

substitute : Nat -> DbTerm -> DbTerm -> DbTerm
substitute i s dbVar@(DbVar k) = if i == k then s else dbVar
substitute i s (DbAbs str t ty) = DbAbs str (substitute (S i) (raise Z s) t) ty
substitute i s (DbApp t1 t2) = DbApp (substitute i s t1) (substitute i s t2)
substitute i s (DbLet name s' t) = DbLet name (substitute i s s') (substitute (S i) (raise Z s) t)
substitute i s (DbFix name ty t) = DbFix name ty (substitute (S i) (raise Z s) t)
substitute i s (DbBinop op t1 t2) = DbBinop op (substitute i s t1) (substitute i s t2)
substitute i s (DbRecord m) = DbRecord $ assert_total (map (substitute i s) m)
substitute i s (DbRecordProj t l) = DbRecordProj (substitute i s t) l
substitute i s (DbVariant l t) = DbVariant l $ substitute i s t
substitute i s (DbVariantMatch t m) = DbVariantMatch (substitute i s t) $ assert_total (map (applyToSecond (substitute (S i) (raise Z s))) m)
substitute i s (DbPrimMatch t m) = DbPrimMatch (substitute i s t) $ assert_total $ map (substitute i s) m
substitute i s t = t

export
isNormal : DbTerm -> Bool
isNormal (DbPrim _) = True
isNormal (DbAbs _ _ _) = True
isNormal (DbRecord m) = assert_total (all isNormal $ values m)
isNormal (DbVariant _ t) = isNormal t
isNormal _ = False

findTypeBinop : Op -> PrimTy -> PrimTy -> Either String PrimTy
findTypeBinop Add PrimTyInteger PrimTyInteger = Right PrimTyInteger
findTypeBinop Add PrimTyDouble PrimTyDouble = Right PrimTyDouble
findTypeBinop Add PrimTyString PrimTyString = Right PrimTyString
findTypeBinop Sub PrimTyInteger PrimTyInteger = Right PrimTyInteger
findTypeBinop Sub PrimTyDouble PrimTyDouble = Right PrimTyDouble
findTypeBinop Mul PrimTyInteger PrimTyInteger = Right PrimTyInteger
findTypeBinop Mul PrimTyDouble PrimTyDouble = Right PrimTyDouble
findTypeBinop Div PrimTyInteger PrimTyInteger = Right PrimTyInteger
findTypeBinop Div PrimTyDouble PrimTyDouble = Right PrimTyDouble
findTypeBinop And PrimTyBool PrimTyBool = Right PrimTyBool
findTypeBinop Or PrimTyBool PrimTyBool = Right PrimTyBool
findTypeBinop Equal PrimTyBool PrimTyBool = Right PrimTyBool
findTypeBinop Equal PrimTyInteger PrimTyInteger = Right PrimTyBool
findTypeBinop Equal PrimTyDouble PrimTyDouble = Right PrimTyBool
findTypeBinop Equal PrimTyString PrimTyString = Right PrimTyBool
findTypeBinop op ty1 ty2 = Left $ "Mismatched type: " ++ show ty1 ++ show op ++ show ty2

evaluateBinopP : Op -> PrimVal -> PrimVal -> Either String PrimVal
evaluateBinopP Add (PrimValInteger i1) (PrimValInteger i2) = Right $ PrimValInteger $ i1 + i2
evaluateBinopP Add (PrimValDouble d1) (PrimValDouble d2) = Right $ PrimValDouble $ d1 + d2
evaluateBinopP Add (PrimValString s1) (PrimValString s2) = Right $ PrimValString $ s1 ++ s2
evaluateBinopP Sub (PrimValInteger i1) (PrimValInteger i2) = Right $ PrimValInteger $ i1 - i2
evaluateBinopP Sub (PrimValDouble d1) (PrimValDouble d2) = Right $ PrimValDouble $ d1 - d2
evaluateBinopP Mul (PrimValInteger i1) (PrimValInteger i2) = Right $ PrimValInteger $ i1 * i2
evaluateBinopP Mul (PrimValDouble d1) (PrimValDouble d2) = Right $ PrimValDouble $ d1 * d2
evaluateBinopP Div (PrimValInteger i1) (PrimValInteger i2) = if i2 == 0
                                                                then Left $ "Cannot divide by zero"
                                                                else Right $ PrimValInteger $ assert_total $ i1 `div` i2
evaluateBinopP Div (PrimValDouble d1) (PrimValDouble d2) = Right $ PrimValDouble $ d1 / d2
evaluateBinopP Equal (PrimValBool x) (PrimValBool y) = Right $ PrimValBool $ x == y
evaluateBinopP Equal (PrimValInteger x) (PrimValInteger y) = Right $ PrimValBool $ x == y
evaluateBinopP Equal (PrimValDouble x) (PrimValDouble y) = Right $ PrimValBool $ x == y
evaluateBinopP Equal (PrimValString x) (PrimValString y) = Right $ PrimValBool $ x == y
evaluateBinopP And (PrimValBool x) (PrimValBool y) = Right $ PrimValBool $ x && y
evaluateBinopP Or (PrimValBool x) (PrimValBool y) = Right $ PrimValBool $ x || y
evaluateBinopP op pv1 pv2 = Left $ "Invalid operation " ++ show pv1 ++ show op ++ show pv2

evaluateBinop : Op -> DbTerm -> DbTerm -> DbTerm
evaluateBinop op t1@(DbPrim pv1) t2@(DbPrim pv2) = case evaluateBinopP op pv1 pv2 of
                                                        Left msg => DbBinop op t1 t2
                                                        Right pv => DbPrim pv
evaluateBinop op t1 t2  = DbBinop op t1 t2

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
  then reduce Z $ substitute Z s t
  else DbLet name (evaluate env s) t
evaluate env f@(DbFix name ty t) = reduce Z $ substitute Z f t
evaluate env (DbBinop op t1 t2) =
  if isNormal t1
  then if isNormal t2
       then evaluateBinop op t1 t2
       else DbBinop op t1 (evaluate env t2)
  else DbBinop op (evaluate env t1) t2
evaluate env ori@(DbModop mod t) =
  if isNormal t
     then case (mod, t) of
               (Not, (DbPrim (PrimValBool b))) => DbPrim $ PrimValBool $ not b
               (Negate, (DbPrim (PrimValInteger i))) => DbPrim $ PrimValInteger $ -i
               (Negate, (DbPrim (PrimValDouble d))) => DbPrim $ PrimValDouble $ -d
               _ => ori
     else DbModop mod (evaluate env t)
evaluate env (DbRecord m) = DbRecord $ assert_total (map (evaluate env) m)
evaluate env (DbRecordProj t l) = if isNormal t
                                     then case t of
                                          (DbRecord m) => maybe t id (lookup l m)
                                          _ => t
                                     else DbRecordProj (evaluate env t) l
evaluate env (DbVariant l t) = DbVariant l $ evaluate env t
evaluate env ori@(DbVariantMatch t m) =
  if isNormal t
     then case t of
               (DbVariant l s) => case lookup l m of
                                       Nothing => ori
                                       (Just (_, t)) => reduce Z $ substitute Z s t
               _ => ori
     else DbVariantMatch (evaluate env t) m
evaluate env ori@(DbPrimMatch t m) =
  if isNormal t
     then case t of
                (DbPrim pv) => case lookup pv m of
                                    Nothing => ori -- If exception is supported, here it should be an exception reporting missing branch for pv
                                    (Just bt) => bt
                _ => ori
     else DbPrimMatch (evaluate env t) m
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
                            Nothing => Left ("Index " ++ (show k) ++ " cannot be found in env " ++ show env)
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
toTerm env (DbFix name ty dt) = do t <- toTerm (name::env) dt
                                   Right $ Fix name ty t
toTerm env (DbPrim pv) = Right $ Prim pv
toTerm env (DbBinop op dt1 dt2) = do t1 <- toTerm env dt1
                                     t2 <- toTerm env dt2
                                     Right $ Binop op t1 t2
toTerm env (DbModop mod dt) = map (Modop mod) (toTerm env dt)
toTerm env (DbRecord m) = map Record $ sequenceSortedMap $ assert_total (map (toTerm env) m)
toTerm env (DbRecordProj t l) = [| RecordProj (toTerm env t) (pure l) |]
toTerm env (DbVariant l t) = map (Variant l) $ toTerm env t
toTerm env (DbVariantMatch t m) = [| VariantMatch (toTerm env t) (sequenceSortedMap $ assert_total (map convert m)) |]
                                  where convert : (String, DbTerm) -> Either String (String, Term)
                                        convert (l, dt) = do let name = findNewName env l
                                                             t <- toTerm (name :: env) dt
                                                             pure (l, t)
toTerm env (DbPrimMatch t m) = [| PrimMatch (toTerm env t) (sequenceSortedMap $ assert_total (map (toTerm env) m)) |]

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
findType tys (DbFix name ty t) = do ty' <- findType (ty::tys) t
                                    if ty' == ty
                                       then Right ty
                                       else Left "Encountered 'fix' with self contradictory type."
findType tys (DbPrim x) = Right $ TyPrimitive $ findPrimType x
findType tys (DbBinop op t1 t2) = do ty1 <- findType tys t1
                                     ty2 <- findType tys t2
                                     case (ty1, ty2) of
                                          (TyPrimitive pty1, TyPrimitive pty2) => map TyPrimitive $ findTypeBinop op pty1 pty2
                                          _ => Left $ "Type mismatch: " ++ show ty1 ++ show op ++ show ty2
findType tys (DbRecord m) = map TyRecord $ sequenceSortedMap $ assert_total $ map (findType tys) m
findType tys (DbRecordProj t l) = do ty <- findType tys t
                                     case ty of
                                          (TyRecord m) => case lookup l m of
                                                               Nothing => Left $ show ty ++ "does not have field " ++ l
                                                               (Just ty) => Right ty
                                          _ => Left "Projection can only applied on record."
findType tys (DbVariant l t) = [| (TyVariant . fromList . (\ty => [(l, ty)])) (findType tys t) |]
findType tys (DbVariantMatch t bm) = do TyVariant tym <- findType tys t
                                        | _ => Left "Expect to match variant."
                                        btys <-  zipMap bm tym
                                        foldlM findSuperType TyBottom btys
                                     where zipMap : SortedMap String (String, DbTerm) -> SortedMap String Ty -> Either String (List Ty)
                                           -- Here we simply allow additional branches that the matched type does not contain
                                           zipMap bm tym = sequence $ map convert $ toList tym
                                           where convert : (String, Ty) -> Either String Ty
                                                 convert (l, ty) = do let Just (_, t) = lookup l bm
                                                                        | Nothing => Left ("Missing branch for " ++ l)
                                                                      findType (ty::tys) t
findType tys (DbModop mod t) = do ty <- findType tys t
                                  case (mod, ty) of
                                       (Not, (TyPrimitive PrimTyBool)) => Right ty
                                       (Negate, (TyPrimitive PrimTyInteger)) => Right ty
                                       (Negate, (TyPrimitive PrimTyDouble)) => Right ty
                                       _ => Left $ "Cannot negate " ++ show ty

findType tys (DbPrimMatch t bm) = do TyPrimitive pty <- findType tys t
                                     | _ => Left "Expect to match primitive"
                                     _ <- allTheSame pty $ map findPrimType (keys bm)
                                     btys <- sequence $ assert_total $ map (findType tys) (values bm)
                                     foldlM findSuperType TyBottom btys
                                  where allTheSame : PrimTy -> List PrimTy -> Either String PrimTy
                                        allTheSame pty [] = Right pty
                                        allTheSame pty (x :: xs) = if pty == x
                                                                      then allTheSame pty xs
                                                                      else Left $ "Mismatched branch type: " ++ show pty ++ " and " ++ show x


export
Show Term where
  show (Var n) = n
  show (Abs n t ty) = "(\\" ++ n ++ ":" ++ show ty ++ "." ++ show t ++ ")"
  show (App t1 t2) = show t1 ++ " " ++ show t2
  show (Let name s t) = "let " ++ name ++ "=" ++ show s ++ " in " ++ show t
  show (Fix name ty t) = "fix " ++ name ++ ":" ++ show ty ++ "." ++ show t
  show (Prim pv) = show pv
  show (Binop op t1 t2) = "(" ++ show t1 ++ show op ++ show t2 ++ ")"
  show (Modop mod t) = show mod ++ show t
  show (Record m) = "{" ++ joinString "," (assert_total (map showField $ toList m)) ++ "}"
                    where showField : (String, Term) -> String
                          showField (l, t) = l ++ " " ++ show t
  show (RecordProj t l) = show t ++ "." ++ l
  show (Variant l t) = "<" ++ l ++ " " ++ show t ++ ">"
  show (VariantMatch t m) = "match " ++ show t ++ " {" ++ joinString "," (assert_total (map showBranch $ toList m)) ++ "}"
                           where showBranch : (String, (String, Term)) -> String
                                 showBranch (l, (x, t)) = l ++ " " ++ x ++ " => " ++ show t
  show (PrimMatch t m) = "match " ++ show t ++ " {" ++ joinString "," (assert_total (map showBranch $ toList m)) ++ "}"
                           where showBranch : (PrimVal, Term) -> String
                                 showBranch (pv, t) = show pv ++ " " ++ " => " ++ show t

