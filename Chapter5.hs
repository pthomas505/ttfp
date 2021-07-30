-- "Type Theory and Formal Proof" by Rob Nederpelt and Herman Geuvers
-- Chapter 5
-- Types dependent on terms


import Data.Set


data Box = BoxBox
           deriving (Show, Eq)

data Kind = KindStar
          | KindPi String Type Kind  -- \Pi V' : Type . Kind
            deriving (Show, Eq)

data Type = TypeVar String           -- V
          | TypeApp Type Term        -- Type Term
          | TypePi String Type Type  -- \Pi V' : Type . Type
          | TypeAbs String Type Type -- /\  V' : Type . Type
            deriving (Show, Eq)

data Term = TermVar String           -- V'
          | TermApp Term Term        -- Term Term
          | TermAbs String Type Term -- \lambda V' : Type . Term
            deriving (Show, Eq)


getFreeTermVariableSetInType :: Type -> Data.Set.Set String
getFreeTermVariableSetInType (TypeVar _) = Data.Set.empty
getFreeTermVariableSetInType (TypeApp m n) =
  Data.Set.union (getFreeTermVariableSetInType m) (getFreeTermVariableSetInTerm n)
getFreeTermVariableSetInType (TypePi x _ n) =
  Data.Set.difference (getFreeTermVariableSetInType n) (Data.Set.singleton x)
getFreeTermVariableSetInType (TypeAbs x _ n) =
  Data.Set.difference (getFreeTermVariableSetInType n) (Data.Set.singleton x)

getFreeTermVariableSetInTerm :: Term -> Data.Set.Set String
getFreeTermVariableSetInTerm (TermVar x) = Data.Set.singleton x
getFreeTermVariableSetInTerm (TermApp m n) =
  Data.Set.union (getFreeTermVariableSetInTerm m) (getFreeTermVariableSetInTerm n)
getFreeTermVariableSetInTerm (TermAbs x _ n) =
  Data.Set.difference (getFreeTermVariableSetInTerm n) (Data.Set.singleton x)


-- substituteInType m x n = m [ x := n ]
substituteInType :: Type -> String -> Term -> Type
substituteInType e@(TypeVar _) _ _ = e
substituteInType (TypeApp p q) x n = TypeApp (substituteInType p x n) (substituteInTerm q x n)
substituteInType e@(TypePi y q p) x n
  | x == y = e
  | x /= y && x `Data.Set.notMember` (getFreeTermVariableSetInType e) = e
  | x /= y && y `Data.Set.notMember` (getFreeTermVariableSetInTerm n) =
      TypePi y q (substituteInType p x n)
  | otherwise = error "bad input"
substituteInType e@(TypeAbs y q p) x n
  | x == y = e
  | x /= y && x `Data.Set.notMember` (getFreeTermVariableSetInType e) = e
  | x /= y && y `Data.Set.notMember` (getFreeTermVariableSetInTerm n) =
      TypeAbs y q (substituteInType p x n)
  | otherwise = error "bad input"

-- substituteInTerm m x n = m [ x := n ]
substituteInTerm :: Term -> String -> Term -> Term
substituteInTerm e@(TermVar y) x n = if x == y then n else e
substituteInTerm (TermApp p q) x n = TermApp (substituteInTerm p x n) (substituteInTerm q x n)
substituteInTerm e@(TermAbs y q p) x n
  | x == y = e
  | x /= y && x `Data.Set.notMember` (getFreeTermVariableSetInTerm e) = e
  | x /= y && y `Data.Set.notMember` (getFreeTermVariableSetInTerm n) =
      TermAbs y q (substituteInTerm p x n)
  | otherwise = error "bad input"


data Declaration = TermDeclaration (String, Type)
                 | TypeDeclaration (String, Kind)

type Context = [Declaration]

getDomain :: Context -> [String]
getDomain [] = []
getDomain (TermDeclaration (x, _) : gamma) = x : (getDomain gamma)
getDomain (TypeDeclaration (alpha, _) : gamma) = alpha : (getDomain gamma)


-- getBox

getBox :: Context -> Kind -> Maybe Box

{-
(sort)
\empty |- * : Box
-}
getBox [] KindStar = return BoxBox

{-
(weak) (s = box) (A = star)
\Gamma |- A : B  \Gamma |- C : s
--------------------------------  if x \notin \Gamma
     \Gamma, x : C |- A : B
-}
getBox (TypeDeclaration (x, c) : gamma) KindStar =
  let a = KindStar in do
    b <- getBox gamma a
    s <- getBox gamma c
    if s == BoxBox && x `notElem` (getDomain gamma)
    then return b
    else Nothing

{-
(weak) (s = star) (A = star)
\Gamma |- A : B  \Gamma |- C : s
--------------------------------  if x \notin \Gamma
     \Gamma, x : C |- A : B
-}
getBox (TermDeclaration (x, c) : gamma) KindStar =
  let a = KindStar in do
    b <- getBox gamma a
    s <- getKind gamma c
    if s == KindStar && x `notElem` (getDomain gamma)
    then return b
    else Nothing

{-
(form) (s = box)
\Gamma |- A : *  \Gamma, x : A |- B : s
---------------------------------------
      \Gamma |- Pi x : A . B : s
-}
getBox gamma (KindPi x a b) = -- a = Type, b = Kind
  let gamma' = TermDeclaration (x, a) : gamma in do
    ki_a <- getKind gamma a
    s <- getBox gamma' b
    if ki_a == KindStar && s == BoxBox then return s else Nothing


-- getKind

getKind :: Context -> Type -> Maybe Kind

{-
(var) (s = box)
   \Gamma |- C : s
----------------------  if x \notin \Gamma
\Gamma, x : C |- x : C
-}

{-
(weak) (s = box)
\Gamma |- A : B  \Gamma |- C : s
--------------------------------  if x \notin \Gamma
     \Gamma, x : C |- A : B
-}

{-
If x == a then the var rule applies and it is used.
If x != a then the var rule does not apply and the weak rule is used instead.
-}

getKind (TypeDeclaration (x, c) : gamma) (TypeVar a) = do
  s <- getBox gamma c
  if s == BoxBox && x `notElem` (getDomain gamma) then
    if x == a then return c else getKind gamma (TypeVar a)
  else Nothing

{-
(weak) (s = star)
\Gamma |- A : B  \Gamma |- C : s
--------------------------------  if x \notin \Gamma
     \Gamma, x : C |- A : B
-}
getKind (TermDeclaration (x, c) : gamma) (TypeVar a) = do
  s <- getKind gamma c
  if s == KindStar && x `notElem` (getDomain gamma)
  then getKind gamma (TypeVar a)
  else Nothing

getKind [] (TypeVar _) = Nothing


{-
(form) (s = star)
\Gamma |- A : *  \Gamma, x : A |- B : s
---------------------------------------
      \Gamma |- Pi x : A . B : s
-}
getKind gamma (TypePi x a b) = -- a = Type, b = Type
  let gamma' = TermDeclaration (x, a) : gamma in do
    ki_a <- getKind gamma a
    s <- getKind gamma' b
    if ki_a == KindStar && s == KindStar then return s else Nothing

{-
(appl) (type)
\Gamma |- M : Pi x : A . B  \Gamma |- N : A
-------------------------------------------
        \Gamma |- M N : B [x := N]
-}
getKind gamma (TypeApp m n) = do -- m = Type, n = Term
  ki_m <- getKind gamma m
  ty_n <- getType gamma n
  case ki_m of
    KindPi _ a b -> if ty_n == a then return b else Nothing
    _ -> Nothing

{-
(abst) (s = box)
\Gamma, x : A |- M : B  \Gamma |- Pi x : A . B : s
--------------------------------------------------
    \Gamma |- \lambda x : A . M : Pi x : A . B
-}
getKind gamma (TypeAbs x a m) = -- a = Type, m = Type
  let gamma' = TermDeclaration (x, a) : gamma in do
    b <- getKind gamma' m
    s <- getBox gamma (KindPi x a b)
    if s == BoxBox then return (KindPi x a b) else Nothing


-- getType

getType :: Context -> Term -> Maybe Type

{-
(var) (s = star)
   \Gamma |- C : s
----------------------  if x \notin \Gamma
\Gamma, x : C |- x : C
-}

{-
(weak) (s = star)
\Gamma |- A : B  \Gamma |- C : s
--------------------------------  if x \notin \Gamma
     \Gamma, x : C |- A : B
-}

{-
If x == a then the var rule applies and it is used.
If x != a then the var rule does not apply and the weak rule is used instead.
-}

getType (TermDeclaration (x, c) : gamma) (TermVar a) = do
  s <- getKind gamma c
  if s == KindStar && x `notElem` (getDomain gamma) then
    if x == a then return c else getType gamma (TermVar a)
  else Nothing

{-
(weak) (s = box)
\Gamma |- A : B  \Gamma |- C : s
--------------------------------  if x \notin \Gamma
     \Gamma, x : C |- A : B
-}
getType (TypeDeclaration (x, c) : gamma) (TermVar a) = do
  s <- getBox gamma c
  if s == BoxBox && x `notElem` (getDomain gamma)
  then getType gamma (TermVar a)
  else Nothing

getType [] (TermVar _) = Nothing


{-
(appl) (term)
\Gamma |- M : Pi x : A . B  \Gamma |- N : A
-------------------------------------------
        \Gamma |- M N : B [x := N]
-}
getType gamma (TermApp m n) = do -- m = Term, n = Term
  ty_m <- getType gamma m
  ty_n <- getType gamma n
  case ty_m of
    TypePi x a b -> if ty_n == a then return (substituteInType b x n) else Nothing
    _ -> Nothing

{-
(abst) (s = star)
\Gamma, x : A |- M : B  \Gamma |- Pi x : A . B : s
--------------------------------------------------
    \Gamma |- \lambda x : A . M : Pi x : A . B
-}
getType gamma (TermAbs x a m) = -- a = Type, m = Term
  let gamma' = TermDeclaration (x, a) : gamma in do
    b <- getType gamma' m
    s <- getKind gamma (TypePi x a b)
    if s == KindStar then return (TypePi x a b) else Nothing


{-
Examples:

*Main> getType [(TypeDeclaration ("P", (KindPi "x" (TypeVar "A") KindStar))), (TypeDeclaration ("A", KindStar))] (TermAbs "x" (TypeVar "A") (TermAbs "y" (TypeApp (TypeVar "P") (TermVar "x")) (TermVar "y")))
Just (TypePi "x" (TypeVar "A") (TypePi "y" (TypeApp (TypeVar "P") (TermVar "x")) (TypeApp (TypeVar "P") (TermVar "x"))))
-}

