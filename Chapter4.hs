-- "Type Theory and Formal Proof" by Rob Nederpelt and Herman Geuvers
-- Chapter 4
-- Types dependent on types


data Box = BoxBox
           deriving (Show, Eq)

data Kind = KindStar            -- *
          | KindArrow Kind Kind -- Kind -> Kind
            deriving (Show, Eq)

data Type = TypeVar String           -- V
          | TypeArrow Type Type      -- Type -> Type
          | TypeApp Type Type        -- Type Type
          | TypeAbs String Kind Type -- \lambda V : Kind . Type
            deriving (Show, Eq)

data Term = TermVar String           -- V'
          | TermApp Term Term        -- Term Term
          | TermAbs String Type Term -- \lambda V' : Type . Term
            deriving (Show, Eq)


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
* -> * : Box
* -> (* -> *) : Box

(form) (s = box)
\Gamma |- A : s  \Gamma |- B : s
--------------------------------
      \Gamma |- A -> B : s
-}
getBox gamma (KindArrow a b) =
  let s = BoxBox in do
    s1 <- getBox gamma a
    s2 <- getBox gamma b
    if s1 == s && s2 == s then return s else Nothing


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
\alpha -> \sigma : *
\beta -> (\sigma -> \alpha) : *

(form) (s = star)
\Gamma |- A : s  \Gamma |- B : s
--------------------------------
      \Gamma |- A -> B : s
-}
getKind gamma (TypeArrow a b) =
  let s = KindStar in do
    s1 <- getKind gamma a
    s2 <- getKind gamma b
    if s1 == s && s2 == s then return s else Nothing

{-
(appl) (type)
\Gamma |- M : A -> B  \Gamma |- N : A
-------------------------------------
          \Gamma |- M N : B
-}
getKind gamma (TypeApp m n) = do
  ki_m <- getKind gamma m
  ki_n <- getKind gamma n
  case ki_m of
    KindArrow a b -> if ki_n == a then return b else Nothing
    _ -> Nothing

{-
(abst) (s = box)
\Gamma, x : A |- M : B  \Gamma |- A -> B : s
--------------------------------------------
    \Gamma |- \lambda x : A . M : A -> B
-}
getKind gamma (TypeAbs x a m) =
  let gamma' = TypeDeclaration (x, a) : gamma in do
    b <- getKind gamma' m
    s <- getBox gamma (KindArrow a b)
    if s == BoxBox then return (KindArrow a b) else Nothing


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
\Gamma |- M : A -> B  \Gamma |- N : A
-------------------------------------
          \Gamma |- M N : B
-}
getType gamma (TermApp m n) = do
  ty_m <- getType gamma m
  ty_n <- getType gamma n
  case ty_m of
    TypeArrow a b -> if ty_n == a then return b else Nothing
    _ -> Nothing

{-
(abst) (s = star)
\Gamma, x : A |- M : B  \Gamma |- A -> B : s
--------------------------------------------
    \Gamma |- \lambda x : A . M : A -> B
-}
getType gamma (TermAbs x a m) =
  let gamma' = TermDeclaration (x, a) : gamma in do
    b <- getType gamma' m
    s <- getKind gamma (TypeArrow a b)
    if s == KindStar then return (TypeArrow a b) else Nothing


{-
Examples:

*Main> getKind [] (TypeAbs "a" KindStar (TypeArrow (TypeVar "a") (TypeVar "a")))
Just (KindArrow KindStar KindStar)

*Main> getKind [] (TypeAbs "a" KindStar (TypeAbs "b" KindStar (TypeArrow (TypeVar "a") (TypeVar "b"))))
Just (KindArrow KindStar (KindArrow KindStar KindStar))

*Main> getKind [] (TypeAbs "a" (KindArrow KindStar KindStar) (TypeVar "a"))
Just (KindArrow (KindArrow KindStar KindStar) (KindArrow KindStar KindStar))

*Main> getType [(TermDeclaration ("x", (TypeVar "a"))), (TypeDeclaration ("a", KindStar))] (TermVar "x")
Just (TypeVar "a")

*Main> getKind [(TermDeclaration ("x", (TypeVar "a"))), (TypeDeclaration ("a", KindStar))] (TypeVar "a")
Just KindStar

*Main> getKind [(TypeDeclaration ("b", KindStar)), (TypeDeclaration ("a", KindStar))] (TypeVar "a")
Just KindStar

*Main> getKind [(TypeDeclaration ("b", KindStar)), (TypeDeclaration ("a", KindStar))] (TypeVar "b")
Just KindStar

*Main> getBox [(TypeDeclaration ("a", KindStar))] KindStar
Just BoxBox

*Main> getBox [(TypeDeclaration ("a", KindStar))] (KindArrow KindStar KindStar)
Just BoxBox

*Main> getKind [(TypeDeclaration ("b", KindStar))] (TypeApp (TypeAbs "a" KindStar (TypeArrow (TypeVar "a") (TypeVar "a"))) (TypeVar "b"))
Just KindStar
-}

