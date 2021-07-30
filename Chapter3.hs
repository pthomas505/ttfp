-- "Type Theory and Formal Proof" by Rob Nederpelt and Herman Geuvers
-- Chapter 3
-- Second order typed lambda calculus


import Data.Set
import Data.Map


data Kind = KindStar -- *
            deriving (Show, Eq)

data Type = TypeVar String          -- V
          | TypeArrow Type Type     -- Type -> Type
          | TypePi String Kind Type -- Pi V : * . Type
            deriving (Show, Eq)

data Term = TermVar String            -- V'
          | TermApp Term Term         -- Term Term
          | TermAbs String Type Term  -- \lambda V' : Type . Term
          | TermApp2 Term Type        -- Term Type
          | TermAbs2 String Kind Term -- /\ V : * . Term
            deriving (Show, Eq)


getFreeTypeVariableSet :: Type -> Data.Set.Set String
getFreeTypeVariableSet (TypeVar x) = Data.Set.singleton x
getFreeTypeVariableSet (TypeArrow m n) =
  Data.Set.union (getFreeTypeVariableSet m) (getFreeTypeVariableSet n)
getFreeTypeVariableSet (TypePi x _ m) =
  Data.Set.difference (getFreeTypeVariableSet m) (Data.Set.singleton x)


-- substitute m x n = m [ x := n ]
substitute :: Type -> String -> Type -> Type
substitute e@(TypeVar y) x n = if x == y then n else e
substitute (TypeArrow p q) x n = TypeArrow (substitute p x n) (substitute q x n)
substitute e@(TypePi y q p) x n
  | x == y = e
  | x /= y && x `Data.Set.notMember` (getFreeTypeVariableSet e) = e
  | x /= y && y `Data.Set.notMember` (getFreeTypeVariableSet n) =
      TypePi y q (substitute p x n)
  | otherwise = error "bad input"


data Declaration = TermDeclaration (String, Type)
                 | TypeDeclaration (String, Kind)

type Context = [Declaration]

getDomain :: Context -> [String]
getDomain [] = []
getDomain (TermDeclaration (x, _) : gamma) = x : (getDomain gamma)
getDomain (TypeDeclaration (alpha, _) : gamma) = alpha : (getDomain gamma)

getTermDomain :: Context -> [String]
getTermDomain [] = []
getTermDomain (TermDeclaration (x, _) : gamma) = x : (getTermDomain gamma)
getTermDomain (_ : gamma) = getTermDomain gamma

getTypeDomain :: Context -> [String]
getTypeDomain [] = []
getTypeDomain (TypeDeclaration (alpha, _) : gamma) = alpha : (getTypeDomain gamma)
getTypeDomain (_ : gamma) = getTypeDomain gamma

isContext :: Context -> Bool
isContext [] = True
isContext (TermDeclaration (x, rho) : gamma) =
  isContext gamma &&
  (getFreeTypeVariableSet rho) `Data.Set.isSubsetOf` Data.Set.fromList (getTypeDomain gamma) &&
  x `notElem` (getDomain gamma)
isContext (TypeDeclaration (alpha, _) : gamma) =
  isContext gamma &&
  alpha `notElem` (getDomain gamma)

getTermDeclarationList :: Context -> [(String, Type)]
getTermDeclarationList [] = []
getTermDeclarationList ((TermDeclaration d) : gamma) = d : (getTermDeclarationList gamma)
getTermDeclarationList (_ : gamma) = getTermDeclarationList gamma

getTypeDeclarationList :: Context -> [(String, Kind)]
getTypeDeclarationList [] = []
getTypeDeclarationList ((TypeDeclaration d) : gamma) = d : (getTypeDeclarationList gamma)
getTypeDeclarationList (_ : gamma) = getTypeDeclarationList gamma


getKind :: Context -> Type -> Maybe Kind
{-
(form)
\Gamma |- B : * if \Gamma is a \lambda2 context, B \in T2 and all free type variables in B are declared in \Gamma.
-}
getKind gamma b =
  if isContext gamma &&
    (getFreeTypeVariableSet b) `Data.Set.isSubsetOf` (Data.Set.fromList (getTypeDomain gamma))
  then return KindStar
  else Nothing


getType :: Context -> Term -> Maybe Type

{-
(var)
\Gamma |- x : \sigma if \Gamma is a \lambda2 context and x : \sigma \in Gamma
-}
getType gamma (TermVar x) =
  if isContext gamma
  then do
    sigma <- Data.Map.lookup x (Data.Map.fromList (getTermDeclarationList gamma))
    return sigma
  else Nothing

{-
(appl)
\Gamma |- M : \sigma -> \tau  \Gamma |- N : \sigma
--------------------------------------------------
               \Gamma |- M N : \tau
-}
getType gamma (TermApp m n) =
  if isContext gamma
  then do
    ty_m <- getType gamma m
    ty_n <- getType gamma n
    case ty_m of
      TypeArrow sigma tau -> if ty_n == sigma then return tau else Nothing
      _ -> Nothing
  else Nothing

{-
(abst)
         \Gamma, x : \sigma |- M : \tau
-------------------------------------------------
\Gamma |- \lambda x : \sigma . M : \sigma -> \tau
-}
getType gamma (TermAbs x sigma m) =
  let gamma' = TermDeclaration (x, sigma) : gamma in
    if isContext gamma'
    then do
      tau <- getType gamma' m
      return (TypeArrow sigma tau)
    else Nothing

{-
(appl_2)
\Gamma |- M : (Pi \alpha : * . A)  \Gamma |- B : *
--------------------------------------------------
          \Gamma |- M B : A [\alpha := B]
-}
getType gamma (TermApp2 m b) =
  if isContext gamma
  then do
    ty_m <- getType gamma m
    ki_b <- getKind gamma b
    case ty_m of
      TypePi alpha _ a -> if ki_b == KindStar
                          then return (substitute a alpha b)
                          else Nothing
      _ -> Nothing
  else Nothing

{-
(abst_2)
            \Gamma, \alpha : * |- M : A
----------------------------------------------------
\Gamma |- \lambda \alpha : * . M : Pi \alpha : * . A
-}
getType gamma (TermAbs2 alpha k m) =
  let gamma' = TypeDeclaration (alpha, k) : gamma in
    if isContext gamma'
    then do
      a <- getType gamma' m
      return (TypePi alpha k a)
    else Nothing


{-
Example:

*Main> getType [] (TermAbs2 "alpha" KindStar (TermAbs "f" (TypeArrow (TypeVar "alpha") (TypeVar "alpha")) (TermAbs "x" (TypeVar "alpha") (TermApp (TermVar "f") (TermApp (TermVar "f") (TermVar "x"))))))
Just (TypePi "alpha" KindStar (TypeArrow (TypeArrow (TypeVar "alpha") (TypeVar "alpha")) (TypeArrow (TypeVar "alpha") (TypeVar "alpha"))))
-}

