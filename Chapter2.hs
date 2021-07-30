-- "Type Theory and Formal Proof" by Rob Nederpelt and Herman Geuvers
-- Chapter 2
-- Simply typed lambda calculus


import Data.Map


data Type = TypeVar String      -- V
          | TypeArrow Type Type -- Type -> Type
            deriving (Show, Eq)

data Term = TermVar String           -- V'
          | TermApp Term Term        -- Term Term
          | TermAbs String Type Term -- \lambda V' : Type . Term
            deriving (Show, Eq)


type Declaration = (String, Type)

type Context = [Declaration]


getSubjectList :: Context -> [String]
getSubjectList [] = []
getSubjectList ((x, _) : gamma) = x : (getSubjectList gamma)

isUnique :: [String] -> Bool
isUnique [] = True
isUnique (x : xs) = x `notElem` xs && isUnique xs

isContext :: Context -> Bool
isContext = isUnique . getSubjectList


getType :: Context -> Term -> Maybe Type

{-
(var)
\Gamma |- x : \sigma if x : \sigma \in Gamma
-}
getType gamma (TermVar x) =
  if isContext gamma
  then Data.Map.lookup x (Data.Map.fromList gamma)
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
  let gamma' = (x, sigma) : gamma in
    if isContext gamma'
    then do
      tau <- getType gamma' m
      return (TypeArrow sigma tau)
    else Nothing

