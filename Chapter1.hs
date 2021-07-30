-- "Type Theory and Formal Proof" by Rob Nederpelt and Herman Geuvers
-- Chapter 1
-- Untyped lambda calculus


import Data.List
import Data.Set


data Term = TermVar String      -- V
          | TermApp Term Term   -- Term Term
          | TermAbs String Term -- \lambda V . Term
            deriving (Show, Eq)


getSubTermList :: Term -> [Term]
getSubTermList e@(TermVar _) = [e]
getSubTermList e@(TermApp m n) = (getSubTermList m) ++ (getSubTermList n) ++ [e]
getSubTermList e@(TermAbs _ m) = (getSubTermList m) ++ [e]

getProperSubTermList :: Term -> [Term]
getProperSubTermList t = Data.List.delete t (getSubTermList t)


getFreeVariableSet :: Term -> Data.Set.Set String
getFreeVariableSet (TermVar x) = Data.Set.singleton x
getFreeVariableSet (TermApp m n) =
  Data.Set.union (getFreeVariableSet m) (getFreeVariableSet n)
getFreeVariableSet (TermAbs x m) =
  Data.Set.difference (getFreeVariableSet m) (Data.Set.singleton x)

isClosedTerm :: Term -> Bool
isClosedTerm t = Data.Set.null (getFreeVariableSet t)


getBindingVariableSet :: Term -> Data.Set.Set String
getBindingVariableSet (TermVar _) = Data.Set.empty
getBindingVariableSet (TermApp m n) =
  Data.Set.union (getBindingVariableSet m) (getBindingVariableSet n)
getBindingVariableSet (TermAbs x m) =
  Data.Set.union (getBindingVariableSet m) (Data.Set.singleton x)


-- replaceFree u v m = replaces every free occurrence of u in m by v.
replaceFree :: String -> String -> Term -> Term
replaceFree u v e@(TermVar x) = if u == x then TermVar v else e
replaceFree u v (TermApp m n) = TermApp (replaceFree u v m) (replaceFree u v n)
replaceFree u v e@(TermAbs x m) =
  if u == x then e
  else TermAbs x (replaceFree u v m)


-- x -> y in (Abs x m)
alphaRename :: Term -> String -> Term
alphaRename (TermAbs x m) y =
  if y `Data.Set.notMember` (getFreeVariableSet m)
    && y `Data.Set.notMember` (getBindingVariableSet m)
  then TermAbs y (replaceFree x y m)
  else error "bad input"
alphaRename _ _ = error "bad input"


-- substitute m x n = m [ x := n ]
substitute :: Term -> String -> Term -> Term
substitute e@(TermVar y) x n = if x == y then n else e
substitute (TermApp p q) x n = TermApp (substitute p x n) (substitute q x n)
substitute e@(TermAbs y p) x n
  | x == y = e
  | x /= y && x `Data.Set.notMember` (getFreeVariableSet e) = e
  | x /= y && y `Data.Set.notMember` (getFreeVariableSet n) =
    TermAbs y (substitute p x n)
  | otherwise = error "bad input"


betaReduce :: Term -> Term
betaReduce (TermApp (TermAbs x m) n) = substitute m x n
betaReduce _ = error "bad input"

