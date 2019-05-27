module RoseTreeIndex

import Pruviloj
import Pruviloj.Induction

%default total
%language ElabReflection

data Tree : Type -> Type where
  Leaf : Tree a
  Node : (value : a) -> (children : List (Tree a)) -> Tree a

data Elem : a -> Tree a -> Type where
  ThisNode : Elem x (Node x cs)
  ChildHere : Elem x tree -> Elem x (Node y (tree :: cs))
  ChildThere : Elem x tree -> Elem x (Node y (tree' :: cs))



