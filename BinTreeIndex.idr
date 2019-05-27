module BinTreeIndex

import Pruviloj
import Pruviloj.Induction

%default total
%language ElabReflection

data Tree : Type -> Type where
  Leaf : Tree a
  Node : (value : a) -> (left : Tree a) -> (right : Tree a) -> Tree a

data Elem : a -> Tree a -> Type where
  ThisNode   : Elem x (Node x l r)
  LeftNode   : Elem x tree -> Elem x (Node y tree r)
  RightNode  : Elem x tree -> Elem x (Node y l tree)

createElem : DecEq a => (tree : Tree a) -> (item : a) -> Maybe (Elem item tree)
createElem Leaf item = Nothing
createElem (Node value left right) item =
  case decEq value item of
    Yes Refl => Just ThisNode
    No contra => (map LeftNode (createElem left item)) <|> (map RightNode (createElem right item))

getElem : (tree : Tree a) -> (Elem item tree) -> a
getElem (Node item l r) ThisNode = item
getElem (Node y l r) (LeftNode p) = getElem l p
getElem (Node y l r) (RightNode p) = getElem r p