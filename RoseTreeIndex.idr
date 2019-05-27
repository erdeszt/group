module RoseTreeIndex

import Pruviloj
import Pruviloj.Induction

%default total
%language ElabReflection

data Tree : Type -> Type where
  Node : (value : a) -> (children : List (Tree a)) -> Tree a

data ListElem : a -> List (Tree a) -> Type where
  Here : ListElem x ((Node x cs) :: ts)
  There : ListElem x xs -> ListElem x (y :: xs)
  ChildHere : ListElem item children -> ListElem item ((Node x children) :: xs)

data Elem : a -> Tree a -> Type where
  ThisNode : Elem x (Node x cs)
  ChildNode : ListElem x trees -> Elem x (Node y trees)

createListElem : DecEq a => (trees : List (Tree a)) -> (item : a) -> Maybe (ListElem item trees)
createListElem [] item = Nothing
createListElem ((Node value children) :: xs) item =
  case decEq value item of
    Yes Refl => Just Here
    No contra =>
      case createListElem xs item of
        Just path => Just (There path)
        Nothing =>
          case createListElem children item of
            Just path => Just (ChildHere path)
            Nothing => Nothing

createElem : DecEq a => (tree : Tree a) -> (item : a) -> Maybe (Elem item tree)
createElem (Node value children) item =
  case decEq value item of
    Yes Refl => Just ThisNode
    No contra =>
      case createListElem children item of
        Nothing => Nothing
        Just path => Just (ChildNode path)

getListElem : (trees : List (Tree a)) -> ListElem item trees -> a
getListElem ((Node item _) :: _)      Here = item
getListElem (_ :: xs)                (There path) = getListElem xs path
getListElem ((Node _ children) :: _) (ChildHere path) = getListElem children path

getElem : (tree : Tree a) -> Elem item tree -> a
getElem (Node item _) ThisNode = item
getElem (Node _ trees) (ChildNode path) = getListElem trees path

getOr : DecEq a => (tree : Tree a) -> (item : a) -> (default : a) -> a
getOr tree item default =
  case createElem tree item of
    Nothing => default
    Just elem => getElem tree elem

testTree : Tree Nat
testTree = Node 1 [Node 2 [Node 3 []], Node 4 [Node 5 []]]



