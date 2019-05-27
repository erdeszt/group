module RoseTreeIndex

import Pruviloj
import Pruviloj.Induction

%default total
%language ElabReflection

data Tree : Type -> Type where
  Node : (value : a) -> (children : List (Tree a)) -> Tree a

data ChildElem : a -> List (Tree a) -> Type where
  ChildHere  :                   ChildElem x ((Node x children) :: siblings)
  ChildThere : ChildElem x xs -> ChildElem x (node :: xs)
  GrandChild : ChildElem x xs -> ChildElem x ((Node value xs) :: siblings)

data Elem : a -> Tree a -> Type where
  RootElem    :                   Elem x (Node x children)
  ChildOfRoot : ChildElem x xs -> Elem x (Node value xs)

createChildElem : DecEq a => (trees : List (Tree a)) -> (item : a) -> Maybe (ChildElem item trees)
createChildElem [] item = Nothing
createChildElem ((Node value children) :: siblings) item =
  case decEq value item of
    Yes Refl => Just ChildHere
    No contra =>
      case createChildElem siblings item of
        Just path => Just (ChildThere path)
        Nothing =>
          case createChildElem children item of
            Just path => Just (GrandChild path)
            Nothing => Nothing

createElem : DecEq a => (tree : Tree a) -> (item : a) -> Maybe (Elem item tree)
createElem (Node value children) item =
  case decEq value item of
    Yes Refl => Just RootElem
    No contra =>
      case createChildElem children item of
        Nothing => Nothing
        Just path => Just (ChildOfRoot path)

getChildElem : (trees : List (Tree a)) -> ChildElem item trees -> a
getChildElem ((Node item _) :: _)      ChildHere        = item
getChildElem (_ :: siblings)          (ChildThere path) = getChildElem siblings path
getChildElem ((Node _ children) :: _) (GrandChild path) = getChildElem children path

getElem : (tree : Tree a) -> Elem item tree -> a
getElem (Node item _)   RootElem          = item
getElem (Node _ trees) (ChildOfRoot path) = getChildElem trees path

getOr : DecEq a => (tree : Tree a) -> (item : a) -> (default : a) -> a
getOr tree item default =
  case createElem tree item of
    Nothing => default
    Just elem => getElem tree elem

testTree : Tree Nat
testTree = Node 1 [Node 2 [Node 3 []], Node 4 [Node 5 []]]

test1 : getOr RoseTreeIndex.testTree 10 11 = 11
test1 = Refl

test2 : getOr RoseTreeIndex.testTree 3 11 = 3
test2 = Refl

