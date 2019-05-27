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
        Nothing => Nothing
        Just path => Just (There path)

createElem : DecEq a => (tree : Tree a) -> (item : a) -> Maybe (Elem item tree)
createElem (Node value children) item =
  case decEq value item of
    Yes Refl => Just ThisNode
    No contra =>
      case createListElem children item of
        Nothing => Nothing
        Just path => Just (ChildNode path)

