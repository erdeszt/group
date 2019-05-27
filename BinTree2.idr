module BinTree2

%default total
%language ElabReflection

data Tree : Type -> Type where
  Node : (value : a) -> (left : Maybe (Tree a)) -> (right : Maybe (Tree a)) -> Tree a

data Elem : a -> Tree a -> Type where
  ThisNode : Elem x (Node x l r)
  LeftNode : Elem x tree -> Elem x (Node y (Just tree) r)
  RightNode : Elem x tree -> Elem x (Node y l (Just tree))

createElem : DecEq a => (tree : Tree a) -> (item : a) -> Maybe (Elem item tree)
createElem (Node value Nothing     Nothing) item =
  case decEq value item of
    Yes Refl => Just ThisNode
    No contra => Nothing
createElem (Node value Nothing     (Just right)) item =
  case decEq value item of
    Yes Refl => Just ThisNode
    No contra => map RightNode (createElem right item)
createElem (Node value (Just left) Nothing) item =
  case decEq value item of
    Yes Refl => Just ThisNode
    No contra => map LeftNode (createElem left item)
createElem (Node value (Just left) (Just right)) item =
  case decEq value item of
    Yes Refl => Just ThisNode
    No contra => (map LeftNode (createElem left item)) <|> (map RightNode (createElem right item))

getElem : {item : a} -> (tree : Tree a) -> Elem item tree -> a
getElem (Node item _ _) ThisNode = item
getElem (Node _ (Just left) _) (LeftNode path) = getElem left path
getElem (Node _ _ (Just right)) (RightNode path) = getElem right path

