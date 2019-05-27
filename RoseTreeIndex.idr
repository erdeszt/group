module RoseTreeIndex

import Pruviloj
import Pruviloj.Induction

%default total
%language ElabReflection

-- data Tree : Type -> Type where
--   Node : (value : a) -> (children : List (Tree a)) -> Tree a

-- data ElemIn : a -> List (Tree a) -> Type where
--   ElemInHere : ElemIn x ((Node x ncs) :: cs)
--   ElemInThere : ElemIn x xs -> ElemIn x (node :: xs)

-- data Elem : a -> Tree a -> Type where
--   ThisNode : Elem x (Node x cs)
--   ChildNode : ElemIn x xs -> Elem x (Node y xs)
--   -- ChildHere : Elem x tree -> Elem x (Node y (tree :: cs))
--   -- ChildThere : Elem x tree -> Elem x (Node y (tree :: cs))

-- createElemIn : DecEqa => (trees : List (Tree a)) -> 

-- createElem : DecEq a => (tree : Tree a) -> (item : a) -> Maybe (Elem item tree)
-- createElem (Node value []) item = 
--   case decEq value item of
--     Yes Refl => Just ThisNode
--     No contra => Nothing
-- createElem (Node value children) item =
--   case decEq value item of
--     Yes Refl => Just ThisNode
--     No contra =>
--       let elemIn = ?yo in ?rhs

-- createElemA : DecEq a => (tree : Tree a) -> (item : a) -> Maybe (Elem item tree)
-- createElemA (Node value []) item =
--   case decEq value item of
--     Yes Refl => Just ThisNode
--     No contra => Nothing
-- createElemA tree@(Node value (firstChild :: children)) item =
--   case decEq value item of
--     Yes Refl => Just ThisNode
--     No contra =>
--       case createElemA firstChild item of
--         Just path => Just (ChildHere path)
--         Nothing =>
--           let node = assert_smaller tree (Node value children) in
--           case createElemA node item of
--             Nothing => Nothing
--             Just path => Just (ChildThere path)
            
-- getElem : {item : a} -> (tree : Tree a) -> Elem item tree -> a
-- getElem (Node item _) ThisNode = item
-- getElem (Node _ (child :: cs)) (ChildHere path) = getElem child path
-- getElem (Node value (tree' :: cs)) (ChildThere path) = value

-- testTree : Tree Int
-- testTree = Node 1 [Node 2 [], Node 3 [Node 4 []]]
--   -- createElem (Node value children) item =
--   --   case decEq value item of
--   --     Yes Refl => Just ThisNode
--   --     No contra => createElemInChildren children item
--     -- case decEq value item of
--     --   Yes Refl => Just ThisNode
--     --   No contra => createElemInChildren tree item

--   -- createElemInChildren :  : Tree a) -> (item : a) -> Maybe (Elem item fullTree)
--   -- createElemInChildren tree@(Node _ []) _ = Nothing
--   -- createElemInChildren tree@(Node _ ((Node value thisCs)::cs)) item =
--   --   case decEq value item of
--   --     Yes Refl => Just (ChildHere ThisNode)
--   --     No contra => ?wat


--     -- case decEq value item of
--     --   Yes Refl => Just ThisNode
--     --   No contra => 
--     --     -- let rec = map (\tree => createElem tree item) children in
--     --     ?wat
--         -- case children of
--         --   [] => Nothing
--         --   c :: cs =>
--         --     case createElem c item of
--         --       Just path => Just (ChildHere path)
--         --       Nothing =>
--         --         case createElem (Node value cs) item of
--         --           Nothing => Nothing
--         --           Just path => Just (ChildThere path)







