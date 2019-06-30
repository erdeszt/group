module GroupChild

import Group
import GroupElem

%default total
%access public export

-- Definition of child with respect to a parent ==
--     group with an Elem that is larger than
--     the Elem of the parent
--     && the Elem of the parent is a prefix of
--     the Elem of the group
--

data Prefix : (childElem : Elem childId group) -> (parentElem : Elem parentId group) -> Type where
  ChildOnLeft : Prefix (LeftGroup child) ThisGroup
  ChildOnRight : Prefix (RightGroup child) ThisGroup
  GoingLeft : Prefix parent child -> Prefix (LeftGroup parent) (LeftGroup child)
  GoingRight : Prefix parent child -> Prefix (RightGroup parent) (RightGroup child)

createPrefix : (childElem : Elem childId group) -> (parentElem : Elem parentId group) -> Maybe (Prefix childElem parentElem)
createPrefix ThisGroup ThisGroup = Nothing -- Same elem TODO: Prevent this with DistinctElem
createPrefix ThisGroup (LeftGroup _) = Nothing -- Child path is shorter than parent
createPrefix ThisGroup (RightGroup _) = Nothing -- Child path is shorter than parent
createPrefix (LeftGroup _) ThisGroup = Just ChildOnLeft
createPrefix (LeftGroup child) (LeftGroup parent) =
  map GoingLeft (createPrefix child parent)
createPrefix (LeftGroup _) (RightGroup _) = Nothing -- Child goes left parent goes right
createPrefix (RightGroup _) ThisGroup = Just ChildOnRight
createPrefix (RightGroup _) (LeftGroup _) = Nothing -- Child goes right parent goes left
createPrefix (RightGroup child) (RightGroup parent) =
  map GoingRight (createPrefix child parent)