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

data Child : (childElem : Elem childId group) -> (parentElem : Elem parentId group) -> Type where
  ChildOnLeft : Child (LeftGroup child) ThisGroup
  ChildOnRight : Child (RightGroup child) ThisGroup
  PrefixLeft : Child parent child -> Child (LeftGroup parent) (LeftGroup child)
  PrefixRight : Child parent child -> Child (RightGroup parent) (RightGroup child)

createChild : (childElem : Elem childId group) -> (parentElem : Elem parentId group) -> Maybe (Child childElem parentElem)
createChild ThisGroup ThisGroup = Nothing -- Same elem TODO: Prevent this with DistinctElem
createChild ThisGroup (LeftGroup _) = Nothing -- Child path is shorter than parent
createChild ThisGroup (RightGroup _) = Nothing -- Child path is shorter than parent
createChild (LeftGroup _) ThisGroup = Just ChildOnLeft
createChild (LeftGroup child) (LeftGroup parent) =
  map PrefixLeft (createChild child parent)
createChild (LeftGroup _) (RightGroup _) = Nothing -- Child goes left parent goes right
createChild (RightGroup _) ThisGroup = Just ChildOnRight
createChild (RightGroup _) (LeftGroup _) = Nothing -- Child goes right parent goes left
createChild (RightGroup child) (RightGroup parent) =
  map PrefixRight (createChild child parent)

lemma_child_transitive : {a, b, c : GroupId}
                      -> {group : Group}
                      -> {aElem : Elem a group}
                      -> {bElem : Elem b group}
                      -> {cElem : Elem c group}
                      -> Child bElem aElem
                      -> Child cElem bElem
                      -> Child cElem aElem
lemma_child_transitive ChildOnLeft (PrefixLeft _) = ChildOnLeft
lemma_child_transitive ChildOnRight (PrefixRight _) = ChildOnRight
lemma_child_transitive (PrefixLeft ba) (PrefixLeft cb) = PrefixLeft (lemma_child_transitive ba cb)
lemma_child_transitive (PrefixRight ba) (PrefixRight cb) = PrefixRight (lemma_child_transitive ba cb)