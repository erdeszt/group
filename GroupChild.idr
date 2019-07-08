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
data Child : (childElem : Elem childId group) -> (parentElem : Elem parent group) -> Group -> Type where
  ParentEndsHereChildOnLeft : (childElem : Elem childId (MkGroup parentId m l r)) -> Child childElem ThisGroup (MkGroup parentId m' (Just group) r')
  ParentEndsHereChildOnRight : (childElem : Elem childId (MkGroup parentId m l r)) -> Child childElem ThisGroup (MkGroup parentId m' l' (Just group))
  PrefixLeft : Child childElem parentElem group -> Child (LeftGroup childElem) (LeftGroup parentElem) (MkGroup gid m' (Just group) r')
  PrefixRight : Child childElem parentElem group -> Child (RightGroup childElem) (RightGroup parentElem) (MkGroup gid m' l' (Just group))

createChild : {group : Group} -> {childId : GroupId} -> {parentId : GroupId} -> (childElem : Elem childId group) -> (parentElem : Elem parentId group) -> Maybe (Child childElem parentElem group)
createChild {group = (MkGroup parentId m l r)} {childId=parentId} {parentId=parentId} ThisGroup ThisGroup =
  Nothing -- childElem = parentElem
createChild {group = (MkGroup parentId m (Just group) r)} {parentId=parentId} (LeftGroup pathToChild) ThisGroup =
  Just (ParentEndsHereChildOnLeft (LeftGroup pathToChild))
createChild {group = (MkGroup parentId m l (Just group))} {parentId=parentId} (RightGroup pathToChild) ThisGroup =
  Just (ParentEndsHereChildOnRight (RightGroup pathToChild))
createChild {group = (MkGroup childId m (Just l) r)} {childId=childId} ThisGroup (LeftGroup _) =
  Nothing -- Child is above parent
createChild {group = (MkGroup groupId m (Just l) r)} (LeftGroup pathToChild) (LeftGroup pathToParent) =
  map PrefixLeft (createChild pathToChild pathToParent)
createChild {group = (MkGroup groupId m (Just l) (Just r))} (RightGroup _) (LeftGroup _) =
  Nothing -- Child goes right parent goes left
createChild {group = (MkGroup childId m l (Just r))} {childId=childId} ThisGroup (RightGroup _) =
  Nothing -- Child is above parent
createChild {group = (MkGroup groupId m (Just l) (Just r))} (LeftGroup _) (RightGroup _) =
  Nothing -- Child goes left parent goes right
createChild {group = (MkGroup groupId m l (Just r))} (RightGroup pathToChild) (RightGroup pathToParent) =
  map PrefixRight (createChild pathToChild pathToParent)

createChild' : {group : Group} -> {childId : GroupId} -> {parentId : GroupId} -> (childElem : Elem childId group) -> (parentElem : Elem parentId group) -> {auto prf : Child childElem parentElem group} -> Child childElem parentElem group
createChild' childElem parentElem {prf} = prf

lemma_child_trans : {a, b, c : GroupId}
                 -> {group : Group}
                 -> {aElem : Elem a group}
                 -> {bElem : Elem b group}
                 -> {cElem : Elem c group}
                 -> Child bElem aElem group
                 -> Child cElem bElem group
                 -> Child cElem aElem group
lemma_child_trans {group = (MkGroup a m (Just l) r)} {aElem = ThisGroup} {bElem} {cElem} (ParentEndsHereChildOnLeft bElem) childCB = ParentEndsHereChildOnLeft cElem
lemma_child_trans {group = (MkGroup a m l (Just r))} {aElem = ThisGroup} {bElem} {cElem} (ParentEndsHereChildOnRight bElem) childCB = ParentEndsHereChildOnRight cElem
lemma_child_trans {group = (MkGroup gid m (Just l) r)} {aElem = (LeftGroup _)} {bElem = (LeftGroup _)} {cElem = (LeftGroup _)} (PrefixLeft prefixBA) (PrefixLeft prefixCB) = PrefixLeft (lemma_child_trans prefixBA prefixCB)
lemma_child_trans {group = (MkGroup gid m l (Just r))} {aElem = (RightGroup _)} {bElem = (RightGroup _)} {cElem = (RightGroup _)} (PrefixRight prefixBA) (PrefixRight prefixCB) = PrefixRight (lemma_child_trans prefixBA prefixCB)

showChild : {childElem : Elem childId group} -> {parentElem : Elem parentId group} -> Child childElem parentElem group -> String
showChild (ParentEndsHereChildOnLeft leftElem) = "ParentEndsHereChildOnLeft (" <+> show leftElem <+> ")"
showChild (ParentEndsHereChildOnRight rightElem) = "ParentEndsHereChildOnRight (" <+> show rightElem <+> ")"
showChild (PrefixLeft leftChild) = "PrefixLeft (" <+> showChild leftChild <+> ")"
showChild (PrefixRight rightChild) = "PrefixRight (" <+> showChild rightChild <+> ")"