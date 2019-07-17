module GroupChild

import Group
import GroupElem
import GroupDistinctElem

%default total
%access public export

-- Definition of child with respect to a parent ==
--     group with an Elem that is larger than
--     the Elem of the parent
--     && the Elem of the parent is a prefix of
--     the Elem of the group
data Child : (childElem : Elem childId group) -> (parentElem : Elem parentId group) -> Group -> Type where
  ParentEndsHereChildOnLeft  : (childElem : Elem childId group) -> Child (LeftGroup childElem) ThisGroup (MkGroup parentId m (Just group) r)
  ParentEndsHereChildOnRight : (childElem : Elem childId group) -> Child (RightGroup childElem) ThisGroup (MkGroup parentId m l (Just group))
  PrefixLeft : Child childElem parentElem group -> Child (LeftGroup childElem) (LeftGroup parentElem) (MkGroup gid m (Just group) r)
  PrefixRight : Child childElem parentElem group -> Child (RightGroup childElem) (RightGroup parentElem) (MkGroup gid m l (Just group))

createChild : {childId, parentId : GroupId}
           -> {group : Group}
           -> (childElem : Elem childId group)
           -> (parentElem : Elem parentId group)
           -> Maybe (Child childElem parentElem group)
createChild {group = (MkGroup parentId m l r)} ThisGroup ThisGroup = Nothing
createChild {group = (MkGroup parentId m (Just l) r)} (LeftGroup child) ThisGroup = Just (ParentEndsHereChildOnLeft child)
createChild {group = (MkGroup parentId m l (Just r))} (RightGroup child) ThisGroup = Just (ParentEndsHereChildOnRight child)
createChild {group = (MkGroup gid m (Just l) r)} ThisGroup (LeftGroup parent) = Nothing -- Child above parent (l)
createChild {group = (MkGroup gid m (Just l) r)} (LeftGroup child) (LeftGroup parent) = map PrefixLeft (createChild child parent)
createChild {group = (MkGroup gid m (Just l) (Just r))} (RightGroup child) (LeftGroup parent) = Nothing -- Child goes right parent goes left
createChild {group = (MkGroup gid m l (Just r))} ThisGroup (RightGroup parent) = Nothing -- Child above parent (r)
createChild {group = (MkGroup gid m (Just l) (Just r))} (LeftGroup child) (RightGroup parent) = Nothing -- Child goes left parent goes right
createChild {group = (MkGroup gid m l (Just r))} (RightGroup child) (RightGroup parent) = map PrefixRight (createChild child parent)

lemma_child_trans : {a, b, c : GroupId}
                 -> {group : Group}
                 -> {aElem : Elem a group}
                 -> {bElem : Elem b group}
                 -> {cElem : Elem c group}
                 -> Child bElem aElem group
                 -> Child cElem bElem group
                 -> Child cElem aElem group
lemma_child_trans {a=a} {aElem = ThisGroup} {bElem = (LeftGroup bElemRec)} {cElem = (LeftGroup cElemRec)} {group = (MkGroup a m (Just l) r)} (ParentEndsHereChildOnLeft bElemRec) (PrefixLeft childCBRec) = ParentEndsHereChildOnLeft cElemRec
lemma_child_trans {a=a} {aElem = ThisGroup} {bElem = (RightGroup bElemRec)} {cElem = (RightGroup cElemRec)} {group = (MkGroup a m l (Just r))} (ParentEndsHereChildOnRight bElemRec) (PrefixRight childCBRec) = ParentEndsHereChildOnRight cElemRec
lemma_child_trans {aElem = (LeftGroup aElemRec)} {bElem = (LeftGroup bElemRec)} {cElem = (LeftGroup cElemRec)} {group = (MkGroup gid m (Just l) r)} (PrefixLeft childBARec) (PrefixLeft childCBRec) = PrefixLeft (lemma_child_trans childBARec childCBRec)
lemma_child_trans {aElem = (RightGroup aElemRec)} {bElem = (RightGroup bElemRec)} {cElem = (RightGroup cElemRec)} {group = (MkGroup gid m l (Just r))} (PrefixRight childBARec) (PrefixRight childCBRec) = PrefixRight (lemma_child_trans childBARec childCBRec)

showChild : {childElem : Elem childId group} -> {parentElem : Elem parentId group} -> Child childElem parentElem group -> String
showChild (ParentEndsHereChildOnLeft leftElem) = "ParentEndsHereChildOnLeft (" <+> show leftElem <+> ")"
showChild (ParentEndsHereChildOnRight rightElem) = "ParentEndsHereChildOnRight (" <+> show rightElem <+> ")"
showChild (PrefixLeft leftChild) = "PrefixLeft (" <+> showChild leftChild <+> ")"
showChild (PrefixRight rightChild) = "PrefixRight (" <+> showChild rightChild <+> ")"