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

-- TODO: Naming + examples
-- TODO: child and parent id can be implicit probably
data PP : (childId : GroupId) -> (parentId : GroupId) -> (childElem : Elem childId group) -> (parentElem : Elem parent group) -> Group -> Type where
  ParentEndsHereChildOnLeft : (childElem : Elem childId (MkGroup parentId m l r)) -> PP childId parentId childElem ThisGroup (MkGroup parentId m' (Just group) r')
  ParentEndsHereChildOnRight : (childElem : Elem childId (MkGroup parentId m l r)) -> PP childId parentId childElem ThisGroup (MkGroup parentId m' l' (Just group))
  PrefixLeft : (pp : PP childId parentId childElem parentElem group) -> PP childId parentId (LeftGroup childElem) (LeftGroup parentElem) (MkGroup gid m' (Just group) r')
  PrefixRight : (pp : PP childId parentId childElem parentElem group) -> PP childId parentId (RightGroup childElem) (RightGroup parentElem) (MkGroup gid m' l' (Just group))

createPP : {group : Group} -> (childId : GroupId) -> (parentId : GroupId) -> (childElem : Elem childId group) -> (parentElem : Elem parentId group) -> Maybe (PP childId parentId childElem parentElem group)
createPP {group = (MkGroup parentId m l r)} parentId parentId ThisGroup ThisGroup =
  Nothing -- childElem = parentElem
createPP {group = (MkGroup parentId m (Just group) r)} childId parentId (LeftGroup pathToChild) ThisGroup =
  Just (ParentEndsHereChildOnLeft (LeftGroup pathToChild))
createPP {group = (MkGroup parentId m l (Just group))} childId parentId (RightGroup pathToChild) ThisGroup =
  Just (ParentEndsHereChildOnRight (RightGroup pathToChild))
createPP {group = (MkGroup childId m (Just l) r)} childId parentId ThisGroup (LeftGroup _) =
  Nothing -- Child is above parent
createPP {group = (MkGroup groupId m (Just l) r)} childId parentId (LeftGroup pathToChild) (LeftGroup pathToParent) =
  map PrefixLeft (createPP childId parentId pathToChild pathToParent)
createPP {group = (MkGroup groupId m (Just x) (Just group))} childId parentId (RightGroup _) (LeftGroup _) =
  Nothing -- Child goes right parent goes left
createPP {group = (MkGroup childId m l (Just x))} childId parentId ThisGroup (RightGroup _) =
  Nothing -- Child is above parent
createPP {group = (MkGroup groupId m (Just group) (Just x))} childId parentId (LeftGroup _) (RightGroup _) =
  Nothing -- Child goes left parent goes right
createPP {group = (MkGroup groupId m l (Just x))} childId parentId (RightGroup pathToChild) (RightGroup pathToParent) =
  map PrefixRight (createPP childId parentId pathToChild pathToParent)


lemma_PP_trans : {a, b, c : GroupId}
              -> {group : Group}
              -> {aElem : Elem a group}
              -> {bElem : Elem b group}
              -> {cElem : Elem c group}
              -> PP b a bElem aElem group
              -> PP c b cElem bElem group
              -> PP c a cElem aElem group
lemma_PP_trans {group = (MkGroup a m' (Just x) r')} {aElem = ThisGroup} {bElem = bElem} {cElem = cElem} (ParentEndsHereChildOnLeft bElem) ppCB = ParentEndsHereChildOnLeft cElem
lemma_PP_trans {group = (MkGroup a m' l' (Just x))} {aElem = ThisGroup} {bElem = bElem} {cElem = cElem} (ParentEndsHereChildOnRight bElem) ppCB = ParentEndsHereChildOnRight cElem
lemma_PP_trans {group = (MkGroup h m (Just x) r)} {aElem = (LeftGroup parentElem)} {bElem = (LeftGroup childElem)} {cElem = (LeftGroup y)} (PrefixLeft pp) (PrefixLeft z) = PrefixLeft (lemma_PP_trans pp z)
lemma_PP_trans {group = (MkGroup h m l (Just x))} {aElem = (RightGroup parentElem)} {bElem = (RightGroup childElem)} {cElem = (RightGroup y)} (PrefixRight pp) (PrefixRight z) = PrefixRight (lemma_PP_trans pp z)