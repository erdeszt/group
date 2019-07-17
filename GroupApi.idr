module GroupApi

import Group
import GroupAccess
import GroupChild
import GroupElem
import GroupDistinctElem

%default total
%access public export


grant : {groupId : GroupId}
     -> (group : Group)
     -> (elem : Elem groupId group)
     -> (userId : UserId)
     -> (group' : Group ** HasDirectAccess groupId userId elem group')
grant (MkGroup groupId m l r) ThisGroup userId =
  (MkGroup groupId (Just userId) l r ** DirectAccessToGroup)
grant (MkGroup gid m (Just left) r) (LeftGroup elem) userId with (grant left elem userId)
  | (group' ** access) = (MkGroup gid m (Just group') r ** DirectAccessOnLeft access)
grant (MkGroup gid m l (Just right)) (RightGroup elem) userId with (grant right elem userId)
  | (group' ** access) = (MkGroup gid m l (Just group') ** DirectAccessOnRight access)

hasDirectAccessExtends : {g, g' : GroupId}
                      -> {u : UserId}
                      -> {group : Group}
                      -> {childElem : Elem g' group}
                      -> {parentElem : Elem g group}
                      -> HasDirectAccess g u parentElem group
                      -> Child childElem parentElem group
                      -> HasAccess g' u childElem group
hasDirectAccessExtends {group = (MkGroup g (Just u) (Just left) r)} DirectAccessToGroup (ParentEndsHereChildOnLeft elem) = AccessToParentLeft elem
hasDirectAccessExtends {group = (MkGroup g (Just u) l (Just right))} DirectAccessToGroup (ParentEndsHereChildOnRight elem) = AccessToParentRight elem
hasDirectAccessExtends {group = (MkGroup gid m (Just left) r)} (DirectAccessOnLeft directAccess) (PrefixLeft child) = AccessOnLeft (hasDirectAccessExtends directAccess child)
hasDirectAccessExtends {group = (MkGroup gid m l (Just right))} (DirectAccessOnRight directAccess) (PrefixRight child) = AccessOnRight (hasDirectAccessExtends directAccess child)

{- EXPERIMENTAL: -}

-- Ideas:
--   * HasAccess g u elem group -> Either (HasDirectAccess g u elem group) (HasDirectAccess g' u elem' group, Child g g' group)
--     * Access to g is either DirectAccess to g or direct access to one of
--       g's parents
