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
      -> Elem groupId group
      -> (userId : UserId)
      -> (group' : Group ** (Elem groupId group', HasAccess groupId userId group'))
grant (MkGroup currentGid member left right) ThisGroup newMember =
  ((MkGroup currentGid (Just newMember) left right) ** (ThisGroup, AccessToGroup))
grant (MkGroup currentGid member (Just left) right) (LeftGroup elem) newMember =
  case grant left elem newMember of
    (group ** (elemPrf, memberPrf)) =>
      ((MkGroup currentGid member (Just group) right) ** (LeftGroup elemPrf, AccessToLeft memberPrf))
grant (MkGroup currentGid member left (Just right)) (RightGroup elem) newMember =
  case grant right elem newMember of
    (group ** (elemPrf, memberPrf)) =>
      ((MkGroup currentGid member left (Just group)) ** (RightGroup elemPrf, AccessToRight memberPrf))

grantHA : {groupId : GroupId}
      -> (group : Group)
      -> (elem : Elem groupId group)
      -> (userId : UserId)
      -> (group' : Group ** HA groupId elem userId group')
grantHA (MkGroup groupId m l r) ThisGroup userId =
  (MkGroup groupId (Just userId) l r ** ATG)
grantHA (MkGroup gid m (Just left) r) (LeftGroup elem) userId with (grantHA left elem userId)
  | (group' ** access) = (MkGroup gid m (Just group') r ** ATL access)
grantHA (MkGroup gid m l (Just right)) (RightGroup elem) userId with (grantHA right elem userId)
  | (group' ** access) = (MkGroup gid m l (Just group') ** ATR access)




{- EXPERIMENTAL: -}

-- Ideas:
--   * Grant direct access
--   * HasAccess g u group -> Either (HasDirectAccess g u group) (HasDirectAccess g' u group, Child g g') -- or somethign like this with Elem
--   * HasDirectAccess g u group -> Child g' g -> HasAccess g' u group
--       * Or HasDirectAccess g' u group
--   * HasDirectAccess g u group -> HasAccess g u group
--   * childToDistinctElem
