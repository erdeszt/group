module GroupApi

import Group
import GroupAccess
import GroupChild
import GroupElem

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


{- EXPERIMENTAL: -}

-- Ideas:
--   * HasAccess g u group -> Either (HasDirectAccess g u group) (HasDirectAccess g' u group, Child g g') -- or somethign like this with Elem
--   * HasDirectAccess g u group -> Child g' g -> HasAccess g' u group
--       * Or HasDirectAccess g' u group
--   * HasDirectAccess g u group -> HasAccess g u group

