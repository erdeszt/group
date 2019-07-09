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


{- EXPERIMENTAL: -}

-- Ideas:
--   * HasAccess g u group -> Either (HasDirectAccess g u group) (HasDirectAccess g' u group, Child g g') -- or somethign like this with Elem
--   * HasDirectAccess g u group -> Child g' g -> HasAccess g' u group
--       * Or HasDirectAccess g' u group
--   * HasDirectAccess g u group -> HasAccess g u group

-- NOTE: Issue is that no connection between HasAccess and Child
--       so the situation like this can exists:
-- accessExtendsToChildren {childElem = (LeftGroup x)} {groupElem = ThisGroup} {distinct = LeftAndThis} {userId} {group=(MkGroup groupId m' (Just group1) r')} (AccessToLeft y) (ParentEndsHereChildOnLeft (LeftGroup x)) = ?wat
--  this means that the access is on the left but according to `distinct`, the child is on the left and parent ends here(but we should have access to parent (which is on the left side == CONTRADICTION))
-- Without distinct elem the usual situation of childElem == groupElem arise
-- So Child is probably still not carrying enough information to
-- provably prevent the above to situation

