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


{- EXPERIMENTAL: -}

-- Ideas:
--   * HasAccess g u group -> Either (HasDirectAccess g u group) (HasDirectAccess g' u group, Child g g') -- or somethign like this with Elem
--   * HasDirectAccess g u group -> Child g' g -> HasAccess g' u group
--       * Or HasDirectAccess g' u group
