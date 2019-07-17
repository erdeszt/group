module GroupApi

import Group
import GroupAccess
import GroupChild
import GroupElem

%default total
%access public export

grant : {groupId : GroupId}
     -> (group : Group)
     -> (elem : Elem groupId group)
     -> (userId : UserId)
     -> (group' : Group ** (elem' : Elem groupId group' ** HasDirectAccess groupId userId elem' group'))
grant (MkGroup groupId m l r) ThisGroup userId =
  (MkGroup groupId (Just userId) l r ** (ThisGroup ** DirectAccessToGroup))
grant (MkGroup gid m (Just left) r) (LeftGroup elem) userId with (grant left elem userId)
  | (group' ** (path ** access)) = (MkGroup gid m (Just group') r ** (LeftGroup path ** DirectAccessOnLeft access))
grant (MkGroup gid m l (Just right)) (RightGroup elem) userId with (grant right elem userId)
  | (group' ** (path ** access)) = (MkGroup gid m l (Just group') ** (RightGroup path ** DirectAccessOnRight access))


{- EXPERIMENTAL: -}

-- Ideas:
--   * HasAccess g u elem group -> Either (HasDirectAccess g u elem group) (HasDirectAccess g' u elem' group, Child g g' group)
--     * Access to g is either DirectAccess to g or direct access to one of
--       g's parents
