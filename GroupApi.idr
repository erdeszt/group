module GroupApi

import Group
import GroupAccess
import GroupChild
import GroupElem

%default total

grantUnchecked : {groupId : GroupId}
              -> (group : Group)
              -> (elem : Elem groupId group)
              -> (userId : UserId)
              -> (group' : Group ** (elem' : Elem groupId group' ** HasDirectAccess groupId userId elem' group'))
grantUnchecked (MkGroup groupId m l r) ThisGroup userId =
  (MkGroup groupId (Just userId) l r ** (ThisGroup ** DirectAccessToGroup))
grantUnchecked (MkGroup gid m (Just left) r) (LeftGroup elem) userId with (grantUnchecked left elem userId)
  | (group' ** (path ** access)) = (MkGroup gid m (Just group') r ** (LeftGroup path ** DirectAccessOnLeft access))
grantUnchecked (MkGroup gid m l (Just right)) (RightGroup elem) userId with (grantUnchecked right elem userId)
  | (group' ** (path ** access)) = (MkGroup gid m l (Just group') ** (RightGroup path ** DirectAccessOnRight access))


secureGrant : {groupId : GroupId}
           -> {grantingUser : UserId}
           -> (group : Group)
           -> (userId : UserId)
           -> {elem : Elem groupId group}
           -> (access : HasAccess groupId grantingUser elem group)
           -> (group' : Group ** (elem' : Elem groupId group' ** HasDirectAccess groupId userId elem' group'))
secureGrant group userId {elem} access = grantUnchecked group elem userId

secureGrantStrict : {groupId : GroupId}
                 -> {grantingUser : UserId}
                 -> (group : Group)
                 -> (userId : UserId)
                 -> {elem : Elem groupId group}
                 -> (access : HasDirectAccess groupId grantingUser elem group)
                 -> (group' : Group ** (elem' : Elem groupId group' ** HasDirectAccess groupId userId elem' group'))
secureGrantStrict (MkGroup groupId (Just grantingUser) l r) userId {elem = ThisGroup} DirectAccessToGroup =
  (MkGroup groupId (Just userId) l r ** (ThisGroup ** DirectAccessToGroup))
secureGrantStrict (MkGroup gid m (Just left) r) userId {elem = (LeftGroup elem)} (DirectAccessOnLeft access) with (secureGrantStrict left userId access)
  | (group' ** (path ** access')) = (MkGroup gid m (Just group') r ** (LeftGroup path ** DirectAccessOnLeft access'))
secureGrantStrict (MkGroup gid m l (Just right)) userId {elem = (RightGroup elem)} (DirectAccessOnRight access) with (secureGrantStrict right userId access)
  | (group' ** (path ** access')) = (MkGroup gid m l (Just group') ** (RightGroup path ** DirectAccessOnRight access'))


public export
data DomainError
  = Unauthorized GroupId UserId
  | GroupNotFound GroupId

public export
grant : {grantingUser : UserId}
     -> (userId : UserId)
     -> (groupId : GroupId)
     -> (group : Group)
     -> (token : AccessToken)
     -> {userToken : UserToken grantingUser token}
     -> Either DomainError (group' : Group ** (elem' : Elem groupId group' ** HasDirectAccess groupId userId elem' group'))
grant userId groupId group (MkToken grantingUser isAdmin) =
  case createElem group groupId of
    Nothing => Left (GroupNotFound groupId)
    Just elem =>
      case createAccess group elem grantingUser of
        Nothing => Left (Unauthorized groupId grantingUser)
        Just access => Right (secureGrant group userId access)


{- EXPERIMENTAL: -}


-- Ideas:
--   * HasAccess g u elem group -> Either (HasDirectAccess g u elem group) (HasDirectAccess g' u elem' group, Child g g' group)
--     * Access to g is either DirectAccess to g or direct access to one of
--       g's parents
