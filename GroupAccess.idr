module GroupAccess

import Group
import GroupElem

%default total
%access public export

data HasAccess : GroupId -> UserId -> Group -> Type where
  AccessToGroup : HasAccess gid uid (MkGroup gid (Just uid) left right)
  AccessToParentLeft : Elem gid left -> HasAccess gid uid (MkGroup gid' (Just uid) (Just left) right)
  AccessToParentRight : Elem gid right -> HasAccess gid uid (MkGroup gid' (Just uid) left (Just right))
  AccessToLeft : HasAccess gid uid group -> HasAccess gid uid (MkGroup gid' member (Just group) right)
  AccessToRight : HasAccess gid uid group -> HasAccess gid uid (MkGroup gid' member left (Just group))

data HasDirectAccess : GroupId -> UserId -> Group -> Type where
  DirectAccessToGroup : HasDirectAccess gid uid (MkGroup gid (Just uid) left right)
  DirectAccessOnLeft : HasDirectAccess gid uid group -> HasDirectAccess gid uid (MkGroup gid' member (Just group) right)
  DirectAccessOnRight : HasDirectAccess gid uid group -> HasDirectAccess gid uid (MkGroup gid' member left (Just group))

-- TODO: HasAccess groupId -> HasDirectAccess groupId | (HasDirectAccess groupId' & Child groupId groupId')
-- TODO: HasAccess groupId group -> Elem groupId group
-- TODO: HasAccess groupId group -> Child groupId (group.id)

access : {groupId : GroupId}
      -> (group : Group)
      -> (elem : Elem groupId group)
      -> (userId : UserId)
      -> Maybe (HasAccess groupId userId group)
access (MkGroup groupId member left right) ThisGroup uid =
  case member of
    Nothing => Nothing
    Just mid =>
      case decEq uid mid of
        No contra => Nothing
        Yes Refl => Just AccessToGroup
access {groupId} (MkGroup groupId' member (Just left) right) (LeftGroup leftElem) uid =
  case member of
    Nothing =>
      case access left leftElem uid of
        Nothing => Nothing
        Just leftAccess => Just (AccessToLeft leftAccess)
    Just mid =>
        case decEq uid mid of
          No contra =>
            case access left leftElem uid of
              Nothing => Nothing
              Just leftAccess => Just (AccessToLeft leftAccess)
          Yes Refl =>
            case createElem left groupId of
              Nothing => Nothing
              Just leftElem => Just (AccessToParentLeft leftElem)
access {groupId} (MkGroup groupId' member left (Just right)) (RightGroup rightElem) uid =
  case member of
    Nothing =>
      case access right rightElem uid of
        Nothing => Nothing
        Just rightAccess => Just (AccessToRight rightAccess)
    Just mid =>
        case decEq uid mid of
          No contra =>
            case access right rightElem uid of
              Nothing => Nothing
              Just rightAccess => Just (AccessToRight rightAccess)
          Yes Refl =>
            case createElem right groupId of
              Nothing => Nothing
              Just rightElem => Just (AccessToParentRight rightElem)
