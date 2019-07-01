module GroupAccess

import Group
import GroupElem

%default total
%access public export

data HasAccess : GroupId -> UserId -> Group -> Type where
  DirectAccess : HasAccess gid uid (MkGroup gid (Just uid) left right)
  AccessToParent : HasAccess gid uid (MkGroup gid' (Just uid) left right)
  AccessToLeft : HasAccess gid uid group -> HasAccess gid uid (MkGroup gid' member (Just group) right)
  AccessToRight : HasAccess gid uid group -> HasAccess gid uid (MkGroup gid' member left (Just group))

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
        Yes Refl => Just DirectAccess
access (MkGroup groupId member (Just left) right) (LeftGroup leftElem) uid =
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
          Yes Refl => Just AccessToParent
access (MkGroup groupId member left (Just right)) (RightGroup rightElem) uid =
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
          Yes Refl => Just AccessToParent