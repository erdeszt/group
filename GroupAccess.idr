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

data HasDirectAccess : Elem groupId group -> UserId -> Group -> Type where
  DirectAccessToGroup : HasDirectAccess ThisGroup userId (MkGroup groupId (Just userId) l r)
  DirectAccessOnLeft : HasDirectAccess elem userId group -> HasDirectAccess (LeftGroup elem) userId (MkGroup gid m (Just group) r)
  DirectAccessOnRight : HasDirectAccess elem userId group -> HasDirectAccess (RightGroup elem) userId (MkGroup gid m l (Just group))

hasAccessToElem : HasAccess groupId userId group -> Elem groupId group
hasAccessToElem AccessToGroup = ThisGroup
hasAccessToElem (AccessToParentLeft leftElem) = LeftGroup leftElem
hasAccessToElem (AccessToParentRight rightElem) = RightGroup rightElem
hasAccessToElem (AccessToLeft leftAccess) = LeftGroup (hasAccessToElem leftAccess)
hasAccessToElem (AccessToRight rightAccess) = RightGroup (hasAccessToElem rightAccess)

directAccess : {groupId : GroupId}
            -> (group : Group)
            -> (elem : Elem groupId group)
            -> (userId : UserId)
            -> Maybe (HasDirectAccess elem userId group)
directAccess (MkGroup groupId member l r) ThisGroup userId =
  case member of
    Nothing => Nothing
    Just memberId =>
      case decEq userId memberId of
        No contra => Nothing
        Yes Refl => Just DirectAccessToGroup
directAccess (MkGroup gid m (Just l) r) (LeftGroup elem) userId = map DirectAccessOnLeft (directAccess l elem userId)
directAccess (MkGroup gid m l (Just r)) (RightGroup elem) userId = map DirectAccessOnRight (directAccess r elem userId)

hasDirectAccessToHasAccess : {groupId : GroupId}
                          -> {userId : UserId}
                          -> {group : Group}
                          -> {elem : Elem groupId group}
                          -> HasDirectAccess elem userId group -> HasAccess groupId userId group
hasDirectAccessToHasAccess {group = (MkGroup groupId (Just userId) l r)} DirectAccessToGroup = AccessToGroup
hasDirectAccessToHasAccess {group = (MkGroup gid m (Just l) r)} (DirectAccessOnLeft directAccess) = AccessToLeft (hasDirectAccessToHasAccess directAccess)
hasDirectAccessToHasAccess {group = (MkGroup gid m l (Just r))} (DirectAccessOnRight directAccess) = AccessToRight (hasDirectAccessToHasAccess directAccess)

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

Show (HasAccess groupId userId group) where
  show  AccessToGroup = "AccessToGroup"
  show (AccessToParentLeft leftElem) = "AccessToParentLeft (" <+> show leftElem <+> ")"
  show (AccessToParentRight rightElem) = "AccessToParentRight (" <+> show rightElem <+> ")"

  show (AccessToLeft leftAccess) = "AccessToLeft (" <+> show leftAccess <+> ")"
  show (AccessToRight rightAccess) = "AccessToRight (" <+> show rightAccess <+> ")"