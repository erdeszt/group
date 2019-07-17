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

data HA : (groupId : GroupId) -> Elem groupId group -> UserId -> Group -> Type where
  ATG : HA groupId ThisGroup userId (MkGroup groupId (Just userId) l r)
  ATPL : (elem : Elem groupId left) -> HA groupId (LeftGroup elem) userId (MkGroup gid (Just userId) (Just left) r)
  ATPR : (elem : Elem groupId right) -> HA groupId (RightGroup elem) userId (MkGroup gid (Just userId) l (Just right))
  ATL : HA groupId elem userId left -> HA groupId (LeftGroup elem) userId (MkGroup gid m (Just left) r)
  ATR : HA groupId elem userId right -> HA groupId (RightGroup elem) userId (MkGroup gid m l (Just right))

data HasDirectAccess : Elem groupId group -> UserId -> Group -> Type where
  DirectAccessToGroup : HasDirectAccess ThisGroup userId (MkGroup groupId (Just userId) l r)
  DirectAccessOnLeft : HasDirectAccess elem userId group -> HasDirectAccess (LeftGroup elem) userId (MkGroup gid m (Just group) r)
  DirectAccessOnRight : HasDirectAccess elem userId group -> HasDirectAccess (RightGroup elem) userId (MkGroup gid m l (Just group))

accessToElem : HasAccess groupId userId group -> Elem groupId group
accessToElem AccessToGroup = ThisGroup
accessToElem (AccessToParentLeft leftElem) = LeftGroup leftElem
accessToElem (AccessToParentRight rightElem) = RightGroup rightElem
accessToElem (AccessToLeft leftAccess) = LeftGroup (accessToElem leftAccess)
accessToElem (AccessToRight rightAccess) = RightGroup (accessToElem rightAccess)

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

directAccessToAccess : {groupId : GroupId}
                          -> {userId : UserId}
                          -> {group : Group}
                          -> {elem : Elem groupId group}
                          -> HasDirectAccess elem userId group -> HasAccess groupId userId group
directAccessToAccess {group = (MkGroup groupId (Just userId) l r)} DirectAccessToGroup = AccessToGroup
directAccessToAccess {group = (MkGroup gid m (Just l) r)} (DirectAccessOnLeft directAccess) = AccessToLeft (directAccessToAccess directAccess)
directAccessToAccess {group = (MkGroup gid m l (Just r))} (DirectAccessOnRight directAccess) = AccessToRight (directAccessToAccess directAccess)

ha : {groupId : GroupId}
  -> (group : Group)
  -> (elem : Elem groupId group)
  -> (userId : UserId)
  -> Maybe (HA groupId elem userId group)
ha (MkGroup groupId member l r) ThisGroup userId =
  case member of
    Nothing => Nothing
    Just memberId =>
      case decEq userId memberId of
        No contra => Nothing
        Yes Refl => Just ATG
ha (MkGroup gid member (Just left) r) (LeftGroup elem) userId =
  case member of
    Nothing => Nothing
    Just memberId =>
      case decEq userId memberId of
        No contra => map ATL (ha left elem userId)
        Yes Refl => Just (ATPL elem)
ha (MkGroup gid member l (Just right)) (RightGroup elem) userId =
  case member of
    Nothing => Nothing
    Just memberId =>
      case decEq userId memberId of
        No contra => map ATR (ha right elem userId)
        Yes Refl => Just (ATPR elem)

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

showHA : HA groupId elem userId group -> String
showHA ATG = "AccessToGroup"
showHA (ATPL elem) = "AccessToParentLeft (" <+> show elem <+> ")"
showHA (ATPR elem) = "AccessToParentRight (" <+> show elem <+> ")"
showHA (ATL access) = "AccessToLeft (" <+> showHA access <+> ")"
showHA (ATR access) = "AccessToRight (" <+> showHA access <+> ")"

showDirectAccess : HasDirectAccess elem userId group -> String
showDirectAccess DirectAccessToGroup = "DirectAccessToGroup"
showDirectAccess (DirectAccessOnLeft elem) = "DirectAccessOnLeft (" <+> showDirectAccess elem <+> ")"
showDirectAccess (DirectAccessOnRight elem) = "DirectAccessOnRight (" <+> showDirectAccess elem <+> ")"

showHasAccess : HasAccess groupId userId group -> String
showHasAccess AccessToGroup = "AccessToGroup"
showHasAccess (AccessToParentLeft leftElem) = "AccessToParentLeft (" <+> showElem leftElem <+> ")"
showHasAccess (AccessToParentRight rightElem) = "AccessToParentRight (" <+> showElem rightElem <+> ")"
showHasAccess (AccessToLeft leftAccess) = "AccessToLeft (" <+> showHasAccess leftAccess <+> ")"
showHasAccess (AccessToRight rightAccess) = "AccessToRight (" <+> showHasAccess rightAccess <+> ")"

Show (HasAccess groupId userId group) where
  show = showHasAccess