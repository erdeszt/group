module GroupAccess

import Group
import GroupElem

%default total
%access public export

data HasAccess : (groupId : GroupId) -> UserId -> Elem groupId group -> Group -> Type where
  AccessToGroup : HasAccess groupId userId ThisGroup (MkGroup groupId (Just userId) l r)
  AccessToParentLeft : (elem : Elem groupId left) -> HasAccess groupId userId (LeftGroup elem) (MkGroup gid (Just userId) (Just left) r)
  AccessToParentRight : (elem : Elem groupId right) -> HasAccess groupId userId (RightGroup elem) (MkGroup gid (Just userId) l (Just right))
  AccessToLeft : HasAccess groupId userId elem left -> HasAccess groupId userId (LeftGroup elem) (MkGroup gid m (Just left) r)
  AccessToRight : HasAccess groupId userId elem right -> HasAccess groupId userId (RightGroup elem)  (MkGroup gid m l (Just right))

data HasDirectAccess : Elem groupId group -> UserId -> Group -> Type where
  DirectAccessToGroup : HasDirectAccess ThisGroup userId (MkGroup groupId (Just userId) l r)
  DirectAccessOnLeft : HasDirectAccess elem userId group -> HasDirectAccess (LeftGroup elem) userId (MkGroup gid m (Just group) r)
  DirectAccessOnRight : HasDirectAccess elem userId group -> HasDirectAccess (RightGroup elem) userId (MkGroup gid m l (Just group))

accessToElem : HasAccess groupId userId elem group -> Elem groupId group
accessToElem AccessToGroup = ThisGroup
accessToElem (AccessToParentLeft leftElem) = LeftGroup leftElem
accessToElem (AccessToParentRight rightElem) = RightGroup rightElem
accessToElem (AccessToLeft leftAccess) = LeftGroup (accessToElem leftAccess)
accessToElem (AccessToRight rightAccess) = RightGroup (accessToElem rightAccess)

directAccessToAccess : {groupId : GroupId}
                     -> {userId : UserId}
                     -> {group : Group}
                     -> {elem : Elem groupId group}
                     -> HasDirectAccess elem userId group -> HasAccess groupId userId elem group
directAccessToAccess {group = (MkGroup groupId (Just userId) l r)} DirectAccessToGroup = AccessToGroup
directAccessToAccess {group = (MkGroup gid m (Just l) r)} (DirectAccessOnLeft directAccess) = AccessToLeft (directAccessToAccess directAccess)
directAccessToAccess {group = (MkGroup gid m l (Just r))} (DirectAccessOnRight directAccess) = AccessToRight (directAccessToAccess directAccess)

createAccess : {groupId : GroupId}
            -> (group : Group)
            -> (elem : Elem groupId group)
            -> (userId : UserId)
            -> Maybe (HasAccess groupId userId elem group)
createAccess (MkGroup groupId member l r) ThisGroup userId =
  case member of
    Nothing => Nothing
    Just memberId =>
      case decEq userId memberId of
        No contra => Nothing
        Yes Refl => Just AccessToGroup
createAccess (MkGroup gid member (Just left) r) (LeftGroup elem) userId =
  case member of
    Nothing => Nothing
    Just memberId =>
      case decEq userId memberId of
        No contra => map AccessToLeft (createAccess left elem userId)
        Yes Refl => Just (AccessToParentLeft elem)
createAccess (MkGroup gid member l (Just right)) (RightGroup elem) userId =
  case member of
    Nothing => Nothing
    Just memberId =>
      case decEq userId memberId of
        No contra => map AccessToRight (createAccess right elem userId)
        Yes Refl => Just (AccessToParentRight elem)

createDirectAccess : {groupId : GroupId}
                  -> (group : Group)
                  -> (elem : Elem groupId group)
                  -> (userId : UserId)
                  -> Maybe (HasDirectAccess elem userId group)
createDirectAccess (MkGroup groupId member l r) ThisGroup userId =
  case member of
    Nothing => Nothing
    Just memberId =>
      case decEq userId memberId of
        No contra => Nothing
        Yes Refl => Just DirectAccessToGroup
createDirectAccess (MkGroup gid m (Just l) r) (LeftGroup elem) userId = map DirectAccessOnLeft (createDirectAccess l elem userId)
createDirectAccess (MkGroup gid m l (Just r)) (RightGroup elem) userId = map DirectAccessOnRight (createDirectAccess r elem userId)

showDirectAccess : HasDirectAccess elem userId group -> String
showDirectAccess DirectAccessToGroup = "DirectAccessToGroup"
showDirectAccess (DirectAccessOnLeft elem) = "DirectAccessOnLeft (" <+> showDirectAccess elem <+> ")"
showDirectAccess (DirectAccessOnRight elem) = "DirectAccessOnRight (" <+> showDirectAccess elem <+> ")"

showHasAccess : HasAccess groupId userId elem group -> String
showHasAccess AccessToGroup = "AccessToGroup"
showHasAccess (AccessToParentLeft leftElem) = "AccessToParentLeft (" <+> showElem leftElem <+> ")"
showHasAccess (AccessToParentRight rightElem) = "AccessToParentRight (" <+> showElem rightElem <+> ")"
showHasAccess (AccessToLeft leftAccess) = "AccessToLeft (" <+> showHasAccess leftAccess <+> ")"
showHasAccess (AccessToRight rightAccess) = "AccessToRight (" <+> showHasAccess rightAccess <+> ")"