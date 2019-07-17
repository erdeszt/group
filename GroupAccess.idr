module GroupAccess

import Group
import GroupChild
import GroupElem

%default total
%access public export

data HasAccess : (groupId : GroupId) -> UserId -> Elem groupId group -> Group -> Type where
  AccessToGroup : HasAccess groupId userId ThisGroup (MkGroup groupId (Just userId) l r)
  AccessToParentLeft : (elem : Elem groupId left) -> HasAccess groupId userId (LeftGroup elem) (MkGroup gid (Just userId) (Just left) r)
  AccessToParentRight : (elem : Elem groupId right) -> HasAccess groupId userId (RightGroup elem) (MkGroup gid (Just userId) l (Just right))
  AccessOnLeft : HasAccess groupId userId elem left -> HasAccess groupId userId (LeftGroup elem) (MkGroup gid m (Just left) r)
  AccessOnRight : HasAccess groupId userId elem right -> HasAccess groupId userId (RightGroup elem)  (MkGroup gid m l (Just right))

data HasDirectAccess : (groupId : GroupId) -> UserId -> Elem groupId group -> Group -> Type where
  DirectAccessToGroup : HasDirectAccess groupId userId ThisGroup (MkGroup groupId (Just userId) l r)
  DirectAccessOnLeft : HasDirectAccess groupId userId elem group -> HasDirectAccess groupId userId (LeftGroup elem) (MkGroup gid m (Just group) r)
  DirectAccessOnRight : HasDirectAccess groupId userId elem group -> HasDirectAccess groupId userId (RightGroup elem) (MkGroup gid m l (Just group))

accessToElem : HasAccess groupId userId elem group -> Elem groupId group
accessToElem AccessToGroup = ThisGroup
accessToElem (AccessToParentLeft leftElem) = LeftGroup leftElem
accessToElem (AccessToParentRight rightElem) = RightGroup rightElem
accessToElem (AccessOnLeft leftAccess) = LeftGroup (accessToElem leftAccess)
accessToElem (AccessOnRight rightAccess) = RightGroup (accessToElem rightAccess)

directAccessToAccess : {groupId : GroupId}
                    -> {userId : UserId}
                    -> {group : Group}
                    -> {elem : Elem groupId group}
                    -> HasDirectAccess groupId userId elem group -> HasAccess groupId userId elem group
directAccessToAccess {group = (MkGroup groupId (Just userId) l r)} DirectAccessToGroup = AccessToGroup
directAccessToAccess {group = (MkGroup gid m (Just l) r)} (DirectAccessOnLeft directAccess) = AccessOnLeft (directAccessToAccess directAccess)
directAccessToAccess {group = (MkGroup gid m l (Just r))} (DirectAccessOnRight directAccess) = AccessOnRight (directAccessToAccess directAccess)

directAccessExtendsToChildren : {g, g' : GroupId}
                             -> {u : UserId}
                             -> {group : Group}
                             -> {childElem : Elem g' group}
                             -> {parentElem : Elem g group}
                             -> HasDirectAccess g u parentElem group
                             -> Child childElem parentElem group
                             -> HasAccess g' u childElem group
directAccessExtendsToChildren {group = (MkGroup g (Just u) (Just left) r)} DirectAccessToGroup (ParentEndsHereChildOnLeft elem) = AccessToParentLeft elem
directAccessExtendsToChildren {group = (MkGroup g (Just u) l (Just right))} DirectAccessToGroup (ParentEndsHereChildOnRight elem) = AccessToParentRight elem
directAccessExtendsToChildren {group = (MkGroup gid m (Just left) r)} (DirectAccessOnLeft directAccess) (PrefixLeft child) = AccessOnLeft (directAccessExtendsToChildren directAccess child)
directAccessExtendsToChildren {group = (MkGroup gid m l (Just right))} (DirectAccessOnRight directAccess) (PrefixRight child) = AccessOnRight (directAccessExtendsToChildren directAccess child)

accessExtendsToChildren : {g, g' : GroupId}
                       -> {u : UserId}
                       -> {group : Group}
                       -> {childElem : Elem g' group}
                       -> {parentElem : Elem g group}
                       -> HasAccess g u parentElem group
                       -> Child childElem parentElem group
                       -> HasAccess g' u childElem group
accessExtendsToChildren {group = (MkGroup g (Just u) (Just group) r)} {parentElem = ThisGroup} {childElem = (LeftGroup x)} AccessToGroup (ParentEndsHereChildOnLeft x) = AccessToParentLeft x
accessExtendsToChildren {group = (MkGroup g (Just u) l (Just group))} {parentElem = ThisGroup} {childElem = (RightGroup x)} AccessToGroup (ParentEndsHereChildOnRight x) = AccessToParentRight x
accessExtendsToChildren {group = (MkGroup h (Just u) (Just left) r)} {parentElem = (LeftGroup elem)} {childElem = (LeftGroup x)} (AccessToParentLeft elem) (PrefixLeft y) = AccessToParentLeft x
accessExtendsToChildren {group = (MkGroup h (Just u) l (Just right))} {parentElem = (RightGroup elem)} {childElem = (RightGroup x)} (AccessToParentRight elem) (PrefixRight y) = AccessToParentRight x
accessExtendsToChildren {group = (MkGroup h m (Just x) r)} {parentElem = (LeftGroup elem)} {childElem = (LeftGroup z)} (AccessOnLeft y) (PrefixLeft w) = AccessOnLeft (accessExtendsToChildren y w)
accessExtendsToChildren {group = (MkGroup h m l (Just x))} {parentElem = (RightGroup elem)} {childElem = (RightGroup z)} (AccessOnRight y) (PrefixRight w) = AccessOnRight (accessExtendsToChildren y w)

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
        No contra => map AccessOnLeft (createAccess left elem userId)
        Yes Refl => Just (AccessToParentLeft elem)
createAccess (MkGroup gid member l (Just right)) (RightGroup elem) userId =
  case member of
    Nothing => Nothing
    Just memberId =>
      case decEq userId memberId of
        No contra => map AccessOnRight (createAccess right elem userId)
        Yes Refl => Just (AccessToParentRight elem)

createDirectAccess : {groupId : GroupId}
                  -> (group : Group)
                  -> (elem : Elem groupId group)
                  -> (userId : UserId)
                  -> Maybe (HasDirectAccess groupId userId elem group)
createDirectAccess (MkGroup groupId member l r) ThisGroup userId =
  case member of
    Nothing => Nothing
    Just memberId =>
      case decEq userId memberId of
        No contra => Nothing
        Yes Refl => Just DirectAccessToGroup
createDirectAccess (MkGroup gid m (Just l) r) (LeftGroup elem) userId = map DirectAccessOnLeft (createDirectAccess l elem userId)
createDirectAccess (MkGroup gid m l (Just r)) (RightGroup elem) userId = map DirectAccessOnRight (createDirectAccess r elem userId)

showHasDirectAccess : HasDirectAccess groupId userId elem group -> String
showHasDirectAccess DirectAccessToGroup = "DirectAccessToGroup"
showHasDirectAccess (DirectAccessOnLeft elem) = "DirectAccessOnLeft (" <+> showHasDirectAccess elem <+> ")"
showHasDirectAccess (DirectAccessOnRight elem) = "DirectAccessOnRight (" <+> showHasDirectAccess elem <+> ")"

showHasAccess : HasAccess groupId userId elem group -> String
showHasAccess AccessToGroup = "AccessToGroup"
showHasAccess (AccessToParentLeft leftElem) = "AccessToParentLeft (" <+> showElem leftElem <+> ")"
showHasAccess (AccessToParentRight rightElem) = "AccessToParentRight (" <+> showElem rightElem <+> ")"
showHasAccess (AccessOnLeft leftAccess) = "AccessOnLeft (" <+> showHasAccess leftAccess <+> ")"
showHasAccess (AccessOnRight rightAccess) = "AccessOnRight (" <+> showHasAccess rightAccess <+> ")"