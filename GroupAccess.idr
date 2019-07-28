module GroupAccess

import Group
import GroupChild
import GroupElem

%default total
%access public export

record AccessToken where
  constructor MkToken
  userId : UserId
  isAdmin : Bool

data UserToken : UserId -> AccessToken -> Type where
  MkUserToken : (userId : UserId) -> UserToken userId (MkToken userId isAdmin)

data HasAccess : (groupId : GroupId) -> UserId -> Elem groupId group -> Group -> Type where
  AccessToGroup : HasAccess groupId userId ThisGroup (MkGroup groupId (Just userId) l r)
  AccessToParentLeft : (elem : Elem groupId left) -> HasAccess groupId userId (LeftGroup elem) (MkGroup gid (Just userId) (Just left) r)
  AccessToParentRight : (elem : Elem groupId right) -> HasAccess groupId userId (RightGroup elem) (MkGroup gid (Just userId) l (Just right))
  AccessOnLeft : HasAccess groupId userId elem left -> HasAccess groupId userId (LeftGroup elem) (MkGroup gid m (Just left) r)
  AccessOnRight : HasAccess groupId userId elem right -> HasAccess groupId userId (RightGroup elem)  (MkGroup gid m l (Just right))

data HasTokenAccess : (token : AccessToken) -> {userToken : UserToken userId token} -> (groupId : GroupId) -> Elem groupId group -> Group -> Type where
  AdminAccess : HasTokenAccess (MkToken userId True) groupId elem group
  RegularAccess : HasAccess groupId userId elem group -> HasTokenAccess (MkToken userId isAdmin) groupId elem group

-- Note: No mapping for AdminAccess
tokenAccessToAccess : {token : AccessToken} -> {prf : UserToken userId token} -> HasTokenAccess token groupId elem group -> Maybe (HasAccess groupId userId elem group)
tokenAccessToAccess {token = (MkToken userId True)} {prf = prf} AdminAccess = Nothing
tokenAccessToAccess {token = (MkToken userId isAdmin)} {prf = (MkUserToken userId)} (RegularAccess access) = Just access

accessToTokenAccess : {token : AccessToken} -> {prf : UserToken userId token} -> HasAccess groupId userId elem group -> HasTokenAccess token groupId elem group
accessToTokenAccess {token = (MkToken userId isAdmin)} {prf = (MkUserToken userId)} access = RegularAccess access

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

directAccessToElem : {elem : Elem g group} -> HasDirectAccess g u elem group -> Elem g group
directAccessToElem directAccess = accessToElem (directAccessToAccess directAccess)

directAccessExtendsToChildren : {g, g' : GroupId}
                             -> {u : UserId}
                             -> {group : Group}
                             -> {childElem : Elem g' group}
                             -> {parentElem : Elem g group}
                             -> HasDirectAccess g u parentElem group
                             -> Child childElem parentElem group
                             -> HasAccess g' u childElem group
directAccessExtendsToChildren directAccess child = accessExtendsToChildren (directAccessToAccess directAccess) child

data GroupMember : Maybe UserId -> UserId -> Type where
  NoMember : GroupMember Nothing userId
  NotThisMember : {userId, otherUserId : UserId} -> (contra : otherUserId = userId -> Void) -> GroupMember (Just otherUserId) userId
  ThisMember : GroupMember (Just userId) userId

groupMember : (member : Maybe UserId) -> (userId : UserId) -> GroupMember member userId
groupMember Nothing userId = NoMember
groupMember (Just memberId) userId =
  case decEq memberId userId of
    (Yes Refl) => ThisMember
    (No contra) => NotThisMember contra

createAccess : {groupId : GroupId}
            -> (group : Group)
            -> (elem : Elem groupId group)
            -> (userId : UserId)
            -> Maybe (HasAccess groupId userId elem group)
createAccess (MkGroup groupId m l r) ThisGroup userId with (groupMember m userId)
  createAccess (MkGroup groupId (Just userId) l r) ThisGroup userId  | ThisMember = Just AccessToGroup
  createAccess (MkGroup groupId _ l r) ThisGroup userId              | _          = Nothing
createAccess (MkGroup gid m (Just left) r) (LeftGroup elem) userId with (groupMember m userId)
  createAccess (MkGroup gid (Just userId) (Just left) r) (LeftGroup elem) userId  | ThisMember = Just (AccessToParentLeft elem)
  createAccess (MkGroup gid _ (Just left) r) (LeftGroup elem) userId              | _          = map AccessOnLeft (createAccess left elem userId)
createAccess (MkGroup gid m l (Just right)) (RightGroup elem) userId with (groupMember m userId)
  createAccess (MkGroup gid (Just userId) l (Just right)) (RightGroup elem) userId | ThisMember = Just (AccessToParentRight elem)
  createAccess (MkGroup gid _ l (Just right)) (RightGroup elem) userId             | _          = map AccessOnRight (createAccess right elem userId)

createAccess2 : {groupId : GroupId}
            -> (group : Group)
            -> (elem : Elem groupId group)
            -> (userId : UserId)
            -> Maybe (HasAccess groupId userId elem group)
createAccess2 (MkGroup groupId m l r) ThisGroup userId with (groupMember m userId)
  createAccess2 (MkGroup groupId (Just userId) l r) ThisGroup userId  | ThisMember = Just AccessToGroup
  createAccess2 (MkGroup groupId _ l r) ThisGroup userId              | _          = Nothing
createAccess2 (MkGroup gid m (Just left) r) (LeftGroup elem) userId with (groupMember m userId)
  createAccess2 (MkGroup gid (Just userId) (Just left) r) (LeftGroup elem) userId  | ThisMember = Just (AccessToParentLeft elem)
  createAccess2 (MkGroup gid _ (Just left) r) (LeftGroup elem) userId              | _  with (createAccess2 left elem userId)
    | Nothing = Nothing
    | (Just access) = Just (AccessOnLeft access)
createAccess2 (MkGroup gid m l (Just right)) (RightGroup elem) userId with (groupMember m userId)
  createAccess2 (MkGroup gid (Just userId) l (Just right)) (RightGroup elem) userId | ThisMember = Just (AccessToParentRight elem)
  createAccess2 (MkGroup gid _ l (Just right)) (RightGroup elem) userId             | _ with (createAccess2 right elem userId)
    | Nothing = Nothing
    | (Just access) = Just (AccessOnRight access)

thm_create_access_correct : {groupId : GroupId}
                         -> {userId : UserId}
                         -> {group : Group}
                         -> (elem : Elem groupId group)
                         -> (access : HasAccess groupId userId elem group)
                         -> (createAccess2 group elem userId = Just access)
thm_create_access_correct {group = (MkGroup groupId (Just userId) l r)} {userId = userId} ThisGroup AccessToGroup with (groupMember (Just userId) userId)
  thm_create_access_correct {group = (MkGroup groupId (Just userId) l r)} {userId = userId} ThisGroup AccessToGroup | (NotThisMember contra) = absurd (contra Refl)
  thm_create_access_correct {group = (MkGroup groupId (Just userId) l r)} {userId = userId} ThisGroup AccessToGroup | ThisMember = Refl
thm_create_access_correct {group = (MkGroup h (Just userId) (Just left) r)} {userId = userId} (LeftGroup elem) (AccessToParentLeft elem) with (groupMember (Just userId) userId)
  thm_create_access_correct {group = (MkGroup h (Just userId) (Just left) r)} {userId = userId} (LeftGroup elem) (AccessToParentLeft elem) | (NotThisMember contra) = absurd (contra Refl)
  thm_create_access_correct {group = (MkGroup h (Just userId) (Just left) r)} {userId = userId} (LeftGroup elem) (AccessToParentLeft elem) | ThisMember = Refl
thm_create_access_correct {group = (MkGroup h (Just userId) l (Just right))} {userId = userId} (RightGroup elem) (AccessToParentRight elem) with (groupMember (Just userId) userId)
  thm_create_access_correct {group = (MkGroup h (Just userId) l (Just right))} {userId = userId} (RightGroup elem) (AccessToParentRight elem) | (NotThisMember contra) = absurd (contra Refl)
  thm_create_access_correct {group = (MkGroup h (Just userId) l (Just right))} {userId = userId} (RightGroup elem) (AccessToParentRight elem) | ThisMember = Refl
thm_create_access_correct {group = (MkGroup h m (Just x) r)} {userId = userId} (LeftGroup y) (AccessOnLeft z) with (groupMember m userId)
  thm_create_access_correct {group = (MkGroup h Nothing (Just x) r)} {userId = userId} (LeftGroup y) (AccessOnLeft z) | NoMember =
    let thm' = thm_create_access_correct y z in
    rewrite thm' in
    Refl
  thm_create_access_correct {group = (MkGroup h (Just otherUserId) (Just x) r)} {userId = userId} (LeftGroup y) (AccessOnLeft z) | (NotThisMember contra) =
    let thm' = thm_create_access_correct y z in
    rewrite thm' in
    Refl
  thm_create_access_correct {group = (MkGroup h (Just userId) (Just x) r)} {userId = userId} (LeftGroup y) (AccessOnLeft z) | ThisMember =
    -- let el = accessToElem z in
    -- let el_plus = accessToElem (AccessOnLeft z) in
    -- cong {f=Just} ?lemma_access_multi
    let thm' = thm_create_access_correct {group=x} y z in
    -- rewrite thm' in
    -- The issue here GroupMember has no relation to HasAccess so it doesn't know it cannot be ThisGroup
    ?watta
thm_create_access_correct {group = (MkGroup h m l (Just x))} {userId = userId} (RightGroup y) (AccessOnRight z) = ?rhs_5


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