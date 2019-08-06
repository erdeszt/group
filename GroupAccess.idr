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
  NoMember : {userId : UserId} -> (contra : Just userId = Nothing -> Void) ->  GroupMember Nothing userId
  NotThisMember : {userId, otherUserId : UserId} -> (contra : otherUserId = userId -> Void) -> GroupMember (Just otherUserId) userId
  ThisMember : GroupMember (Just userId) userId

groupMember : (member : Maybe UserId) -> (userId : UserId) -> GroupMember member userId
groupMember Nothing userId = NoMember (\prf => uninhabited prf)
groupMember (Just memberId) userId =
  case decEq memberId userId of
    (Yes Refl) => ThisMember
    (No contra) => NotThisMember contra

justsEq : Just a = Just b -> a = b
justsEq Refl = Refl

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

data Member : UserId -> Group -> Type where
  MemberHere : Member userId (MkGroup g (Just userId) l r)
  MemberInLeft : Member userId group -> Member userId (MkGroup g m (Just group) r)
  MemberInRight : Member userId group -> Member userId (MkGroup g m l (Just group))

createMember : (userId : UserId) -> (group : Group) -> Maybe (Member userId group)
createMember userId (MkGroup groupId member Nothing Nothing) with (groupMember member userId)
  createMember userId (MkGroup groupId Nothing Nothing Nothing) | NoMember = Nothing
  createMember userId (MkGroup groupId (Just otherUserId) Nothing Nothing) | (NotThisMember contra) = Nothing
  createMember userId (MkGroup groupId (Just userId) Nothing Nothing) | ThisMember = Just MemberHere
createMember userId (MkGroup groupId member Nothing (Just right)) with (groupMember member userId)
  createMember userId (MkGroup groupId Nothing Nothing (Just right)) | NoMember = map MemberInRight (createMember userId right)
  createMember userId (MkGroup groupId (Just otherUserId) Nothing (Just right)) | (NotThisMember contra) = map MemberInRight (createMember userId right)
  createMember userId (MkGroup groupId (Just userId) Nothing (Just right)) | ThisMember = Just MemberHere
createMember userId (MkGroup groupId member (Just left) Nothing) with (groupMember member userId)
  createMember userId (MkGroup groupId Nothing (Just left) Nothing) | NoMember = map MemberInLeft (createMember userId left)
  createMember userId (MkGroup groupId (Just otherUserId) (Just left) Nothing) | (NotThisMember contra) = map MemberInLeft (createMember userId left)
  createMember userId (MkGroup groupId (Just userId) (Just left) Nothing) | ThisMember = Just MemberHere
createMember userId (MkGroup groupId member (Just left) (Just right)) with (groupMember member userId)
  createMember userId (MkGroup groupId Nothing (Just left) (Just right)) | NoMember =
    map MemberInRight (createMember userId right) <|> map MemberInLeft (createMember userId left)
  createMember userId (MkGroup groupId (Just otherUserId) (Just left) (Just right)) | (NotThisMember contra) =
    map MemberInRight (createMember userId right) <|> map MemberInLeft (createMember userId left)
  createMember userId (MkGroup groupId (Just userId) (Just left) (Just right)) | ThisMember = Just MemberHere

-- member_to_access : {userId : UserId} -> {group : Group} -> Member userId group -> (groupId : GroupId ** (elem : Elem groupId group ** HasAccess groupId userId elem group))

solve_map : {a : Type} -> (F : a -> b) -> (y : a) -> (x : Maybe a) -> (prf : x = Just y) -> map F x = Just (F y)
solve_map f y Nothing Refl impossible
solve_map f y (Just y) Refl = Refl

solve_left : (createAccess left leftElem userId = Just leftAccess)
     -> map AccessOnLeft (createAccess left leftElem userId) = Just (AccessOnLeft leftAccess)
solve_left {userId} {left} {leftElem} {leftAccess} prf =
  solve_map AccessOnLeft leftAccess (createAccess left leftElem userId) prf

solve_right : (createAccess right rightElem userId = Just rightAccess)
     -> map AccessOnRight (createAccess right rightElem userId) = Just (AccessOnRight rightAccess)
solve_right {userId} {right} {rightElem} {rightAccess} prf =
  solve_map AccessOnRight rightAccess (createAccess right rightElem userId) prf

thm_create_access_correct : {groupId : GroupId}
                         -> {userId : UserId}
                         -> (group : Group)
                         -> (elem : Elem groupId group)
                         -> (access : HasAccess groupId userId elem group)
                         -> Either (createAccess group elem userId = Just access) (parentId : GroupId ** (parentElem : Elem parentId group ** (Child elem parentElem group, HasAccess parentId userId parentElem group)))
thm_create_access_correct {userId = userId} (MkGroup groupId (Just userId) l r) ThisGroup AccessToGroup with (groupMember (Just userId) userId)
  thm_create_access_correct {userId = userId} (MkGroup groupId (Just userId) l r) ThisGroup AccessToGroup | (NotThisMember contra) = Left (absurd (contra Refl))
  thm_create_access_correct {userId = userId} (MkGroup groupId (Just userId) l r) ThisGroup AccessToGroup | ThisMember = Left Refl
thm_create_access_correct {userId = userId} (MkGroup h (Just userId) (Just left) r) (LeftGroup x) (AccessToParentLeft x) with (groupMember (Just userId) userId)
  thm_create_access_correct {userId = userId} (MkGroup h (Just userId) (Just left) r) (LeftGroup x) (AccessToParentLeft x) | (NotThisMember contra) = Left (absurd (contra Refl))
  thm_create_access_correct {userId = userId} (MkGroup h (Just userId) (Just left) r) (LeftGroup x) (AccessToParentLeft x) | ThisMember = Left Refl
thm_create_access_correct {userId = userId} (MkGroup h (Just userId) l (Just right)) (RightGroup x) (AccessToParentRight x) with (groupMember (Just userId) userId)
  thm_create_access_correct {userId = userId} (MkGroup h (Just userId) l (Just right)) (RightGroup x) (AccessToParentRight x) | (NotThisMember contra) = Left (absurd (contra Refl))
  thm_create_access_correct {userId = userId} (MkGroup h (Just userId) l (Just right)) (RightGroup x) (AccessToParentRight x) | ThisMember = Left Refl
thm_create_access_correct {userId = userId} (MkGroup h m (Just left) r) (LeftGroup leftElem) (AccessOnLeft leftAccess) with (groupMember m userId)
  thm_create_access_correct {userId = userId} (MkGroup h Nothing (Just left) r) (LeftGroup leftElem) (AccessOnLeft leftAccess) | (NoMember contra) =
    case thm_create_access_correct left leftElem leftAccess of
      Left direct => Left (solve_left direct)
      Right (parentId ** (parentElem ** (child, parentAccess))) => Right (parentId ** (LeftGroup parentElem ** (PrefixLeft child, AccessOnLeft parentAccess)))
  thm_create_access_correct {userId = userId} (MkGroup h (Just otherUserId) (Just left) r) (LeftGroup leftElem) (AccessOnLeft leftAccess) | (NotThisMember contra) =
    case thm_create_access_correct left leftElem leftAccess of
      Left direct => Left (solve_left direct)
      Right (parentId ** (parentElem ** (child, parentAccess))) => Right (parentId ** (LeftGroup parentElem ** (PrefixLeft child, AccessOnLeft parentAccess)))
  thm_create_access_correct {userId = userId} (MkGroup h (Just userId) (Just left) r) (LeftGroup leftElem) (AccessOnLeft leftAccess) | ThisMember =
    Right (h ** ThisGroup ** (ParentEndsHereChildOnLeft leftElem, AccessToGroup))
thm_create_access_correct {userId = userId} (MkGroup h m l (Just right)) (RightGroup rightElem) (AccessOnRight rightAccess) with (groupMember m userId)
  thm_create_access_correct {userId = userId} (MkGroup h Nothing l (Just right)) (RightGroup rightElem) (AccessOnRight rightAccess) | (NoMember contra) =
    case thm_create_access_correct right rightElem rightAccess of
      Left direct => Left (solve_right direct)
      Right (parentId ** (parentElem ** (child, parentAccess))) => Right (parentId ** (RightGroup parentElem ** (PrefixRight child, AccessOnRight parentAccess)))
  thm_create_access_correct {userId = userId} (MkGroup h (Just otherUserId) l (Just right)) (RightGroup rightElem) (AccessOnRight rightAccess) | (NotThisMember contra) =
    case thm_create_access_correct right rightElem rightAccess of
      Left direct => Left (solve_right direct)
      Right (parentId ** (parentElem ** (child, parentAccess))) => Right (parentId ** (RightGroup parentElem ** (PrefixRight child, AccessOnRight parentAccess)))
  thm_create_access_correct {userId = userId} (MkGroup h (Just userId) l (Just right)) (RightGroup rightElem) (AccessOnRight rightAccess) | ThisMember =
    Right (h ** ThisGroup ** (ParentEndsHereChildOnRight rightElem, AccessToGroup))

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
