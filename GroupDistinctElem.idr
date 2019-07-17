module GroupDistinctElem

import Bifunctor
import Group
import GroupElem
import Or

%default total
%access public export

data DistinctElem : Elem g1 group -> Elem g2 group -> Type where
  ThisAndLeft : DistinctElem ThisGroup (LeftGroup group)
  ThisAndRight : DistinctElem ThisGroup (RightGroup group)
  LeftAndThis : DistinctElem (LeftGroup group) ThisGroup
  DifferInChildLL : DistinctElem g1 g2 -> DistinctElem (LeftGroup g1) (LeftGroup g2)
  LeftAndRight : DistinctElem (LeftGroup g1) (RightGroup g2)
  RightAndThis : DistinctElem (RightGroup group) ThisGroup
  RightAndLeft : DistinctElem (RightGroup g1) (LeftGroup g2)
  DifferInChildRR : DistinctElem g1 g2 -> DistinctElem (RightGroup g1) (RightGroup g2)

createDistinctElem : (elem1 : Elem g1 group) -> (elem2 : Elem g2 group) -> Maybe (DistinctElem elem1 elem2)
createDistinctElem ThisGroup ThisGroup = Nothing
createDistinctElem ThisGroup (LeftGroup _) = Just ThisAndLeft
createDistinctElem ThisGroup (RightGroup _) = Just ThisAndRight
createDistinctElem (LeftGroup _) ThisGroup = Just LeftAndThis
createDistinctElem (LeftGroup left1) (LeftGroup left2) = map DifferInChildLL (createDistinctElem left1 left2)
createDistinctElem (LeftGroup _) (RightGroup _) = Just LeftAndRight
createDistinctElem (RightGroup _) ThisGroup = Just RightAndThis
createDistinctElem (RightGroup _) (LeftGroup _) = Just RightAndLeft
createDistinctElem (RightGroup right1) (RightGroup right2) = map DifferInChildRR (createDistinctElem right1 right2)

distinctElemSymm
  : {aElem : Elem a group}
 -> {bElem : Elem b group}
 -> DistinctElem aElem bElem
 -> DistinctElem bElem aElem
distinctElemSymm {aElem = ThisGroup} {bElem = (LeftGroup _)} ThisAndLeft = LeftAndThis
distinctElemSymm {aElem = ThisGroup} {bElem = (RightGroup _)} ThisAndRight = RightAndThis
distinctElemSymm {aElem = (LeftGroup _)} {bElem = ThisGroup} LeftAndThis = ThisAndLeft
distinctElemSymm {aElem = (LeftGroup _)} {bElem = (LeftGroup _)} (DifferInChildLL diff) = DifferInChildLL (distinctElemSymm diff)
distinctElemSymm {aElem = (LeftGroup _)} {bElem = (RightGroup _)} LeftAndRight = RightAndLeft
distinctElemSymm {aElem = (RightGroup _)} {bElem = ThisGroup} RightAndThis = ThisAndRight
distinctElemSymm {aElem = (RightGroup _)} {bElem = (LeftGroup _)} RightAndLeft = LeftAndRight
distinctElemSymm {aElem = (RightGroup _)} {bElem = (RightGroup _)} (DifferInChildRR diff) = DifferInChildRR (distinctElemSymm diff)

distinctElemToTopElem : {aElem : Elem a group}
                     -> {bElem : Elem b group}
                     -> DistinctElem aElem bElem
                     -> Or (Elem a group) (Elem b group)
distinctElemToTopElem ThisAndLeft = OnlyLeft ThisGroup
distinctElemToTopElem ThisAndRight = OnlyLeft ThisGroup
distinctElemToTopElem LeftAndThis = OnlyRight ThisGroup
distinctElemToTopElem (DifferInChildLL diff) = bimap LeftGroup LeftGroup (distinctElemToTopElem diff)
distinctElemToTopElem {aElem = LeftGroup aElem'} {bElem = RightGroup bElem'} LeftAndRight = Both (LeftGroup aElem') (RightGroup bElem')
distinctElemToTopElem RightAndThis = OnlyRight ThisGroup
distinctElemToTopElem {aElem = RightGroup aElem'} {bElem = LeftGroup bElem'} RightAndLeft = Both (RightGroup aElem') (LeftGroup bElem')
distinctElemToTopElem (DifferInChildRR diff) = bimap RightGroup RightGroup (distinctElemToTopElem diff)
