module GroupDistinctElem

import Group
import GroupElem

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
createDistinctElem ThisGroup (LeftGroup x) = Just ThisAndLeft
createDistinctElem ThisGroup (RightGroup x) = Just ThisAndRight
createDistinctElem (LeftGroup x) ThisGroup = Just LeftAndThis
createDistinctElem (LeftGroup x) (LeftGroup y) = map DifferInChildLL (createDistinctElem x y)
createDistinctElem (LeftGroup x) (RightGroup y) = Just LeftAndRight
createDistinctElem (RightGroup x) ThisGroup = Just RightAndThis
createDistinctElem (RightGroup x) (LeftGroup y) = Just RightAndLeft
createDistinctElem (RightGroup x) (RightGroup y) = map DifferInChildRR (createDistinctElem x y)