module BackboneQueues

%access public export
%default total

KeyValuePair : Type
KeyValuePair = (String, String)

TeamName : Type
TeamName = String

QueueName : Type
QueueName = String

Priority : Type
Priority = Nat

ImageId : Type
ImageId = Nat

DermId : Type
DermId = Nat

Url : Type
Url = String

record ImageWithProps where
  constructor MkImageWithProps
  imageId: ImageId
  properties : List KeyValuePair

record WorkItem where
  constructor MkWorkItem
  images : List ImageWithProps
  pluginUrl : Url
  pluginProperties : List KeyValuePair

data EnqueueFor : Type where 
  EnqueueForDerms : List DermId -> EnqueueFor
  EnqueueForProject : (requiredEvaluationsPerWorkItem : Nat) -> EnqueueFor

interface BackboneQueueApi api where
  emptyQueue : api
  enqueue : api -> List WorkItem -> TeamName -> Maybe QueueName -> Priority -> EnqueueFor -> api
  getNext : api -> TeamName -> Maybe QueueName -> DermId -> Maybe WorkItem

  requirement_getNext_from_empty_queue_is_always_Nothing : {teamName : TeamName} 
                                                        -> {queueName : Maybe QueueName}
                                                        -> {dermId : DermId}
                                                        -> (getNext emptyQueue teamName queueName dermId) = Nothing

  requirement_non_interference_between_derms : {teamName : TeamName}
                                            -> {queueName : Maybe QueueName}
                                            -> {dermId : DermId}
                                            -> {dermIdOther : DermId}  -- What about dermId = dermIdOther
                                            -> {otherDermsItems : List WorkItem}
                                            -> {dermsWorkItem : WorkItem}
                                            -> let queue = (enqueue emptyQueue otherDermsItems teamName queueName 1 (EnqueueForDerms [dermIdOther])) in
                                               let queue' = enqueue queue [dermsWorkItem] teamName queueName 1 (EnqueueForDerms [dermId]) in
                                               (getNext queue' teamName queueName dermId) = (Just dermsWorkItem)
                                            
record QueueItem where
  constructor MkQueueItem
  workItem : WorkItem
  teamName : TeamName
  queueName : Maybe QueueName
  priority : Priority
  dermId : Maybe DermId

data LBA = MkLBA (List QueueItem) -- List Based (implementation of the) Api

enqueueForAllDerms : LBA -> WorkItem -> TeamName -> Maybe QueueName -> Priority -> List DermId -> LBA
enqueueForAllDerms state workItem teamname queueName priority [] = state
enqueueForAllDerms (MkLBA xs) workItem teamName queueName priority (derm :: derms) = 
  let queueItem = MkQueueItem workItem teamName queueName priority (Just derm) in
  enqueueForAllDerms (MkLBA (queueItem :: xs)) workItem teamName queueName priority derms

-- lemma_dec_eq_reflexive : {a : DermId} -> case decEq a a of { Yes _ => aResult; No _ => bResult } = aResult
-- lemma_dec_eq_reflexive = ?wattt

BackboneQueueApi LBA where
  emptyQueue = MkLBA []




  enqueue state [] teamName queueName priority enqueueFor = state
  -- TODO: Non empty list for derms, work items
  enqueue state (x :: xs) teamName queueName priority (EnqueueForDerms derms) =
    let state' = enqueueForAllDerms state x teamName queueName priority derms in
    enqueue state' xs teamName queueName priority (EnqueueForDerms derms)
  enqueue state (x :: xs) teamName queueName priority (EnqueueForProject requiredEvaluationsPerWorkItem) = ?imp_2

  getNext (MkLBA []) teamName queueName dermId = Nothing
  getNext (MkLBA ((MkQueueItem workItem x y priority Nothing) :: ws)) teamName queueName dermId = Nothing -- NOTE: Incomplete, no project queues yet
  getNext st@(MkLBA ((MkQueueItem workItem x y priority (Just z)) :: ws)) teamName queueName dermId =
    case decEq z dermId of
      Yes Refl => Just workItem
      -- NOTE: FIX THIS
      No _ => getNext (assert_smaller st (MkLBA ws)) teamName queueName dermId
    

  requirement_getNext_from_empty_queue_is_always_Nothing = Refl

  -- NOTE(decEqSelfIsYes): https://github.com/idris-lang/Idris-dev/issues/4394
  requirement_non_interference_between_derms {otherDermsItems = []} {dermId} =
    -- rewrite decEqSelfIsYes {x=dermId} in
    ?wat
    -- case decEq dermId dermId of
    --   Yes Refl => ?wasaat
    --   No _ => ?noo
  requirement_non_interference_between_derms {otherDermsItems = (x :: xs)} = ?wat_2
