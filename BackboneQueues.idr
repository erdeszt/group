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
                                                        -> (getNext emptyQueue teamNam queueName dermId) = Nothing


data LBA = MkLBA (List WorkItem) -- List Based (implementation of the) Api

BackboneQueueApi LBA where
  emptyQueue = MkLBA []

  enqueue state workItems teamName queueName priority enqueueFor = ?impl_enqueue

  getNext (MkLBA []) teamName queueName dermId = Nothing
  getNext (MkLBA (w :: ws)) teamName queueName dermId = ?impl_getNext_for_empty_queue

  requirement_getNext_from_empty_queue_is_always_Nothing = Refl
