module BackboneQueue

data DermId = MkDID String

lemma_DermId_inj : (MkDID did1) = (MkDID did2) -> did1 = did2
lemma_DermId_inj Refl = Refl

DecEq DermId where
  decEq (MkDID d1) (MkDID d2) =
    case decEq d1 d2 of
      (Yes Refl) => Yes Refl
      (No contra) => No (\x => contra (lemma_DermId_inj x))

ImageId : Type
ImageId = String

KeyValuePair : Type
KeyValuePair = (String, String)

record ImageWithProps where
  constructor MkImageWithProps
  imageId    : ImageId
  properties : List KeyValuePair

record QueueItem where
  constructor MkQueueItem
  dermId : DermId
  images : List ImageWithProps

data BBQ : Nat -> Type where
  EmptyBBQ : BBQ 0
  ConsBBQ  : QueueItem -> BBQ n -> BBQ (S n)

data HasDermItem : DermId -> BBQ n -> Type where
  HasDermItemHere : HasDermItem dermId (ConsBBQ (MkQueueItem dermId images) tail)
  HasDermItemThere : HasDermItem dermId queue -> HasDermItem dermId (ConsBBQ queueItem queue)

hasDermItem : (dermId : DermId) -> (queue : BBQ n) -> Maybe (HasDermItem dermId queue)
hasDermItem dermId EmptyBBQ = Nothing
hasDermItem dermId (ConsBBQ (MkQueueItem queueItemDermId images) tail) with (decEq dermId queueItemDermId)
  hasDermItem queueItemDermId (ConsBBQ (MkQueueItem queueItemDermId images) tail) | (Yes Refl) =
    Just HasDermItemHere
  hasDermItem dermId (ConsBBQ (MkQueueItem queueItemDermId images) tail) | (No contra) =
    map HasDermItemThere (hasDermItem dermId tail)


record EnqueueRequest where
  constructor MkEnqueueRequest
  dermId : DermId
  images : List ImageWithProps

enqueue : EnqueueRequest -> BBQ n -> BBQ (S n)
enqueue (MkEnqueueRequest dermId images) queue = ConsBBQ (MkQueueItem dermId images) queue

dequeue : DermId -> BBQ (S n) -> Maybe (QueueItem, BBQ n)
dequeue dermId (ConsBBQ (MkQueueItem queueItemDermId images) tail) with (decEq dermId queueItemDermId)
  dequeue queueItemDermId (ConsBBQ (MkQueueItem queueItemDermId images) tail) | (Yes Refl) = Just (MkQueueItem queueItemDermId images, tail)
  dequeue dermId (ConsBBQ (MkQueueItem queueItemDermId images) tail) | (No contra) =
    case tail of
      EmptyBBQ => Nothing
      (ConsBBQ _ _) =>
        case dequeue dermId tail of
          Nothing => Nothing
          (Just (item, tail')) => Just (item, ConsBBQ (MkQueueItem queueItemDermId images) tail')

them_dequeue_from_singleton_queue : {dermId : DermId}
                                 -> {images : List ImageWithProps}
                                 -> {n : Nat}
                                 -> {queue : BBQ n}
                                 -> dequeue dermId (enqueue (MkEnqueueRequest dermId images) queue) = Just (MkQueueItem dermId images, queue)
them_dequeue_from_singleton_queue {dermId} {queue} with (decEq dermId dermId)
  them_dequeue_from_singleton_queue {dermId = dermId} {queue} | (Yes Refl) = Refl
  them_dequeue_from_singleton_queue {dermId = dermId} {queue = EmptyBBQ} | (No contra) = absurd (contra Refl)
  them_dequeue_from_singleton_queue {dermId = dermId} {queue = (ConsBBQ x y)} | (No contra) = absurd (contra Refl)

thm_enqueue_dequeue_for_derm_in_any_queue : {dermId : DermId}
                                         -> {queue : BBQ (S n)}
                                         -> {prf : HasDermItem dermId queue}
                                         -> dequeue dermId queue = Just (MkQueueItem dermId images, tail)
thm_enqueue_dequeue_for_derm_in_any_queue {dermId = dermId} {queue = (ConsBBQ (MkQueueItem dermId images) tail)} {prf = HasDermItemHere} with (decEq dermId dermId)
  thm_enqueue_dequeue_for_derm_in_any_queue {dermId = dermId} {queue = (ConsBBQ (MkQueueItem dermId images) tail)} {prf = HasDermItemHere} | (Yes Refl) = ?wat_4
  thm_enqueue_dequeue_for_derm_in_any_queue {dermId = dermId} {queue = (ConsBBQ (MkQueueItem dermId images) tail)} {prf = HasDermItemHere} | (No contra) = ?wat_3
thm_enqueue_dequeue_for_derm_in_any_queue {dermId = dermId} {queue = (ConsBBQ queueItem x)} {prf = (HasDermItemThere y)} = ?wat_2
