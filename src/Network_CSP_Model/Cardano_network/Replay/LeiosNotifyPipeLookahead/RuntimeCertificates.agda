{-# OPTIONS --safe #-}

-- Assembly lemmas for supplied finite runtime schedules, not exhaustive search.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.RuntimeCertificates
  (Notification : Set) where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans)
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverModel Notification as Node
import Cardano_network.LeiosNotifyPipeLookahead.NodeModel Notification 1000 as Server
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as Core
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as Driver

-- Independently checked chunks concatenate without weakening their action lists.
append : ∀ {s t u actions more} → Node.Run s actions t → Node.Run t more u →
  Node.Run s (actions ++ more) u
append Node.stop tail = tail
append (Node.internal step run) tail = Node.internal step (append run tail)
append (Node.visible step run) tail = Node.visible step (append run tail)

-- Explicit indices avoid reconstructing large concrete states during certificate assembly.
join : (s t u : Node.State) (actions more : List Node.Action) →
  Node.Run s actions t → Node.Run t more u → Node.Run s (actions ++ more) u
join _ _ _ _ _ first second = append first second

-- Wire erasure distributes over sequential chunks without normalizing a whole log.
wire-append : (actions more : List Node.Action) →
  Node.wireRows (actions ++ more) ≡ Node.wireRows actions ++ Node.wireRows more
wire-append [] more = refl
wire-append (Node.wire row ∷ actions) more = cong (row ∷_) (wire-append actions more)
wire-append (Node.setForecast _ ∷ actions) more = wire-append actions more
wire-append (Node.setTerminate _ ∷ actions) more = wire-append actions more
wire-append (Node.eligible _ ∷ actions) more = wire-append actions more
wire-append (Node.handledNormal _ ∷ actions) more = wire-append actions more
wire-append (Node.rejectedCancel ∷ actions) more = wire-append actions more

-- Each chunk exports its checked run and equality with independently supplied raw rows.
record Certificate (s : Node.State) (actions : List Node.Action)
  (rows : List Driver.Event) (t : Node.State) : Set where
  constructor certificate
  field
    execution : Node.Run s actions t
    matching : Node.wireRows actions ≡ rows

-- Indexed assembly preserves exact global record order through proved concatenation.
combine : (s t u : Node.State) (actions more : List Node.Action)
  (rows following : List Driver.Event) → Certificate s actions rows t → Certificate t more following u →
  Certificate s (actions ++ more) (rows ++ following) u
combine _ _ _ actions more _ _ first second = certificate
  (append (Certificate.execution first) (Certificate.execution second))
  (trans (wire-append actions more)
    (cong₂ _++_ (Certificate.matching first) (Certificate.matching second)))

-- Server-only adversarial captures retain their own policy run instead of a fake client.
append-server : ∀ {s t u actions more} → Server.Run s actions t → Server.Run t more u →
  Server.Run s (actions ++ more) u
append-server Server.stop tail = tail
append-server (Server.internal step run) tail = Server.internal step (append-server run tail)
append-server (Server.visible step run) tail = Server.visible step (append-server run tail)

-- Local application eligibility inputs contribute no driver wire record.
server-records : List Server.Action → List Core.Action
server-records [] = []
server-records (Server.wire action ∷ actions) = action ∷ server-records actions
server-records (Server.offer _ ∷ actions) = server-records actions

-- Forget accounting only after constructing its actual node-policy certificate.
server-source : ∀ {s actions t} → Server.Run s actions t →
  Σ[ core ∈ List Core.Action ]
    (Core.Run Core.nodeNext (Server.peer s) core (Server.peer t) ×
     Core.wireActions core ≡ server-records actions)
server-source Server.stop = [] , Core.stop , refl
server-source (Server.internal (Server.schedule step _) run) with server-source run
... | core , source , matches = core , Core.internal step source , matches
server-source (Server.internal (Server.admitAccepted _) run) with server-source run
... | core , source , matches = core , Core.internal Core.admitted source , matches
server-source (Server.internal (Server.admitExcessive _) run) with server-source run
... | core , source , matches = core , Core.internal Core.excessive source , matches
server-source (Server.internal (Server.nextQueued {m = msg} _ step) run) with server-source run
... | core , source , matches = Core.nextReply (Core.normal msg) ∷ core , Core.visible step source , matches
server-source (Server.visible (Server.applicationOffer _ _) run) = server-source run
server-source (Server.visible (Server.peerRecord Server.request step) run) with server-source run
... | core , source , matches = Core.recvRequest ∷ core , Core.visible step source , cong (Core.recvRequest ∷_) matches
server-source (Server.visible (Server.peerRecord Server.quit step) run) with server-source run
... | core , source , matches = Core.recvQuit ∷ core , Core.visible step source , cong (Core.recvQuit ∷_) matches
server-source (Server.visible (Server.peerRecord (Server.reply {m = msg}) step) run) with server-source run
... | core , source , matches = Core.sendReply msg ∷ core , Core.visible step source , cong (Core.sendReply msg ∷_) matches
server-source (Server.visible (Server.peerRecord Server.done step) run) with server-source run
... | core , source , matches = Core.sendDone ∷ core , Core.visible step source , cong (Core.sendDone ∷_) matches
