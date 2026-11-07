{-# OPTIONS --guardedness #-}

-- Concrete witnesses for the bounded-pipeline / lookahead wire-language relation.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.BoundedRelationTests where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; replicate)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_; proj₁)
open import Relation.Nullary.Decidable using (isYes; toWitness)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
import Cardano_network.Replay.LeiosNotifySession as Log
open Log using (Send; Recv; server; client)
import Cardano_network.Replay.LeiosNotifyPipeline as Pipeline
import Cardano_network.LeiosNotifyPipe exactParams as Payloads
import Cardano_network.LeiosNotifyPipeLookahead.Model Payloads.Notification as S
open S using (genericNext; nodeNext; normal; canceled)
import Cardano_network.LeiosNotifyPipeLookahead.Wire.Server Payloads.Notification as SW
import Cardano_network.LeiosNotifyPipeLookahead.Wire.Client Payloads.Notification as CW
open import Cardano_network.Replay.LeiosNotifyPipeLookahead.BoundedRelation

-- `a` is exactly what the existing server/client decoders produce for `BlockAnnouncement h`.
server-a : serverWires ((Send , Log.BlockAnnouncement h) ∷ []) ≡ just (SW.reply (normal a) ∷ [])
server-a = refl

-- The client decoder yields the same notification with receive agency.
client-a : clientWires ((Recv , Log.BlockAnnouncement h) ∷ []) ≡ just (CW.reply (normal a) ∷ [])
client-a = refl

-- Wrong agency is a failed translation, not a dropped row.
server-wrong-agency : serverWires ((Recv , Log.Canceled) ∷ []) ≡ nothing
server-wrong-agency = refl

-- The counterexample rows translate to the stated lookahead rows.
canceled-open-wires : serverWires canceledOpenRows ≡ just (SW.request ∷ SW.reply canceled ∷ [])
canceled-open-wires = refl

-- A pipelined server session: two requests, one answer, Quit, a cancel and Done.
serverRows : List Log.E
serverRows = (Recv , Log.RequestNext) ∷ (Recv , Log.RequestNext) ∷ (Send , Log.BlockAnnouncement h) ∷
  (Recv , Log.Quit) ∷ (Send , Log.Canceled) ∷ (Send , Log.Done) ∷ []

-- Its exact lookahead translation.
serverWs : List SW.Wire
serverWs = SW.request ∷ SW.request ∷ SW.reply (normal a) ∷ SW.quit ∷ SW.reply canceled ∷ SW.done ∷ []

-- The bounded server accepts it at depth 2 and 1000, but not at depth 1.
server-bounded-2 : isYes (Pipeline.Spec.check 2 server serverRows) ≡ true
server-bounded-2 = refl
server-bounded-1000 : isYes (Pipeline.Spec.check 1000 server serverRows) ≡ true
server-bounded-1000 = refl
server-bounded-1 : isYes (Pipeline.Spec.check 1 server serverRows) ≡ false
server-bounded-1 = refl

-- The inclusion computes the exact translated rows from the bounded witness.
server-included-2 : proj₁ (server-included-generic 2 serverRows (toWitness {a? = Pipeline.Spec.check 2 server serverRows} _)) ≡ serverWs
server-included-2 = refl
server-included-1000 : proj₁ (server-included-generic 1000 serverRows (toWitness {a? = Pipeline.Spec.check 1000 server serverRows} _)) ≡ serverWs
server-included-1000 = refl

-- The lookahead server independently accepts those rows under genericNext.
server-lookahead-generic : isYes (SW.decide genericNext SW.initial serverWs) ≡ true
server-lookahead-generic = refl

-- A pipelined client session: two requests, one reply, Quit, a drained cancel and Done.
clientRows : List Log.E
clientRows = (Send , Log.RequestNext) ∷ (Send , Log.RequestNext) ∷ (Recv , Log.BlockAnnouncement h) ∷
  (Send , Log.Quit) ∷ (Recv , Log.Canceled) ∷ (Recv , Log.Done) ∷ []

-- Its exact lookahead client translation.
clientWs : List CW.Wire
clientWs = CW.request ∷ CW.request ∷ CW.reply (normal a) ∷ CW.quit ∷ CW.reply canceled ∷ CW.done ∷ []

-- Bounded acceptance at depths 2 and 1000; depth 1 forbids the second request.
client-bounded-2 : isYes (Pipeline.Spec.check 2 client clientRows) ≡ true
client-bounded-2 = refl
client-bounded-1000 : isYes (Pipeline.Spec.check 1000 client clientRows) ≡ true
client-bounded-1000 = refl
client-bounded-1 : isYes (Pipeline.Spec.check 1 client clientRows) ≡ false
client-bounded-1 = refl

-- The client inclusion computes the exact translated rows.
client-included-2 : proj₁ (client-included 2 clientRows (toWitness {a? = Pipeline.Spec.check 2 client clientRows} _)) ≡ clientWs
client-included-2 = refl
client-included-1000 : proj₁ (client-included 1000 clientRows (toWitness {a? = Pipeline.Spec.check 1000 client clientRows} _)) ≡ clientWs
client-included-1000 = refl

-- The lookahead client independently accepts them.
client-lookahead : isYes (CW.decide CW.initial clientWs) ≡ true
client-lookahead = refl

-- nodeNext counterexample at depths 1 and 1000 (bounds 2 and 1001), plus concrete decisions.
canceled-open-1 : _
canceled-open-1 = node-canceled-open 1
canceled-open-1000 : _
canceled-open-1000 = node-canceled-open 1000
canceled-open-bounded : isYes (Pipeline.Spec.check 1 server canceledOpenRows) ≡ true
canceled-open-bounded = refl
canceled-open-node : isYes (SW.decide nodeNext SW.initial (SW.request ∷ SW.reply canceled ∷ [])) ≡ false
canceled-open-node = refl
canceled-open-generic : isYes (SW.decide genericNext SW.initial (SW.request ∷ SW.reply canceled ∷ [])) ≡ true
canceled-open-generic = refl

-- Normal reply after Quit: lookahead accepts, bounded rejects.
normal-after-quit-1 : _
normal-after-quit-1 = normal-after-quit 1
normal-after-quit-1000 : _
normal-after-quit-1000 = normal-after-quit 1000
naq-rows : List Log.E
naq-rows = (Recv , Log.RequestNext) ∷ (Recv , Log.Quit) ∷ (Send , Log.BlockAnnouncement h) ∷ []
naq-wires : serverWires naq-rows ≡ just (SW.request ∷ SW.quit ∷ SW.reply (normal a) ∷ [])
naq-wires = refl
naq-bounded : isYes (Pipeline.Spec.check 2 server naq-rows) ≡ false
naq-bounded = refl
naq-node : isYes (SW.decide nodeNext SW.initial (SW.request ∷ SW.quit ∷ SW.reply (normal a) ∷ [])) ≡ true
naq-node = refl

-- Requests beyond the bound: bounded rejects, lookahead accepts under both contracts.
over-depth-1 : _
over-depth-1 = over-depth 1
over-depth-1000 : _
over-depth-1000 = over-depth 1000
over-lookahead-1 : _
over-lookahead-1 = over-depth-lookahead 1
over-lookahead-1000 : _
over-lookahead-1000 = over-depth-lookahead 1000
over-bounded-3 : isYes (Pipeline.Spec.check 3 server (replicate 4 (Recv , Log.RequestNext))) ≡ false
over-bounded-3 = refl
within-bounded-3 : isYes (Pipeline.Spec.check 3 server (replicate 3 (Recv , Log.RequestNext))) ≡ true
within-bounded-3 = refl
over-lookahead-node : isYes (SW.decide nodeNext SW.initial (replicate 4 SW.request)) ≡ true
over-lookahead-node = refl

-- A reply before its request (the lookahead Lead state): lookahead accepts, bounded rejects.
client-lead-1 : _
client-lead-1 = client-lead 1
client-lead-1000 : _
client-lead-1000 = client-lead 1000
lead-wires : clientWires ((Recv , Log.BlockAnnouncement h) ∷ (Send , Log.RequestNext) ∷ []) ≡
  just (CW.reply (normal a) ∷ CW.request ∷ [])
lead-wires = refl
lead-bounded : isYes (Pipeline.Spec.check 1000 client ((Recv , Log.BlockAnnouncement h) ∷ (Send , Log.RequestNext) ∷ [])) ≡ false
lead-bounded = refl
lead-lookahead : isYes (CW.decide CW.initial (CW.reply (normal a) ∷ CW.request ∷ [])) ≡ true
lead-lookahead = refl
