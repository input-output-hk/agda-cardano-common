{-# OPTIONS --guardedness #-}

-- Inhabited exact-summary compositions and negative controls at the same boundary.
module Cardano_network.Replay.LeiosNotifyPairedBridgeTests where

open import Data.Nat using (ℕ)
open import Data.Fin using (zero)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Cardano_network.Base using (lo; hi; FromInitiator)
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
open import Cardano_network.Data exactParams
open import Cardano_network.LeiosNotifyP exactParams using (LNPEv; sendLNP; receiveLNP; apiLPev)
open import Cardano_network.Net exactParams using (lnpSendRequestNext)
open import Process_Trees using (ExtI)
import Cardano_network.Replay.LeiosNotifySession as Log
open Log using (E; Send; Recv; client; server; RequestNext; BlockAnnouncement; BlockOffer; BlockTxsOffer; Votes; Done)
import Cardano_network.Replay.LeiosNotifyPipeline as N
import Cardano_network.Replay.LeiosNotifyPairedSession as R
import Cardano_network.Replay.LeiosNotifyPairedBridge as B
import Cardano_network.Replay.LeiosNotifyExactCanonical as Canon
import Cardano_network.Replay.LeiosNotifyExactObservation as O
import Cardano_network.Replay.LeiosNotifyPairedModel exactParams as M
import Cardano_network.Replay.LeiosNotifyPairedTests as Existing
import Semantics.LTS {E = LNPEv} {I = ExtI LNPEv} as Local
import Semantics.LTS {E = M.PairEv} {I = M.PairI} as Pair
open import Semantics.Deadlock {E = M.PairEv} {I = M.PairI}
  using (_⟹∖√⟨_⟩_; ∖√-refl; ∖√-ev)

-- Four notifications exercise all native families with nontrivial retained values.
notifications : List Log.Msg
notifications = BlockAnnouncement (just (10 , 11 , 200)) ∷ BlockOffer 12 13 300 ∷
  BlockTxsOffer 14 15 ∷ Votes ((9 , 3) ∷ (7 , 1) ∷ (9 , 3) ∷ []) ∷ []

-- Both endpoint inputs preserve the chosen notifications and close after draining.
clientRows serverRows : List E
clientRows = (Send , RequestNext) ∷ (Send , RequestNext) ∷
  (Send , RequestNext) ∷ (Send , RequestNext) ∷
  (Recv , BlockAnnouncement (just (10 , 11 , 200))) ∷ (Recv , BlockOffer 12 13 300) ∷
  (Recv , BlockTxsOffer 14 15) ∷ (Recv , Votes ((9 , 3) ∷ (7 , 1) ∷ (9 , 3) ∷ [])) ∷
  (Send , Done) ∷ []
serverRows = (Recv , RequestNext) ∷ (Recv , RequestNext) ∷
  (Recv , RequestNext) ∷ (Recv , RequestNext) ∷
  (Send , BlockAnnouncement (just (10 , 11 , 200))) ∷ (Send , BlockOffer 12 13 300) ∷
  (Send , BlockTxsOffer 14 15) ∷ (Send , Votes ((9 , 3) ∷ (7 , 1) ∷ (9 , 3) ∷ [])) ∷
  (Recv , Done) ∷ []

-- The executable checker certifies a genuinely depth-four paired history.
accepted : R.Compatible 4 (R.initial 4) clientRows serverRows
accepted = toWitness {a? = R.compatible? 4 (R.initial 4) clientRows serverRows} tt

-- Completeness constructs one run of the native peer pair through full-payload FIFOs.
all-fields-system : B.Inputs 4 zero zero lo hi clientRows serverRows
all-fields-system = B.inputs-complete 4 zero zero lo hi accepted

-- Soundness recovers acceptance from exactly that composed execution and observation.
roundtrip : R.Compatible 4 (R.initial 4) clientRows serverRows
roundtrip = B.inputs-sound 4 zero zero lo hi all-fields-system

-- Each parsed message, including optional metadata and arbitrary lists, is representable.
all-messages : ∀ m → O.canonical (Canon.message m) ≡ m
all-messages = Canon.observe-message

-- Optional announcement metadata may genuinely be absent, rather than fabricated.
absent-system : B.Inputs 1 zero zero hi lo
  ((Send , RequestNext) ∷ (Recv , BlockAnnouncement nothing) ∷ [])
  ((Recv , RequestNext) ∷ (Send , BlockAnnouncement nothing) ∷ [])
absent-system = B.inputs-complete 1 zero zero hi lo
  (toWitness {a? = R.compatible? 1 (R.initial 1)
    ((Send , RequestNext) ∷ (Recv , BlockAnnouncement nothing) ∷ [])
    ((Recv , RequestNext) ∷ (Send , BlockAnnouncement nothing) ∷ [])} tt)

-- Prefix acceptance includes two actual queued sends without any remote receipt.
inflight-system : B.Inputs 2 zero zero lo hi
  ((Send , RequestNext) ∷ (Send , RequestNext) ∷ []) []
inflight-system = B.inputs-complete 2 zero zero lo hi
  (toWitness {a? = R.compatible? 2 (R.initial 2)
    ((Send , RequestNext) ∷ (Send , RequestNext) ∷ []) []} tt)

-- A depth-zero pair still has a real wire-Done execution at empty credit.
zero-system : B.Inputs 0 zero zero lo hi ((Send , Done) ∷ []) ((Recv , Done) ∷ [])
zero-system = B.inputs-complete 0 zero zero lo hi
  (toWitness {a? = R.compatible? 0 (R.initial 0) ((Send , Done) ∷ []) ((Recv , Done) ∷ [])} tt)

-- The existing locally legal size mismatch has no exact-field composed witness.
size-mismatch-impossible : ¬ B.Inputs 1 zero zero lo hi Existing.cs Existing.mismatched
size-mismatch-impossible input = Existing.rejected
  (R.toWitness 1 (B.inputs-sound 1 zero zero lo hi input))

-- The native product can take an API handoff and queue its actual request packet.
direct-events : List Pair.Event
direct-events = Pair.evLabel _ (M.atClient (apiLPev zero lo lnpSendRequestNext)) tt ∷
  Pair.evLabel _ (M.atClient (sendLNP zero lo)) (tt , FromInitiator , tt , leiosNotifyP MsgLNPRequestNext) ∷ []

-- This independent LTS witness does not assume a replay-to-PTree existence result.
direct-run : ∃[ T ] B.system 2 zero zero lo hi ⟹∖√⟨ direct-events ⟩ T
direct-run = _ , ∖√-ev (Pair.sVis refl refl) (∖√-ev (Pair.sVis refl refl) ∖√-refl)

-- Exact observation sees only the request send while retaining its endpoint.
direct-observation : B.Obs direct-events ((client , Send , RequestNext) ∷ [])
direct-observation = refl

-- The independent concrete run transfers back into paired replay.
direct-sound : R.HasTrace 2 (R.initial 2) ((client , Send , RequestNext) ∷ [])
direct-sound with direct-run
... | T , run = B.sound 2 zero zero lo hi run direct-observation

-- A negative merge certificate excludes a concrete composed witness by soundness.
exclude : ∀ {cs ss} → ¬ R.Compatible 1 (R.initial 1) cs ss →
  ¬ B.Inputs 1 zero zero lo hi cs ss
exclude bad input = bad (B.inputs-sound 1 zero zero lo hi input)

-- One-response input templates isolate payload equality from local wire control.
clientWith serverWith : Log.Msg → List E
clientWith m = (Send , RequestNext) ∷ (Recv , m) ∷ []
serverWith m = (Recv , RequestNext) ∷ (Send , m) ∷ []

-- Offer hash equality is observed.
offer-hash-impossible : ¬ B.Inputs 1 zero zero lo hi
  (clientWith (BlockOffer 1 2 3)) (serverWith (BlockOffer 4 2 3))
offer-hash-impossible = exclude (toWitnessFalse {a? = R.compatible? 1 (R.initial 1)
  (clientWith (BlockOffer 1 2 3)) (serverWith (BlockOffer 4 2 3))} tt)

-- Offer slot equality is observed.
offer-slot-impossible : ¬ B.Inputs 1 zero zero lo hi
  (clientWith (BlockOffer 1 2 3)) (serverWith (BlockOffer 1 4 3))
offer-slot-impossible = exclude (toWitnessFalse {a? = R.compatible? 1 (R.initial 1)
  (clientWith (BlockOffer 1 2 3)) (serverWith (BlockOffer 1 4 3))} tt)

-- Offer byte size equality is observed.
offer-size-impossible : ¬ B.Inputs 1 zero zero lo hi
  (clientWith (BlockOffer 1 2 3)) (serverWith (BlockOffer 1 2 4))
offer-size-impossible = exclude (toWitnessFalse {a? = R.compatible? 1 (R.initial 1)
  (clientWith (BlockOffer 1 2 3)) (serverWith (BlockOffer 1 2 4))} tt)

-- Announcement hash equality is observed.
announcement-hash-impossible : ¬ B.Inputs 1 zero zero lo hi
  (clientWith (BlockAnnouncement (just (1 , 2 , 3)))) (serverWith (BlockAnnouncement (just (4 , 2 , 3))))
announcement-hash-impossible = exclude (toWitnessFalse {a? = R.compatible? 1 (R.initial 1)
  (clientWith (BlockAnnouncement (just (1 , 2 , 3)))) (serverWith (BlockAnnouncement (just (4 , 2 , 3))))} tt)

-- Announcement slot equality is observed.
announcement-slot-impossible : ¬ B.Inputs 1 zero zero lo hi
  (clientWith (BlockAnnouncement (just (1 , 2 , 3)))) (serverWith (BlockAnnouncement (just (1 , 4 , 3))))
announcement-slot-impossible = exclude (toWitnessFalse {a? = R.compatible? 1 (R.initial 1)
  (clientWith (BlockAnnouncement (just (1 , 2 , 3)))) (serverWith (BlockAnnouncement (just (1 , 4 , 3))))} tt)

-- Announcement body size equality is observed.
announcement-size-impossible : ¬ B.Inputs 1 zero zero lo hi
  (clientWith (BlockAnnouncement (just (1 , 2 , 3)))) (serverWith (BlockAnnouncement (just (1 , 2 , 4))))
announcement-size-impossible = exclude (toWitnessFalse {a? = R.compatible? 1 (R.initial 1)
  (clientWith (BlockAnnouncement (just (1 , 2 , 3)))) (serverWith (BlockAnnouncement (just (1 , 2 , 4))))} tt)

-- Absent announcement metadata is distinct from a present summary.
announcement-presence-impossible : ¬ B.Inputs 1 zero zero lo hi
  (clientWith (BlockAnnouncement nothing)) (serverWith (BlockAnnouncement (just (1 , 2 , 3))))
announcement-presence-impossible = exclude (toWitnessFalse {a? = R.compatible? 1 (R.initial 1)
  (clientWith (BlockAnnouncement nothing)) (serverWith (BlockAnnouncement (just (1 , 2 , 3))))} tt)

-- Transaction-offer hash equality is observed.
txs-offer-hash-impossible : ¬ B.Inputs 1 zero zero lo hi
  (clientWith (BlockTxsOffer 1 2)) (serverWith (BlockTxsOffer 3 2))
txs-offer-hash-impossible = exclude (toWitnessFalse {a? = R.compatible? 1 (R.initial 1)
  (clientWith (BlockTxsOffer 1 2)) (serverWith (BlockTxsOffer 3 2))} tt)

-- Transaction-offer slot equality is observed.
txs-offer-slot-impossible : ¬ B.Inputs 1 zero zero lo hi
  (clientWith (BlockTxsOffer 1 2)) (serverWith (BlockTxsOffer 1 3))
txs-offer-slot-impossible = exclude (toWitnessFalse {a? = R.compatible? 1 (R.initial 1)
  (clientWith (BlockTxsOffer 1 2)) (serverWith (BlockTxsOffer 1 3))} tt)

-- Each retained ranking-block hash is observed.
vote-hash-impossible : ¬ B.Inputs 1 zero zero lo hi
  (clientWith (Votes ((1 , 2) ∷ []))) (serverWith (Votes ((3 , 2) ∷ [])))
vote-hash-impossible = exclude (toWitnessFalse {a? = R.compatible? 1 (R.initial 1)
  (clientWith (Votes ((1 , 2) ∷ []))) (serverWith (Votes ((3 , 2) ∷ [])))} tt)

-- Each retained voter identifier is observed.
vote-voter-impossible : ¬ B.Inputs 1 zero zero lo hi
  (clientWith (Votes ((1 , 2) ∷ []))) (serverWith (Votes ((1 , 3) ∷ [])))
vote-voter-impossible = exclude (toWitnessFalse {a? = R.compatible? 1 (R.initial 1)
  (clientWith (Votes ((1 , 2) ∷ []))) (serverWith (Votes ((1 , 3) ∷ [])))} tt)

-- Vote lists retain order rather than being compared as sets.
vote-order-impossible : ¬ B.Inputs 1 zero zero lo hi
  (clientWith (Votes ((1 , 2) ∷ (3 , 4) ∷ []))) (serverWith (Votes ((3 , 4) ∷ (1 , 2) ∷ [])))
vote-order-impossible = exclude (toWitnessFalse {a? = R.compatible? 1 (R.initial 1)
  (clientWith (Votes ((1 , 2) ∷ (3 , 4) ∷ []))) (serverWith (Votes ((3 , 4) ∷ (1 , 2) ∷ [])))} tt)

-- Repeated vote summaries cannot silently be dropped.
vote-duplicates-impossible : ¬ B.Inputs 1 zero zero lo hi
  (clientWith (Votes ((1 , 2) ∷ (1 , 2) ∷ []))) (serverWith (Votes ((1 , 2) ∷ [])))
vote-duplicates-impossible = exclude (toWitnessFalse {a? = R.compatible? 1 (R.initial 1)
  (clientWith (Votes ((1 , 2) ∷ (1 , 2) ∷ []))) (serverWith (Votes ((1 , 2) ∷ [])))} tt)

-- The four-credit capture is impossible under a three-credit model as well.
insufficient-depth : ¬ B.Inputs 3 zero zero lo hi clientRows serverRows
insufficient-depth input = toWitnessFalse
  {a? = R.compatible? 3 (R.initial 3) clientRows serverRows} tt
  (B.inputs-sound 3 zero zero lo hi input)

-- The theorem's target is definitionally the existing native peer/FIFO constructor.
native-target : B.system 2 zero zero lo hi ≡ M.pipelined-system 2 zero zero lo hi
native-target = refl
