{-# OPTIONS --safe #-}

-- Positive witnesses and negative controls for independent session replay.
module Cardano_network.Replay.InterleavedTests where

open import Data.Unit using (tt)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (True; False; toWitness; toWitnessFalse)
open import Cardano_network.Replay.LeiosFetchSession
open import Cardano_network.Replay.Parse using (client; server)
open import Cardano_network.Replay.LeiosFetchInterleaved
open import Cardano_network.Replay.InterleavedReport using (report)
open import Semantics.Replay using (module Traces)

-- Two clients may each have one request outstanding at global depth two.
clients : List (Events 2)
clients = inj₁ (Send , MsgLeiosBlockRequest 5 0)
        ∷ inj₂ (inj₁ (Send , MsgLeiosBlockRequest 6 0))
        ∷ inj₂ (inj₁ (Recv , MsgLeiosBlock 6 10))
        ∷ inj₁ (Recv , MsgLeiosBlock 5 10) ∷ []

-- Computation checks the per-session bound rather than a global bound.
clients-ok : True (check 1 (client ∷ client ∷ []) clients)
clients-ok = tt

-- The decision's positive witness is a trace of the single product model.
clients-run : Traces.HasTrace (model 1 2) (initial (client ∷ client ∷ [])) clients
clients-run = toWitness {a? = check 1 (client ∷ client ∷ []) clients} clients-ok

-- Replies cannot consume another session's request, even with the same hash.
isolated : List (Events 2)
isolated = inj₁ (Send , MsgLeiosBlockRequest 5 0)
         ∷ inj₂ (inj₁ (Recv , MsgLeiosBlock 5 10)) ∷ []

-- A reply in an idle session is rejected.
isolated-bad : False (check 1 (client ∷ client ∷ []) isolated)
isolated-bad = tt

-- The negative result refutes all product runs for that interleaving.
isolated-refuted : ¬ (Traces.HasTrace (model 1 2) (initial (client ∷ client ∷ [])) isolated)
isolated-refuted = toWitnessFalse {a? = check 1 (client ∷ client ∷ []) isolated} isolated-bad

-- Independent servers can both become busy before either silent serve step.
servers : List (Events 2)
servers = inj₁ (Recv , MsgLeiosBlockRequest 5 0)
        ∷ inj₂ (inj₁ (Recv , MsgLeiosBlockRequest 6 0))
        ∷ inj₂ (inj₁ (Send , MsgLeiosBlock 6 10))
        ∷ inj₁ (Send , MsgLeiosBlock 5 10) ∷ []

-- The product witness includes both servers' silent transitions.
servers-ok : True (check 1 (server ∷ server ∷ []) servers)
servers-ok = tt

-- A mixed-role interleaving parses and accepts as one trace.
mixed-ok : report 1 "sessions client server\n0 Send BlockRequest 5 0\n1 Recv BlockRequest 6 0\n0 Recv Block 5 10\n1 Send Block 6 10\n" ≡ "accepted (4 events, 2 sessions)"
mixed-ok = refl

-- A wrong-hash reply is rejected at its GLOBAL index with the correct tag.
wrong-hash : report 1 "sessions client client\n0 Send BlockRequest 5 0\n1 Send Done\n0 Recv Block 6 10\n" ≡
             "rejected at index 3 (session 0): Recv Block 0000000000000000000000000000000000000000000000000000000000000006 10\nmodel session state after 2 events: client open, outstanding oldest first [BlockRequest 0000000000000000000000000000000000000000000000000000000000000005 0] (accepts: a response to the FIRST of these, or a new request if fewer than k are outstanding)"
wrong-hash = refl

-- Reusing a closed generation is rejected rather than silently resetting it.
closed : False (check 1 (client ∷ []) (inj₁ (Send , MsgLeiosDone) ∷ inj₁ (Send , MsgLeiosDone) ∷ []))
closed = tt

-- A new generation gets its own initial state after an earlier Done.
new-generation : report 1 "sessions client client\n0 Send Done\n1 Send BlockRequest 5 0\n" ≡ "accepted (2 events, 2 sessions)"
new-generation = refl

-- Outstanding requests at EOF are valid prefixes.
prefix : report 1 "sessions server\n0 Recv BlockRequest 5 0\n" ≡ "accepted (1 events, 1 sessions)"
prefix = refl

-- Session ids must be declared by the manifest.
unknown-session : report 1 "sessions client\n1 Send Done\n" ≡ "parse error at line 2: 1 Send Done"
unknown-session = refl

-- Invalid role declarations cannot be interpreted as empty manifests.
bad-role : report 1 "sessions peer\n" ≡ "parse error at line 1: sessions peer"
bad-role = refl

-- Empty logs have a well-defined identity product.
empty-ok : report 1 "sessions\n" ≡ "accepted (0 events, 0 sessions)"
empty-ok = refl

-- An event cannot target the empty product.
empty-bad : report 1 "sessions\n0 Send Done\n" ≡ "parse error at line 2: 0 Send Done"
empty-bad = refl

-- Interleaving another session does not increase a client's own bound.
overflow : False (check 1 (client ∷ client ∷ [])
           (inj₁ (Send , MsgLeiosBlockRequest 5 0)
          ∷ inj₂ (inj₁ (Send , MsgLeiosBlockRequest 6 0))
          ∷ inj₁ (Send , MsgLeiosBlockRequest 7 0) ∷ []))
overflow = tt

-- FIFO ordering within a session still applies at depth two.
fifo : False (check 2 (client ∷ client ∷ [])
       (inj₁ (Send , MsgLeiosBlockRequest 5 0)
      ∷ inj₂ (inj₁ (Send , MsgLeiosDone))
      ∷ inj₁ (Send , MsgLeiosBlockRequest 6 0)
      ∷ inj₁ (Recv , MsgLeiosBlock 6 10) ∷ []))
fifo = tt
