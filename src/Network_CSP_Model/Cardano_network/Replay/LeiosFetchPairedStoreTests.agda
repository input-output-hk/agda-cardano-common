{-# OPTIONS --guardedness #-}

-- Inhabited capture prefixes for the renamed client and store-backed producer.
module Cardano_network.Replay.LeiosFetchPairedStoreTests where
open import Data.Fin using (zero)
open import Data.List using (List; []; _∷_)
open import Data.Product using (∃-syntax; _,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl)
open import Cardano_network.Base using (hi; FromInitiator; N2N_LeiosFetch)
open import Cardano_network.Replay.ReplayParams using (replayParams)
open import Cardano_network.Data replayParams using (Payload; leiosFetchP; MsgLFPBlockRequest)
open import Cardano_network.Net replayParams using (apiLP; input; output; lfpSendBlockRequest)
import Cardano_network.Replay.LeiosFetchPairedStoreModel as M
import Cardano_network.Replay.LeiosFetchPairedStoreTrace as T
import Semantics.LTS {E = M.PairEv} {I = M.PairI} as Pair
open import Semantics.Deadlock {E = M.PairEv} {I = M.PairI}
  using (_⟹∖√⟨_⟩_; ∖√-refl; ∖√-ev)

-- The request names a body held by the initial server store.
request : Payload
request = tt , FromInitiator , tt , leiosFetchP (MsgLFPBlockRequest (1 , 3))

-- Client API/send and server wire receive retain distinct endpoint tags.
request-events : List Pair.Event
request-events = Pair.evLabel _ (M.atClient (apiLP zero hi lfpSendBlockRequest)) (1 , 3) ∷
  Pair.evLabel _ (M.atClient (input zero hi N2N_LeiosFetch)) request ∷
  Pair.evLabel _ (M.atServer (output zero hi N2N_LeiosFetch)) request ∷ []

-- Actual server/thread/store composition can consume the queued request.
request-run : ∃[ end ] M.system 2 zero hi (1 ∷ []) ⟹∖√⟨ request-events ⟩ end
request-run = _ , ∖√-ev (Pair.sVis refl refl)
  (∖√-ev (Pair.sVis refl refl) (∖√-ev (Pair.sVis refl refl) ∖√-refl))

import Cardano_network.Replay.LeiosFetchSession as F
import Cardano_network.Replay.LeiosFetchPairedModelTests as Bare
open import Cardano_network.Replay.LeiosFetchObs using (ObsS)
open import Cardano_network.Replay.LeiosFetchServerModel using (Bodies)
open import Data.Empty using (⊥)
open import Semantics.Replay using (module Traces)
module Spec = Traces (F.Spec.leiosFetch 2)

-- The inherited server soundness theorem has an inhabited composed antecedent.
request-server-legal : Spec.HasTrace F.server₀ ((F.Recv , F.MsgLeiosBlockRequest 1 3) ∷ [])
request-server-legal with request-run
... | end , run = T.server-legal 2 zero hi (1 ∷ []) run refl

-- Store-backed service excludes the wrong-hash behavior admitted by the bare peer.
wrong-server-impossible : ∀ (bs : Bodies) {events end} →
  M.system 2 zero hi bs ⟹∖√⟨ events ⟩ end →
  ObsS (T.projectServer events)
    ((F.Recv , F.MsgLeiosBlockRequest 1 3) ∷ (F.Send , F.MsgLeiosBlock 2 0) ∷ []) → ⊥
wrong-server-impossible bs run obs = Bare.wrong-server-rejected (T.server-legal 2 zero hi bs run obs)
