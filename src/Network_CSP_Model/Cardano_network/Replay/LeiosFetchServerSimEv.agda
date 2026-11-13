{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; z≤n; _+_)

-- The visible clause of server soundness (trace-replay Phase 5, Increment 1).
-- Every visible step of a related composite is matched by the spec:
--   * the producer's wire receive (Idle) and wire send (Block / BlockTxs) by
--     exactly one spec event, equal under `clsS`/`forget`;
--   * the api rendezvous (report, reply command) by no spec move;
--   * the store rendezvous of the waiting thread by `sServe` — the body handed
--     over has the requested hash (`srest-get`, `ebHash = id`), which is what
--     makes the later Block carry the requested hash;
--   * a negative read or missing replay-table offset by `sThrow`;
--   * the BlockTxs application reply retains the reported point (`b1-ev`, `b2-ev`),
--     while the wire reply carries only its positional transactions.
-- Impossible rendezvous are refuted by the component alphabets (`AE`/`SE`) and,
-- between the two threads' api commands, by `tag`.
-- Invariant 1 (B7a): checked with `agda --safe` on the command line.
module Cardano_network.Replay.LeiosFetchServerSimEv (k : ℕ) where

open import Data.List using (List; []; _∷_; length; map; _++_)
import Data.List.Properties as L
import Data.Nat.Properties as N
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Cardano_network.Replay.LeiosFetchWords using (decodable-all)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)

open import Cardano_network.Base using (FromInitiator)
open import Process_Trees using (ExtI)
open import Cardano_network.Replay.ReplayParams using (replayParams)
open import Cardano_network.Net replayParams using (Net_Api)
open import Cardano_network.Data replayParams using (Payload; DecEq-EBPoint; DecEq-TxsRequest)
open import Cardano_network.LeiosFetchP replayParams using (stIdle)
open import Cardano_network.Parametric.Leios.NoLivelock.PeerLFP replayParams
  using (SIdleV; siBlk; siTxs; siDecodeStop; siDone)
open import Cardano_network.Replay.LeiosFetchServerModel using (Proc; Bodies; lS; dS; nS; serveTxs)
open import Cardano_network.Replay.LeiosFetchServerParts
open import Cardano_network.Replay.LeiosFetchServerRel k
open import Cardano_network.Replay.LeiosFetchObs using (ObsS; clsS; forget; recv-request; recv-request-fails; request-match)
import Cardano_network.Replay.LeiosFetchWireBridge {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} as WB
open WB using (silent; logged)
open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (Event; _─[_]─►_; ev; evl)

open import Cardano_network.Replay.LeiosFetchSession
  using (St; E; Send; Recv; sReady; sIdle; blockTxsReq; MsgLeiosBlockRequest; MsgLeiosBlock; MsgLeiosBlockTxsRequest
        ; MsgLeiosBlockTxs; MsgLeiosDone; module Spec)
open Spec k
  using (leiosFetch; _-[_]→_; sRecvBlockReq; sRecvTxsReq; sRecvDone; sSendBlock; sSendTxs; sServe; sThrow)
open import Semantics.Replay using (module Traces)
open Traces leiosFetch using (_⇒⟨_⟩_; done; tau; vis)

-- no Idle receive of the producer is an api label
idle-not-api : ∀ {x t′} → SIdleV lS dS x t′ → ¬ AE (renE x)
idle-not-api (siBlk _)   ()
idle-not-api (siTxs _ _ _) ()
idle-not-api (siDecodeStop _ _ _) ()
idle-not-api siDone      ()

-- the matching spec run of one visible model step
Match : Bodies → Event → St → Proc → Set₁
Match bs e s M′ = WB.Match k clsS (Rel bs) M′ s (clsS e)

-- every visible model step is matched by the spec, observing the same
sim-ev : ∀ {bs M M′ s e} → Rel bs M s → M ─[ ev (evl e) ]─► M′ → Match bs e s M′

-- Idle: a wire receive starts a request (or closes)
sim-ev (rIdle pr ea eb ss) st with comp-ev (prest-ns pr) (alphA-rest ea) (alphB-rest eb) (srest-alph ss) st
... | eP _ _ stP with pidle-ev pr stP
...   | _ , _ , siBlk q , refl , refl = logged refl
        (λ { (Recv , MsgLeiosBlockRequest _ _) refl _ → _ , vis sRecvBlockReq done , rReqB q ea eb ss })
...   | _ , _ , siTxs q bm ok , refl , refl = logged (recv-request tt FromInitiator tt q bm ok)
        (λ { (Recv , MsgLeiosBlockTxsRequest _ _ _ b) same _ →
          case request-match {b = b} (cong proj₂ same) of λ { (refl , refl , refl , valid , offsets-eq) →
            _ , vis (sRecvTxsReq valid (sym (cong length offsets-eq))) done ,
            rReqT (q , bm) (decodable-all ok) ea eb ss } })
...   | _ , _ , siDecodeStop q bm bad , refl , refl =
        silent (recv-request-fails tt FromInitiator tt q bm bad) done (rDecode ea eb ss)
...   | _ , _ , siDone , refl , refl = logged refl
        (λ { (Recv , MsgLeiosDone) refl _ → _ , vis sRecvDone done , rDone ea eb ss })
sim-ev (rIdle pr ea eb ss) st | eAA a stP _ with pidle-ev pr stP
... | _ , _ , sv , refl , _ = ⊥-elim (idle-not-api sv a)
sim-ev (rIdle pr ea eb ss) st | eAB a stP _ with pidle-ev pr stP
... | _ , _ , sv , refl , _ = ⊥-elim (idle-not-api sv a)
sim-ev (rIdle pr ea eb ss) st | eSA s stA _ with erestA-ev ea stA
... | _ , refl , _ = ⊥-elim s
sim-ev (rIdle pr ea eb ss) st | eSB s stB _ with erestB-ev eb stB
... | _ , refl , _ = ⊥-elim s
sim-ev (rIdle pr ea eb ss) st | eBoth stA stB with erestA-ev ea stA | erestB-ev eb stB
... | _ , refl , _ | _ , eq , _ = case cong tag eq of λ ()

-- BlockRequest received: the report reaches thread A
sim-ev (rReqB q ea eb ss) st with comp-ev peer-ns (alphA-rest ea) (alphB-rest eb) (srest-alph ss) st
... | eP na _ stP with p-out-ev ⦃ DecEq-EBPoint ⦄ stP
...   | refl , _ = ⊥-elim (na _)
sim-ev (rReqB q ea eb ss) st | eAA _ stP stA with p-out-ev ⦃ DecEq-EBPoint ⦄ stP | erestA-ev ea stA
... | refl , refl | _ , refl , refl = silent refl done (rWaitB q pBack eb ss)
sim-ev (rReqB q ea eb ss) st | eAB _ stP stB with p-out-ev ⦃ DecEq-EBPoint ⦄ stP | erestB-ev eb stB
... | refl , _ | _ , eq , _ = case cong tag eq of λ ()
sim-ev (rReqB q ea eb ss) st | eSA s stA _ with erestA-ev ea stA
... | _ , refl , _ = ⊥-elim s
sim-ev (rReqB q ea eb ss) st | eSB s stB _ with erestB-ev eb stB
... | _ , refl , _ = ⊥-elim s
sim-ev (rReqB q ea eb ss) st | eBoth stA stB with erestA-ev ea stA | erestB-ev eb stB
... | _ , refl , _ | _ , eq , _ = case cong tag eq of λ ()

-- thread A waits on the store: the body read fixes the reply (`sServe`)
sim-ev (rWaitB q pr eb ss) st with comp-ev (prest-ns pr) (alphA1 {q}) (alphB-rest eb) (srest-alph ss) st
... | eP na _ stP with pblk-ev pr stP
...   | _ , refl , _ = ⊥-elim (na _)
sim-ev (rWaitB q pr eb ss) st | eAA a _ stA with a1-ev {q} stA
... | inj₁ (_ , refl , _) = ⊥-elim a
... | inj₂ (refl , _) = ⊥-elim a
sim-ev (rWaitB q pr eb ss) st | eAB _ stP stB with pblk-ev pr stP | erestB-ev eb stB
... | _ , refl , _ | _ , eq , _ = case cong tag eq of λ ()
sim-ev (rWaitB q pr eb ss) st | eSA _ stA stS with a1-ev {q} stA
... | inj₁ (x , refl , refl) with srest-get {h = proj₁ q} ss stS
...   | refl , ss′ = silent refl (tau sServe done) (rReadyB q pr eb ss′)
sim-ev (rWaitB q pr eb ss) st | eSA _ stA stS | inj₂ (refl , refl) =
  silent refl (tau sThrow done) (rThrownB pr eb (srest-lacks ss stS))
sim-ev (rWaitB q pr eb ss) st | eSB s stB _ with erestB-ev eb stB
... | _ , refl , _ = ⊥-elim s
sim-ev (rWaitB q pr eb ss) st | eBoth stA stB with a1-ev {q} stA | erestB-ev eb stB
... | inj₁ (_ , refl , _) | _ , eq , _ = case cong tag eq of λ ()
... | inj₂ (refl , _) | _ , eq , _ = case cong tag eq of λ ()

-- reply ready: thread A commands the Block, which carries the requested hash
sim-ev (rReadyB q pr eb ss) st with comp-ev (prest-ns pr) (alphA2 {proj₁ q}) (alphB-rest eb) (srest-alph ss) st
... | eP na _ stP with pblk-ev pr stP
...   | _ , refl , _ = ⊥-elim (na _)
sim-ev (rReadyB q pr eb ss) st | eAA _ stP stA with pblk-ev pr stP | a2-ev {proj₁ q} stA
... | _ , refl , refl | refl , refl = silent refl done (rSendB q eBack eb ss)
sim-ev (rReadyB q pr eb ss) st | eAB _ stP stB with pblk-ev pr stP | erestB-ev eb stB
... | _ , refl , _ | _ , eq , _ = case cong tag eq of λ ()
sim-ev (rReadyB q pr eb ss) st | eSA s stA _ with a2-ev {proj₁ q} stA
... | refl , _ = ⊥-elim s
sim-ev (rReadyB q pr eb ss) st | eSB s stB _ with erestB-ev eb stB
... | _ , refl , _ = ⊥-elim s
sim-ev (rReadyB q pr eb ss) st | eBoth stA stB with a2-ev {proj₁ q} stA | erestB-ev eb stB
... | refl , _ | _ , eq , _ = case cong tag eq of λ ()

-- the producer sends the Block: the spec's `sSendBlock`
sim-ev (rSendB q ea eb ss) st with comp-ev peer-ns (alphA-rest ea) (alphB-rest eb) (srest-alph ss) st
... | eP _ _ stP with p-snd-ev stP
...   | refl , refl = logged refl
        (λ { (Send , MsgLeiosBlock _ _) refl cap → _ , vis sSendBlock done , rIdle pBack ea eb ss })
sim-ev (rSendB q ea eb ss) st | eAA a stP _ with p-snd-ev stP
... | refl , _ = ⊥-elim a
sim-ev (rSendB q ea eb ss) st | eAB a stP _ with p-snd-ev stP
... | refl , _ = ⊥-elim a
sim-ev (rSendB q ea eb ss) st | eSA s stA _ with erestA-ev ea stA
... | _ , refl , _ = ⊥-elim s
sim-ev (rSendB q ea eb ss) st | eSB s stB _ with erestB-ev eb stB
... | _ , refl , _ = ⊥-elim s
sim-ev (rSendB q ea eb ss) st | eBoth stA stB with erestA-ev ea stA | erestB-ev eb stB
... | _ , refl , _ | _ , eq , _ = case cong tag eq of λ ()

-- BlockTxsRequest received: the report reaches thread B
sim-ev (rReqT qb bounds ea eb ss) st with comp-ev peer-ns (alphA-rest ea) (alphB-rest eb) (srest-alph ss) st
... | eP na _ stP with p-out-ev ⦃ DecEq-TxsRequest ⦄ stP
...   | refl , _ = ⊥-elim (na _)
sim-ev (rReqT qb bounds ea eb ss) st | eAA _ stP stA with p-out-ev ⦃ DecEq-TxsRequest ⦄ stP | erestA-ev ea stA
... | refl , _ | _ , eq , _ = case cong tag eq of λ ()
sim-ev (rReqT qb bounds ea eb ss) st | eAB _ stP stB with p-out-ev ⦃ DecEq-TxsRequest ⦄ stP | erestB-ev eb stB
... | refl , refl | _ , refl , refl = silent refl done (rWaitT qb bounds pBack ea ss)
sim-ev (rReqT qb bounds ea eb ss) st | eSA s stA _ with erestA-ev ea stA
... | _ , refl , _ = ⊥-elim s
sim-ev (rReqT qb bounds ea eb ss) st | eSB s stB _ with erestB-ev eb stB
... | _ , refl , _ = ⊥-elim s
sim-ev (rReqT qb bounds ea eb ss) st | eBoth stA stB with erestA-ev ea stA | erestB-ev eb stB
... | _ , refl , _ | _ , eq , _ = case cong tag eq of λ ()

-- thread B waits on the store: the read confirms the EB for the application reply
sim-ev (rWaitT qb bounds pr ea ss) st with comp-ev (prest-ns pr) (alphA-rest ea) (alphB1 {qb}) (srest-alph ss) st
... | eP na _ stP with ptx-ev pr stP
...   | _ , refl , _ = ⊥-elim (na _)
sim-ev (rWaitT qb bounds pr ea ss) st | eAA _ stP stA with ptx-ev pr stP | erestA-ev ea stA
... | _ , refl , _ | _ , eq , _ = case cong tag eq of λ ()
sim-ev (rWaitT qb bounds pr ea ss) st | eAB a _ stB with b1-ev {qb} stB
... | inj₁ (_ , refl , _) = ⊥-elim a
... | inj₂ (refl , _) = ⊥-elim a
sim-ev (rWaitT qb bounds pr ea ss) st | eSA s stA _ with erestA-ev ea stA
... | _ , refl , _ = ⊥-elim s
sim-ev (rWaitT qb bounds pr ea ss) st | eSB _ stB stS with b1-ev {qb} stB
... | inj₁ (_ , refl , refl) with srest-get {h = proj₁ (proj₁ qb)} ss stS
...   | _ , ss′ = silent refl (tau sServe done) (rWorkT qb (proj₂ qb) [] bounds refl pr ea ss′)
sim-ev (rWaitT qb bounds pr ea ss) st | eSB _ stB stS | inj₂ (refl , refl) =
  silent refl (tau sThrow done) (rThrownT pr ea (srest-lacks ss stS))
sim-ev (rWaitT qb bounds pr ea ss) st | eBoth stA stB with erestA-ev ea stA | b1-ev {qb} stB
... | _ , refl , _ | inj₁ (_ , eq , _) = case cong tag eq of λ ()
... | _ , refl , _ | inj₂ (eq , _) = case cong tag eq of λ ()

-- Transaction closure: completed accumulation commands the exact counted reply.
sim-ev (rWorkT qb [] acc [] count pr ea ss) st with comp-ev (prest-ns pr) (alphA-rest ea) (alphWork []) (srest-alph ss) st
... | eP na _ stP with ptx-ev pr stP
... | _ , refl , _ = ⊥-elim (na _)
sim-ev (rWorkT qb [] acc [] count pr ea ss) st | eAA _ stP stA with ptx-ev pr stP | erestA-ev ea stA
... | _ , refl , _ | _ , eq , _ = case cong tag eq of λ ()
sim-ev (rWorkT qb [] acc [] count pr ea ss) st | eAB _ stP stB with ptx-ev pr stP | work-done-ev stB
... | _ , refl , refl | refl , refl = silent refl done
  (rSendT qb acc (trans (L.length-map proj₂ acc) (trans (sym (N.+-identityʳ (length acc))) count)) ea eBack ss)
sim-ev (rWorkT qb [] acc [] count pr ea ss) st | eSA se stA _ with erestA-ev ea stA
... | _ , refl , _ = ⊥-elim se
sim-ev (rWorkT qb [] acc [] count pr ea ss) st | eSB se stB _ with work-done-ev stB
... | refl , _ = ⊥-elim se
sim-ev (rWorkT qb [] acc [] count pr ea ss) st | eBoth stA stB with erestA-ev ea stA | work-done-ev stB
... | _ , refl , _ | eq , _ = case cong tag eq of λ ()

-- Each held unit-transaction read advances the accumulator without a logged event.
sim-ev (rWorkT qb (o ∷ os) acc (bound ∷ bounds) count pr ea ss) st
  with comp-ev (prest-ns pr) (alphA-rest ea) (alphWork (bound ∷ bounds)) (srest-alph ss) st
... | eP na _ stP with ptx-ev pr stP
... | _ , refl , _ = ⊥-elim (na _)
sim-ev (rWorkT qb (o ∷ os) acc (bound ∷ bounds) count pr ea ss) st | eAA _ stP stA with ptx-ev pr stP | erestA-ev ea stA
... | _ , refl , _ | _ , eq , _ = case cong tag eq of λ ()
sim-ev (rWorkT qb (o ∷ os) acc (bound ∷ bounds) count pr ea ss) st | eAB ae _ stB with work-ev bound stB
... | inj₁ (refl , _) = ⊥-elim ae
... | inj₂ (refl , _) = ⊥-elim ae
sim-ev (rWorkT qb (o ∷ os) acc (bound ∷ bounds) count pr ea ss) st | eSA se stA _ with erestA-ev ea stA
... | _ , refl , _ = ⊥-elim se
sim-ev (rWorkT qb (o ∷ os) acc (bound ∷ bounds) count pr ea ss) st | eSB _ stB stS with work-ev bound stB
... | inj₁ (refl , refl) = silent refl done (rWorkT qb os (acc ++ ((o , Data.Unit.tt) ∷ [])) bounds
  (trans (cong (_+ length os) (L.length-++ acc))
    (trans (N.+-assoc (length acc) 1 (length os)) count)) pr ea (srest-tx ss stS))
... | inj₂ (refl , _) = ⊥-elim (srest-no-lacksTx ss stS)
sim-ev (rWorkT qb (o ∷ os) acc (bound ∷ bounds) count pr ea ss) st | eBoth stA stB with erestA-ev ea stA | work-ev bound stB
... | _ , refl , _ | inj₁ (eq , _) = case cong tag eq of λ ()
... | _ , refl , _ | inj₂ (eq , _) = case cong tag eq of λ ()

-- the producer sends the BlockTxs: the spec's `sSendTxs`
sim-ev (rSendT qb acc count ea eb ss) st with comp-ev peer-ns (alphA-rest ea) (alphB-rest eb) (srest-alph ss) st
... | eP _ _ stP with p-snd-ev stP
...   | refl , refl = logged refl
        (λ { (Send , MsgLeiosBlockTxs _ z) refl w → _ ,
          vis (subst (λ n → sReady (blockTxsReq (proj₁ (proj₁ qb)) (proj₂ (proj₁ qb)) n) -[ Send , MsgLeiosBlockTxs (length (map proj₂ acc)) z ]→ sIdle) count sSendTxs) done , rIdle pBack ea eb ss })
sim-ev (rSendT qb acc count ea eb ss) st | eAA a stP _ with p-snd-ev stP
... | refl , _ = ⊥-elim a
sim-ev (rSendT qb acc count ea eb ss) st | eAB a stP _ with p-snd-ev stP
... | refl , _ = ⊥-elim a
sim-ev (rSendT qb acc count ea eb ss) st | eSA s stA _ with erestA-ev ea stA
... | _ , refl , _ = ⊥-elim s
sim-ev (rSendT qb acc count ea eb ss) st | eSB s stB _ with erestB-ev eb stB
... | _ , refl , _ = ⊥-elim s
sim-ev (rSendT qb acc count ea eb ss) st | eBoth stA stB with erestA-ev ea stA | erestB-ev eb stB
... | _ , refl , _ | _ , eq , _ = case cong tag eq of λ ()

-- after Done nothing visible can happen: `done` has no partner
sim-ev (rDone ea eb ss) st with comp-ev peer-ns (alphA-rest ea) (alphB-rest eb) (srest-alph ss) st
... | eP na _ stP with p-done-ev stP
...   | _ , refl = ⊥-elim (na _)
sim-ev (rDone ea eb ss) st | eAA _ stP stA with p-done-ev stP | erestA-ev ea stA
... | _ , refl | _ , eq , _ = case cong tag eq of λ ()
sim-ev (rDone ea eb ss) st | eAB _ stP stB with p-done-ev stP | erestB-ev eb stB
... | _ , refl | _ , eq , _ = case cong tag eq of λ ()
sim-ev (rDone ea eb ss) st | eSA s stA _ with erestA-ev ea stA
... | _ , refl , _ = ⊥-elim s
sim-ev (rDone ea eb ss) st | eSB s stB _ with erestB-ev eb stB
... | _ , refl , _ = ⊥-elim s
sim-ev (rDone ea eb ss) st | eBoth stA stB with erestA-ev ea stA | erestB-ev eb stB
... | _ , refl , _ | _ , eq , _ = case cong tag eq of λ ()

-- A thrown composite may drain silently, but has no visible continuation.
sim-ev (rThrownB pr eb ss) st = ⊥-elim (thrownB-no-ev pr eb ss st)
sim-ev (rThrownT pr ea ss) st = ⊥-elim (thrownT-no-ev pr ea ss st)

-- Decoder failure has no further visible events to match.
sim-ev (rDecode ea eb ss) st = ⊥-elim (decode-no-ev ea eb ss st)
