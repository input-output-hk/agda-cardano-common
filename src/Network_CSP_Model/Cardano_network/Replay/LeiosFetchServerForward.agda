{-# OPTIONS --guardedness #-}

-- Forward moves for SERVER COMPLETENESS (trace-replay Phase 5, Increment 2).
-- The inversions of Increment 1 (`LeiosFetchServerParts`) do not run backwards, and
-- `sVis refl refl` only computes where no channel or value is compared with
-- a symbolic copy of itself.  This module supplies the moves that need more:
--   * `Fire`: a prefix fires any value and an output its own value, for
--     symbolic channels and values;
--   * the body store, for a symbolic `bs`: a body read of a held hash
--     (`store-read`, by induction on `h ∈ bs` through the keyed menu), the
--     round residual drains back to the loop head (`Back`, `store-back`), and
--     the store offers nothing outside `storeES` (`store-quiet`);
--   * producer and thread moves at symbolic values;
--   * lifts of component moves through the composite `C P Ta Tb S`.
-- Invariant 1 (B7a): checked with `agda --safe` on the command line.
module Cardano_network.Replay.LeiosFetchServerForward where

open import Cardano_network.Replay.LeiosFetchWords using (decoderOffsets; decodable)
import Data.Bool
import Cardano_network.Replay.LeiosFetchObs
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; _<_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_; yes; no; Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans)

open import Process_Trees using (PTree; ExtI; AnyTypes; react)
open import Class.DecEq using (DecEq)
open import Cardano_network.Params using (module Params)
open import Cardano_network.Base using (N2N_LeiosFetch; hi; FromResponder)
open import Cardano_network.Replay.ReplayParams using (replayParams; replayLP; replayTopo)
open import Cardano_network.Net replayParams using (Net_Api; Net_Api-≟; ApiLPTag; apiLP; input)
import Cardano_network.Net replayParams as Net
open import Cardano_network.Data replayParams using (Payload; MessageLeiosFetchP; leiosFetchP)
import Cardano_network.Data replayParams as Data
open import Cardano_network.LeiosFetchP replayParams using (LFPEv; LFPEv-≟; serverStepP; LFPState; stIdle)
import Cardano_network.LeiosFetchP replayParams as LFP
open import Cardano_network.Parametric.Leios.PeersP replayParams using (ιLFP; ιLFP⁻¹; ιLFP-linv)
open import Cardano_network.Parametric.Leios.NoLivelock.PeerLFP replayParams using (Rd; snd)
open import Cardano_network.Replay.LeiosFetchServerModel
open import Cardano_network.ApiAlphabet replayParams using (apiES)
open import Cardano_network.Replay.LeiosFetchServerParts
  using ( work-force; original-label; AE; SE; peerAfter; lat; bodyA; bodyB; a1; a2; b1; b2; C; smid
        ; □-force-rr; □-stable; store-ev; store-stable )

-- Negative reads are disjoint from the positive body reads constructed here.
import Cardano_network.Parametric.Leios.NodeLogicL
module Logic = Cardano_network.Parametric.Leios.NodeLogicL.Generic replayParams replayLP replayTopo apiES (λ _ → tt)
open Logic using (lacksBodies; lacksBodyEv)

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using (EventSet; ∅ES; _□_; _>>=_; _⊓_; _⦀_; mergeMaybe; viewV)
import CSP.Operators {E = LFPEv} LFPEv-≟ as LOp
import CSP.Rename {E₁ = LFPEv} {E₂ = Net_Api Payload} ιLFP ιLFP⁻¹ ιLFP-linv as RenLFP
import CSP.Laws.Traces.RenameDeadlock {E₁ = LFPEv} {E₂ = Net_Api Payload} ιLFP ιLFP⁻¹ ιLFP-linv as RD
open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (Event; evLabel; _─[_]─►_; ev; evl; τ; sVis; sSil)
import Semantics.LTS {E = LFPEv} {I = ExtI LFPEv} as F
open import Semantics.Deadlock {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (_⟹∖√⟨_⟩_; ∖√-refl; ∖√-τ)
open import Semantics.Stability {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using (stable→react)
open import CSP.Laws.Traces.TraceLawsParallel (Net_Api-≟ {Payload})
  using (Par-sync; Par-soloL; Par-soloR; Par-τ-L; Par-τ-R)
open import CSP.Laws.Traces.TraceLawsBind (Net_Api-≟ {Payload}) using (bind-ev; bind-τ)
open import CSP.Laws.Bisim.IterCong (Net_Api-≟ {Payload}) using (iter-bind-ev; iter-bind-τ)
import CSP.Laws.Bisim.IterCong LFPEv-≟ as ICL
open import CSP.Laws.Bisim.Laws (Net_Api-≟ {Payload}) using (⊓-stepL; ⊓-stepR)
open import CSP.Laws.DivFree.Loop (Net_Api-≟ {Payload}) using (loopStep)

------------------------------------------------------------------------
-- Firing prefixes and outputs at symbolic channels and values
------------------------------------------------------------------------

open import Cardano_network.Replay.LeiosFetchOutParts public using (module Fire)

open Fire (Net_Api-≟ {Payload}) using (pfx-fire; out-fire; out-br)
open Fire LFPEv-≟ using () renaming (out-fire to out-fireL)

------------------------------------------------------------------------
-- Labels
------------------------------------------------------------------------

-- pins the label of a step (so the implicit label arguments are solved)
stepAt : ∀ {P P′ : Proc} (e : Event) → P ─[ ev (evl e) ]─► P′ → P ─[ ev (evl e) ]─► P′
stepAt _ st = st

-- the store's body read of hash `h`, handing over the body `h`
getL : ℕ → Event
getL h = evLabel _ (getBodyEvS h) h

-- the session's api label of command `m` with value `v`
apiL : (m : ApiLPTag) → Net.ApiLPCar m → Event
apiL m v = evLabel _ (apiLP lS dS m) v

-- `Q` does not offer the label
Quiet : Proc → Event → Set₁
Quiet Q (evLabel X c a) = viewV (PTree.force Q) (X , c) a ≡ nothing

------------------------------------------------------------------------
-- Lifting component moves through the composite
------------------------------------------------------------------------

-- the producer alone (wire I/O)
liftP : ∀ {P P′ Ta Tb S e} → ¬ AE e → ¬ SE e → P ─[ ev (evl e) ]─► P′
      → Quiet (Ta ⦀ Tb) e → Quiet S e → C P Ta Tb S ─[ ev (evl e) ]─► C P′ Ta Tb S
liftP na ns st qT qS = Par-soloL storeES _ _ _ ns (Par-soloL apiES _ _ _ na st qT) qS

-- an api rendezvous of the producer with thread A
liftPA : ∀ {P P′ Ta Ta′ Tb S e} → AE e → ¬ SE e → P ─[ ev (evl e) ]─► P′ → Ta ─[ ev (evl e) ]─► Ta′
       → Quiet Tb e → Quiet S e → C P Ta Tb S ─[ ev (evl e) ]─► C P′ Ta′ Tb S
liftPA ae ns stP stA qB qS =
  Par-soloL storeES _ _ _ ns (Par-sync apiES _ _ _ ae stP (Par-soloL ∅ES _ _ _ (λ ()) stA qB)) qS

-- an api rendezvous of the producer with thread B
liftPB : ∀ {P P′ Ta Tb Tb′ S e} → AE e → ¬ SE e → P ─[ ev (evl e) ]─► P′ → Tb ─[ ev (evl e) ]─► Tb′
       → Quiet Ta e → Quiet S e → C P Ta Tb S ─[ ev (evl e) ]─► C P′ Ta Tb′ S
liftPB ae ns stP stB qA qS =
  Par-soloL storeES _ _ _ ns (Par-sync apiES _ _ _ ae stP (Par-soloR ∅ES _ _ _ (λ ()) stB qA)) qS

-- a store rendezvous of thread A with the store
liftAS : ∀ {P Ta Ta′ Tb S S′ e} → SE e → ¬ AE e → Ta ─[ ev (evl e) ]─► Ta′ → S ─[ ev (evl e) ]─► S′
       → Quiet Tb e → Quiet P e → C P Ta Tb S ─[ ev (evl e) ]─► C P Ta′ Tb S′
liftAS se na stA stS qB qP =
  Par-sync storeES _ _ _ se (Par-soloR apiES _ _ _ na (Par-soloL ∅ES _ _ _ (λ ()) stA qB) qP) stS

-- a store rendezvous of thread B with the store
liftBS : ∀ {P Ta Tb Tb′ S S′ e} → SE e → ¬ AE e → Tb ─[ ev (evl e) ]─► Tb′ → S ─[ ev (evl e) ]─► S′
       → Quiet Ta e → Quiet P e → C P Ta Tb S ─[ ev (evl e) ]─► C P Ta Tb′ S′
liftBS se na stB stS qA qP =
  Par-sync storeES _ _ _ se (Par-soloR apiES _ _ _ na (Par-soloR ∅ES _ _ _ (λ ()) stB qA) qP) stS

-- the producer's τ
liftτP : ∀ {P P′ Ta Tb S} → P ─[ τ ]─► P′ → C P Ta Tb S ─[ τ ]─► C P′ Ta Tb S
liftτP st = Par-τ-L storeES _ _ _ (Par-τ-L apiES _ _ _ st)

-- thread A's τ
liftτA : ∀ {P Ta Ta′ Tb S} → Ta ─[ τ ]─► Ta′ → C P Ta Tb S ─[ τ ]─► C P Ta′ Tb S
liftτA st = Par-τ-L storeES _ _ _ (Par-τ-R apiES _ _ _ (Par-τ-L ∅ES _ _ _ st))

-- thread B's τ
liftτB : ∀ {P Ta Tb Tb′ S} → Tb ─[ τ ]─► Tb′ → C P Ta Tb S ─[ τ ]─► C P Ta Tb′ S
liftτB st = Par-τ-L storeES _ _ _ (Par-τ-R apiES _ _ _ (Par-τ-R ∅ES _ _ _ st))

-- the store's τ
liftτS : ∀ {P Ta Tb S S′} → S ─[ τ ]─► S′ → C P Ta Tb S ─[ τ ]─► C P Ta Tb S′
liftτS st = Par-τ-R storeES _ _ _ st

------------------------------------------------------------------------
-- The body store, for a symbolic `bs`
------------------------------------------------------------------------

-- the keyed menu is stable
ob-stable : ∀ bs xs → Process_Trees.isStable (offerBodies nS bs xs)
ob-stable bs []         = λ _ _ → refl
ob-stable bs (eb ∷ ebs) =
  □-stable {P = Op.Output (getBodyEvS eb) eb (Op.Ret bs)} {Q = offerBodies nS bs ebs} (λ _ _ → refl) (ob-stable bs ebs)

-- a round residual that τ-drains back to `Ret bs`
data Back (bs : Bodies) : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Bodies → Set₁ where
  -- drained
  bRet : Back bs (Op.Ret bs)
  -- one τ closer
  bτ   : ∀ {c c′} → c ─[ τ ]─► c′ → Back bs c′ → Back bs c

-- a `□` of two react nodes fires what its merged offer map offers
□-fire : ∀ {P Q : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Bodies} {vP τP vQ τQ}
           {at : AnyTypes (Net_Api Payload)} {a : proj₁ at} {M}
       → PTree.force P ≡ react vP τP → PTree.force Q ≡ react vQ τQ
       → mergeMaybe (vP at a) (vQ at a) ≡ just M
       → (P □ Q) ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► M
□-fire {P} {Q} eqP eqQ br = sVis (□-force-rr {P = P} {Q = Q} eqP eqQ) br

-- the keyed menu hands over the body with hash `h` whenever `h ∈ xs`
ob-fire : ∀ bs xs {h} → h ∈ xs
        → Σ[ c ∈ PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Bodies ]
            (offerBodies nS bs xs ─[ ev (evl (getL h)) ]─► c × Back bs c)
ob-fire bs (eb ∷ ebs) {h} (here refl) with stable→react {t = offerBodies nS bs ebs} (ob-stable bs ebs)
... | vQ , τQ , eqQ , _ with vQ (_ , getBodyEvS h) h in e
...   | nothing = Op.Ret bs , □-fire refl eqQ (cong₂ mergeMaybe (out-br (getBodyEvS h) h (Op.Ret bs)) e) , bRet
...   | just c′ = Op.Ret bs ⊓ c′ , □-fire refl eqQ (cong₂ mergeMaybe (out-br (getBodyEvS h) h (Op.Ret bs)) e)
                , bτ (⊓-stepL _ _) bRet
ob-fire bs (eb ∷ ebs) {h} (there m) with ob-fire bs ebs m
... | c , sVis eqQ brQ , bk with Op.Output-cont (getBodyEvS eb) eb (Op.Ret bs) (_ , getBodyEvS h) h in e
...   | nothing = c , □-fire refl eqQ (cong₂ mergeMaybe e brQ) , bk
...   | just p  = p ⊓ c , □-fire refl eqQ (cong₂ mergeMaybe e brQ) , bτ (⊓-stepR _ _) bk

-- a body read off one store round, for a held hash (the deposit arm stays silent)
original-round-fire : ∀ bs {h} → h ∈ bs
           → Σ[ c ∈ PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Bodies ]
               (originalBodyStep nS bs ─[ ev (evl (getL h)) ]─► c × Back bs c)
original-round-fire bs m with ob-fire bs bs m
... | c , sVis eqQ brQ , bk = c , □-fire refl (□-force-rr {P = offerBodies nS bs bs} {Q = lacksBodies nS bs} eqQ refl)
  (cong (mergeMaybe nothing) (trans (cong (λ z → mergeMaybe z nothing) brQ) (mergeMaybe-right c))) , bk
  where
  -- A positive read has no competing negative-menu continuation.
  mergeMaybe-right : (c : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Bodies)
                   → mergeMaybe (just c) nothing ≡ just c
  mergeMaybe-right _ = refl

-- Extending the store by a tx arm preserves every positive body read.
round-fire : ∀ bs {h} → h ∈ bs →
  Σ[ c ∈ PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Bodies ]
    (bodyStep nS bs ─[ ev (evl (getL h)) ]─► c × Back bs c)
round-fire bs m with original-round-fire bs m
... | c , sVis eq br , back = c , □-fire eq refl (cong (λ v → mergeMaybe v nothing) br) , back

-- a body read at the store's loop head, for a held hash: the store goes mid-round
store-read : ∀ bs {h} → h ∈ bs
           → Σ[ c ∈ PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Bodies ]
               (bodyStore nS bs ─[ ev (evl (getL h)) ]─► smid c × Back bs c)
store-read bs m with round-fire bs m
... | c , st , bk =
  c , iter-bind-ev (loopStep (bodyStep nS)) (bodyStep nS bs >>= λ a′ → Op.Ret (inj₁ a′))
        (bind-ev (λ a′ → Op.Ret (inj₁ a′)) (bodyStep nS bs) st)
    , bk

-- a drained residual takes the store back to its loop head, silently
store-back : ∀ {bs c P Ta Tb} → Back bs c → C P Ta Tb (smid c) ⟹∖√⟨ [] ⟩ C P Ta Tb (bodyStore nS bs)
store-back bRet       = ∖√-τ (liftτS (sSil refl)) ∖√-refl
store-back (bτ st bk) =
  ∖√-τ (liftτS (iter-bind-τ (loopStep (bodyStep nS)) _ (bind-τ (λ a′ → Op.Ret (inj₁ a′)) _ st))) (store-back bk)

-- a react node offers nothing it cannot step on
quiet-from : ∀ {Q : Proc} {v τc X} {c : Net_Api Payload X} {a : X}
           → PTree.force Q ≡ react v τc → (∀ {Q′} → ¬ (Q ─[ ev (evl (evLabel X c a)) ]─► Q′))
           → Quiet Q (evLabel X c a)
quiet-from {Q} {v} {τc} {X} {c} {a} eq nst = trans (cong (λ n → viewV n (X , c) a) eq) (go (v (X , c) a) refl)
  where
    -- the offer is nothing, since any offer would be a step
    go : ∀ m → v (X , c) a ≡ m → m ≡ nothing
    go nothing  _ = refl
    go (just _) e = ⊥-elim (nst (sVis eq e))

-- the store offers nothing outside `storeES`
store-quiet : ∀ bs {X} {c : Net_Api Payload X} {a : X} → ¬ EventSet.mem storeES (X , c) a
            → Quiet (bodyStore nS bs) (evLabel X c a)
store-quiet bs ns =
  quiet-from (proj₁ (proj₂ (proj₂ (stable→react {t = bodyStore nS bs} (store-stable bs)))))
             (λ st → ns (store-ev {bs} st))

------------------------------------------------------------------------
-- Producer and thread moves at symbolic values
------------------------------------------------------------------------

-- the renamed producer performs its round's moves, renamed
peer-fwd : ∀ {t t′ : Rd} {A} {e₁ : LFPEv A} {a : A}
         → t F.─[ F.ev (F.evl (F.evLabel A e₁ a)) ]─► t′
         → peerAfter t ─[ ev (evl (evLabel A (ιLFP e₁) a)) ]─► peerAfter t′
peer-fwd {A = A} {e₁} {a} st =
  RD.ren-ev-fwd {inv = RenLFP.ι-vis-inv} {at = A , e₁} {a = a} {bt = A , ιLFP e₁} {b = a}
    (ICL.iter-bind-ev (serverStepP lS dS) _ st) ivi
  where
    -- the rename's inverse recovers the source event
    ivi : RenLFP.ι-vis-inv (A , ιLFP e₁) a ≡ just ((A , e₁) , a)
    ivi rewrite ιLFP-linv e₁ = refl

-- the producer reports `v` on api command `m`, then its loop-back to `st` is pending
p-out-fwd : ∀ {m : ApiLPTag} {d : DecEq (Net.ApiLPCar m)} {v st}
          → peerAfter (LOp.Output ⦃ d ⦄ (LFP.apiLPev lS dS m) v (LOp.Ret (inj₁ st)))
              ─[ ev (evl (apiL m v)) ]─► peerAfter (LOp.Ret (inj₁ st))
p-out-fwd {d = d} = peer-fwd (out-fireL {d = d})

-- the producer sends `msg`, then its loop-back to Idle is pending
p-snd-fwd : ∀ {msg}
          → peerAfter (snd lS dS FromResponder msg stIdle)
              ─[ ev (evl (evLabel _ (input lS dS N2N_LeiosFetch) (tt , FromResponder , tt , leiosFetchP msg))) ]─►
            peerAfter (LOp.Ret (inj₁ stIdle))
p-snd-fwd = peer-fwd out-fireL

-- The positive branch fires alone: its channel is disjoint from the negative read.
positive-read : ∀ {h} {k : ℕ → Proc} →
  ((getBodyEvS h Op.⟶ k) □ (lacksBodyEv nS h Op.⟶₀ Op.Stop))
  ─[ ev (evl (getL h)) ]─► k h
positive-read {h} {k} = sVis refl
  (cong (λ m → mergeMaybe m nothing) (Fire.pfx-br (Net_Api-≟ {Payload}) (getBodyEvS h) k h))

-- thread A reads the reported hash's body from the store
a1-fwd : ∀ {q} → lat bodyA (a1 q) ─[ ev (evl (getL (proj₁ q))) ]─► lat bodyA (a2 (proj₁ q))
a1-fwd = iter-bind-ev _ _ (bind-ev _ _ positive-read)

-- thread A commands the Block with the body it holds
a2-fwd : ∀ {eb} → lat bodyA (a2 eb) ─[ ev (evl (apiL Net.lfpSendBlock eb)) ]─► lat bodyA Op.Skip
a2-fwd = iter-bind-ev _ _ (bind-ev _ _ out-fire)

-- thread B confirms the reported hash is held (empty bitmap: the reply follows at once)
b1-fwd : ∀ {q} → lat bodyB (b1 (q , [])) ─[ ev (evl (getL (proj₁ q))) ]─► lat bodyB (b2 q)
b1-fwd = iter-bind-ev _ _ (bind-ev _ _ positive-read)

-- thread B commands the (empty) BlockTxs for point `q`
b2-fwd : ∀ {q} → lat bodyB (b2 q) ─[ ev (evl (apiL Net.lfpSendBlockTxs (q , []))) ]─► lat bodyB Op.Skip
b2-fwd = iter-bind-ev _ _ (bind-ev _ _ out-fire)

-- The original body menu is stable before the extra transaction arm is added.
original-round-stable : ∀ bs → Process_Trees.isStable (originalBodyStep nS bs)
original-round-stable bs = □-stable {P = Op.Prefix (putBodyEv nS) _}
  {Q = offerBodies nS bs bs □ lacksBodies nS bs} (λ _ _ → refl)
  (□-stable {P = offerBodies nS bs bs} {Q = lacksBodies nS bs} (ob-stable bs bs) (λ _ _ → refl))

-- The held unit tx fires alone, since every original-menu label is a body label.
tx-round-fire : ∀ bs → bodyStep nS bs ─[ ev (evl (evLabel Data.Unit.⊤ (getTxEv nS tt) tt)) ]─► Op.Ret bs
tx-round-fire bs with stable→react {t = originalBodyStep nS bs} (original-round-stable bs)
... | v , τc , eq , _ with v (_ , getTxEv nS tt) tt in br
... | nothing = □-fire eq refl (cong₂ mergeMaybe br (out-br {d = Params.decTx replayParams} (getTxEv nS tt) tt (Op.Ret bs)))
... | just p = ⊥-elim (original-label {bs = bs} (sVis eq br))

-- The replay store can always hand over the sole unit transaction.
store-tx-read : ∀ bs → bodyStore nS bs ─[ ev (evl (evLabel Data.Unit.⊤ (getTxEv nS tt) tt)) ]─► smid (Op.Ret bs)
store-tx-read bs = iter-bind-ev (loopStep (bodyStep nS)) _
  (bind-ev (λ a′ → Op.Ret (inj₁ a′)) (bodyStep nS bs) (tx-round-fire bs))

-- Body confirmation works for an arbitrary requested offset list.
b1-any-fwd : ∀ {q bm} → lat bodyB (b1 (q , bm)) ─[ ev (evl (getL (proj₁ q))) ]─►
  lat bodyB (serveTxs nS lS hi q bm [])
b1-any-fwd = iter-bind-ev _ _ (bind-ev _ _ positive-read)

-- A valid offset's transaction read advances the indexed accumulator.
work-fwd : ∀ {q o os acc} → o Data.Nat.< Cardano_network.Replay.LeiosFetchWords.decoderOffsets →
  lat bodyB (serveTxs nS lS hi q (o ∷ os) acc) ─[ ev (evl (evLabel Data.Unit.⊤ (getTxEv nS tt) tt)) ]─►
  lat bodyB (serveTxs nS lS hi q os (acc Data.List.++ ((o , tt) ∷ [])))
work-fwd {q} {o} {os} {acc} bound rewrite work-force q o os acc bound =
  iter-bind-ev _ _ (bind-ev _ _ (sVis refl refl))

-- The completed closure commands its actual accumulated indexed transactions.
work-out-fwd : ∀ {q acc} → lat bodyB (serveTxs nS lS hi q [] acc) ─[ ev (evl (apiL Net.lfpSendBlockTxs (q , acc))) ]─► lat bodyB Op.Skip
work-out-fwd = iter-bind-ev _ _ (bind-ev _ _ out-fire)

-- A decoded transaction request is received and reported at its actual bitmap.
p-recvT-fwd : ∀ q bm → Data.Bool.T (Cardano_network.Replay.LeiosFetchWords.decodable bm) →
  peerAfter (serverStepP lS dS stIdle) ─[ ev (evl (evLabel _ (Net.output lS dS N2N_LeiosFetch)
    (tt , Cardano_network.Base.FromInitiator , tt , leiosFetchP (Data.MsgLFPBlockTxsRequest q bm)))) ]─►
  peerAfter (LOp.Output ⦃ Data.DecEq-TxsRequest ⦄ (LFP.apiLPev lS dS Net.lfpReqBlockTxsRequest)
    (q , bm) (LOp.Ret (inj₁ (LFP.stBlockTxs q bm))))
p-recvT-fwd q bm ok = peer-fwd (F.sVis refl branch)
  where
  -- Expose the successful decoder Boolean at the concrete receive offer.
  branch : LOp.viewV (PTree.force (serverStepP lS dS stIdle)) (_ , LFP.receiveLFP lS dS)
    (tt , Cardano_network.Base.FromInitiator , tt , leiosFetchP (Data.MsgLFPBlockTxsRequest q bm)) ≡
    just (LOp.Output ⦃ Data.DecEq-TxsRequest ⦄ (LFP.apiLPev lS dS Net.lfpReqBlockTxsRequest)
      (q , bm) (LOp.Ret (inj₁ (LFP.stBlockTxs q bm))))
  branch rewrite Cardano_network.Replay.LeiosFetchObs.T-true ok = refl
