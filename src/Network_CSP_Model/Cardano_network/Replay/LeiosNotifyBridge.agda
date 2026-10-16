{-# OPTIONS --guardedness #-}

-- Wire-order correspondence with the EXISTING LeiosNotifyP peers at replayParams,
-- link 0 / hi. Both directions forget notification payloads, retain all six
-- message kinds and their wire directions, and exclude only the semantic tick.
-- API and local done events are unlogged. No NodeLogicL/store claim is made.
module Cardano_network.Replay.LeiosNotifyBridge where

open import Data.Nat using (ℕ)
open import Data.Fin using (zero)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (universal)
open import Data.List.Properties using (∷-injective)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (case_of_)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Class.DecEq using (DecEq)
open import Process_Trees using (PTree; ExtI; react)
open import Cardano_network.Base using (hi; FromInitiator; FromResponder; Mode)
open import Cardano_network.Replay.ReplayParams using (replayParams)
open import Cardano_network.Net replayParams using (Link; ApiLPTag; ApiLPCar; lnpSendRequestNext; lnpSendDone; lnpSendBlockAnnouncement; lnpSendBlockOffer; lnpSendBlockTxsOffer; lnpSendVotes)
open import Cardano_network.Data replayParams
open import Cardano_network.LeiosNotifyP replayParams
open import Cardano_network.Parametric.Leios.NoLivelock.PeerLNP replayParams
  using (Rd; snd; cIdleV; ciNext; ciDone; cBusyV; cbAnn; cbOff; cbTxs; cbVote;
         sIdleV; siNext; siDone; sBusyV; sbAnn; sbOff; sbTxs; sbVote)
open import CSP.Operators LNPEv-≟ using (Ret; Output; Prefix₀; ∅t; iter-bind)
open import CSP.Laws.DivFree.Loop LNPEv-≟ using (iter-τ-elim; iter-ev-elim; itτ; itBack)
open import CSP.Laws.Bisim.IterCong LNPEv-≟ using (iter-bind-ev)
open import CSP.Laws.Traces.PrefixInversion LNPEv-≟ using (⟶₀-ev-inv)
open import Cardano_network.Replay.LeiosFetchServerParts using (module OutInv)
open OutInv LNPEv-≟ using (out-ev)
open import Cardano_network.Replay.LeiosFetchServerForward using (module Fire)
open Fire LNPEv-≟ using (out-fire; pfx-fire)
open import Semantics.LTS {E = LNPEv} {I = ExtI LNPEv}
  using (Event; evLabel; _─[_]─►_; ev; evl; τ; sVis; sSil; sTau)
open import Semantics.Deadlock {E = LNPEv} {I = ExtI LNPEv}
  using (_⟹∖√⟨_⟩_; ∖√-refl; ∖√-τ; ∖√-ev)
import Semantics.Replay.Bridge {E = LNPEv} {I = ExtI LNPEv} as Br
open import Cardano_network.Replay.LeiosNotifySession
  using (Role; client; server; Direction; Send; Recv; Kind; request; announcement;
         offer; txsOffer; votes; doneK; St; idle; busy; closed; E; Observed;
         forget; nextKind; module Spec; RequestNext; BlockAnnouncement;
         BlockOffer; BlockTxsOffer; Votes; Done)
import Cardano_network.Replay.LeiosNotifySession as N

-- The model endpoint, matching the one-link concrete replay parameterization.
l : Link
l = zero

-- The peer direction at the selected model endpoint.
d : Cardano_network.Base.Dir
d = hi

-- A finished or running Notify peer tree.
Proc : Set₁
Proc = PTree LNPEv (ExtI LNPEv) Rr

-- Select the original peer's iteration body by its role.
step : Role → LNPState → Rd
step client = clientStepP l d
step server = serverStepP l d

-- Wrap a residual round with the original iteration body.
It : Role → Rd → Proc
It r t = iter-bind t (step r)

-- Interpret the three original protocol control states.
ctl : LNPState → St
ctl stIdle = idle
ctl stBusy = busy
ctl stDone = closed

-- Observe message kind while explicitly forgetting payload fields.
wireKind : MessageLeiosNotifyP → Kind
wireKind MsgLNPRequestNext = request
wireKind (MsgLNPBlockAnnouncement _) = announcement
wireKind (MsgLNPBlockOffer _ _) = offer
wireKind (MsgLNPBlockTxsOffer _) = txsOffer
wireKind (MsgLNPVotes _) = votes
wireKind MsgLNPDone = doneK

-- Wire directions/kinds are observed; API and local done are not.
cls : Event → Maybe Observed
cls (evLabel _ (sendLNP _ _) (_ , _ , _ , leiosNotifyP m)) = just (Send , wireKind m)
cls (evLabel _ (receiveLNP _ _) (_ , _ , _ , leiosNotifyP m)) = just (Recv , wireKind m)
cls _ = nothing

-- Exact equality at the stated direction/kind abstraction.
Obs : List Event → List E → Set
Obs = Br.Obs cls forget

-- A canonical log payload for each observed message kind.
canonical : Kind → N.Msg
canonical request = RequestNext
canonical announcement = BlockAnnouncement nothing
canonical offer = BlockOffer 0 0 0
canonical txsOffer = BlockTxsOffer 0 0
canonical votes = Votes []
canonical doneK = Done

-- Canonical payloads preserve the observable message kind.
canonical-kind : ∀ k → N.kind (canonical k) ≡ k
canonical-kind request = refl
canonical-kind announcement = refl
canonical-kind offer = refl
canonical-kind txsOffer = refl
canonical-kind votes = refl
canonical-kind doneK = refl

-- Any visible residual step lifts through the original loop.
fire : ∀ {r t t′ x} → t ─[ ev (evl x) ]─► t′ → It r t ─[ ev (evl x) ]─► It r t′
fire {r} {t} = iter-bind-ev (step r) t

-- The loop-back is the original iter silent transition.
back : ∀ {r a} → It r (Ret (inj₁ a)) ─[ τ ]─► It r (step r a)
back = sSil refl

-- A stable menu or output residual has no silent transitions.
noτ : ∀ {r t v M} → PTree.force t ≡ react v ∅t → ¬ (It r t ─[ τ ]─► M)
noτ {r} {t} eq st with iter-τ-elim t (step r) st
... | itτ _ (sSil eq′) _ = case trans (sym eq) eq′ of λ ()
... | itBack _ eq′ _ = case trans (sym eq) eq′ of λ ()
... | itτ _ (sTau eq′ br) _ with trans (sym eq) eq′
...   | refl = case br of λ ()

-- A final return has no silent move.
end-noτ : ∀ {r M u} → ¬ (It r (Ret (inj₂ u)) ─[ τ ]─► M)
end-noτ {r} {u = u} st with iter-τ-elim (Ret (inj₂ u)) (step r) st
... | itτ _ (sSil ()) _
... | itτ _ (sTau () _) _
... | itBack _ () _

-- Returned residuals have no wire or API event.
ret-noev : ∀ {r a x M} → ¬ (It r (Ret a) ─[ ev (evl x) ]─► M)
ret-noev {r} {a} st with iter-ev-elim (Ret a) (step r) st
... | _ , sVis () _ , _

-- The only τ out of a pending loop-back reaches the next loop head.
back-inv : ∀ {r a M} → It r (Ret (inj₁ a)) ─[ τ ]─► M → M ≡ It r (step r a)
back-inv {r} {a} st with iter-τ-elim (Ret (inj₁ a)) (step r) st
... | itτ _ (sSil ()) _
... | itτ _ (sTau () _) _
... | itBack _ refl refl = refl

-- Output inversion supplies its exact event and following residual.
out-inv : ∀ {r B} {dd : DecEq B} {c : LNPEv B} {v a x M} →
          It r (Output ⦃ dd ⦄ c v (Ret a)) ─[ ev (evl x) ]─► M →
          x ≡ evLabel B c v × M ≡ It r (Ret a)
out-inv {r} {dd = dd} {c} {v} {a} st with iter-ev-elim (Output ⦃ dd ⦄ c v (Ret a)) (step r) st
... | _ , p , refl with out-ev ⦃ dd ⦄ p
...   | refl , refl = refl , refl

-- Relate all reachable residuals, including unlogged API hand-offs.
data Rel (r : Role) : Proc → St → Set₁ where
  head : ∀ {a} → Rel r (It r (step r a)) (ctl a)
  loopBack : ∀ {a} → Rel r (It r (Ret (inj₁ a))) (ctl a)
  sending : ∀ {md m a s} → Spec.Step r s (Send , canonical (wireKind m)) (ctl a) →
            Rel r (It r (snd l d md m a)) s
  delivering : ∀ {tag} {dd : DecEq (ApiLPCar tag)} {v a} →
               Rel r (It r (Output ⦃ dd ⦄ (apiLPev l d tag) v (Ret (inj₁ a)))) (ctl a)
  doneNotice : Rel r (It r (doneLNP l d ⟶₀ Ret (inj₁ stDone))) closed

-- Model silent steps leave the first-order control state unchanged.
simτ : ∀ {r P P′ s} → Rel r P s → P ─[ τ ]─► P′ →
       Σ[ s′ ∈ St ] (Spec._⇒⟨_⟩_ r s [] s′ × Rel r P′ s′)
simτ {client} (head {stIdle}) p = ⊥-elim (noτ {r = client} refl p)
simτ {client} (head {stBusy}) p = ⊥-elim (noτ {r = client} refl p)
simτ {client} (head {stDone}) p = ⊥-elim (end-noτ {r = client} p)
simτ {server} (head {stIdle}) p = ⊥-elim (noτ {r = server} refl p)
simτ {server} (head {stBusy}) p = ⊥-elim (noτ {r = server} refl p)
simτ {server} (head {stDone}) p = ⊥-elim (end-noτ {r = server} p)
simτ {r} loopBack p with back-inv {r = r} p
... | refl = _ , Spec.done {role = r} , head
simτ {r} (sending _) p = ⊥-elim (noτ {r = r} refl p)
simτ {r} delivering p = ⊥-elim (noτ {r = r} refl p)
simτ {r} doneNotice p = ⊥-elim (noτ {r = r} refl p)

-- Match every visible model event with zero or one observed spec steps.
simEv : ∀ {r P P′ s x} → Rel r P s → P ─[ ev (evl x) ]─► P′ →
        Σ[ es ∈ List E ] Σ[ s′ ∈ St ] (Obs (x ∷ []) es × Spec._⇒⟨_⟩_ r s es s′ × Rel r P′ s′)
simEv {client} (head {stIdle}) p with iter-ev-elim (step client stIdle) (step client) p
... | _ , q , refl with cIdleV q
...   | ciNext _ = [] , _ , refl , Spec.done {role = client} , sending refl
...   | ciDone _ = [] , _ , refl , Spec.done {role = client} , sending refl
simEv {client} (head {stBusy}) p with iter-ev-elim (step client stBusy) (step client) p
... | _ , q , refl with cBusyV q
...   | cbAnn h = (Recv , BlockAnnouncement nothing) ∷ [] , _ , refl , Spec.vis {role = client} refl (Spec.done {role = client}) , delivering
...   | cbOff pt sz = (Recv , BlockOffer 0 0 0) ∷ [] , _ , refl , Spec.vis {role = client} refl (Spec.done {role = client}) , delivering
...   | cbTxs pt = (Recv , BlockTxsOffer 0 0) ∷ [] , _ , refl , Spec.vis {role = client} refl (Spec.done {role = client}) , delivering
...   | cbVote vs = (Recv , Votes []) ∷ [] , _ , refl , Spec.vis {role = client} refl (Spec.done {role = client}) , delivering
simEv {client} (head {stDone}) p = ⊥-elim (ret-noev {r = client} p)
simEv {server} (head {stIdle}) p with iter-ev-elim (step server stIdle) (step server) p
... | _ , q , refl with sIdleV q
...   | siNext = (Recv , RequestNext) ∷ [] , _ , refl , Spec.vis {role = server} refl (Spec.done {role = server}) , loopBack
...   | siDone = (Recv , Done) ∷ [] , _ , refl , Spec.vis {role = server} refl (Spec.done {role = server}) , doneNotice
simEv {server} (head {stBusy}) p with iter-ev-elim (step server stBusy) (step server) p
... | _ , q , refl with sBusyV q
...   | sbAnn h = [] , _ , refl , Spec.done {role = server} , sending refl
...   | sbOff pt sz = [] , _ , refl , Spec.done {role = server} , sending refl
...   | sbTxs pt = [] , _ , refl , Spec.done {role = server} , sending refl
...   | sbVote vs = [] , _ , refl , Spec.done {role = server} , sending refl
simEv {server} (head {stDone}) p = ⊥-elim (ret-noev {r = server} p)
simEv {r} loopBack p = ⊥-elim (ret-noev {r = r} p)
simEv {r} (sending {m = m} pr) p with out-inv {r = r} p
... | refl , refl = (Send , canonical (wireKind m)) ∷ [] , _ ,
  cong (λ k → (Send , k) ∷ []) (sym (canonical-kind (wireKind m))) , Spec.vis {role = r} pr (Spec.done {role = r}) , loopBack
simEv {r} delivering p with out-inv {r = r} p
... | refl , refl = [] , _ , refl , Spec.done {role = r} , loopBack
simEv {r} doneNotice p with iter-ev-elim (doneLNP l d ⟶₀ Ret (inj₁ stDone)) (step r) p
... | _ , q , refl with ⟶₀-ev-inv q
...   | _ , refl , refl = [] , _ , refl , Spec.done {role = r} , loopBack

-- The existing peer is simulated by the first-order session specification.
simulation : (r : Role) → Br.Sim (Spec.leiosNotify r) cls forget (Rel r)
simulation r = record { sim-τ = simτ ; sim-ev = simEv }

-- Equal observed traces have the same control transitions and endpoint.
transport : ∀ {r s t es fs} → map forget es ≡ map forget fs →
            Spec._⇒⟨_⟩_ r s es t → Spec._⇒⟨_⟩_ r s fs t
transport {r} {fs = []} refl (Spec.done) = Spec.done {role = r}
transport {fs = _ ∷ _} () (Spec.done)
transport _ (Spec.tau () _)
transport {r} {fs = []} () (Spec.vis st p)
transport {r} {s} {fs = f ∷ fs} eq (Spec.vis st p) =
  Spec.vis {role = r} (trans (cong (nextKind r s) (sym (proj₁ (∷-injective eq)))) st)
    (transport {r = r} (proj₂ (∷-injective eq)) p)

-- All original peer observations satisfy the strict wire-order specification.
sound : ∀ r {t M es} → It r (step r stIdle) ⟹∖√⟨ t ⟩ M → Obs t es → Spec.HasTrace r idle es
sound r run obs with Br.sound (Spec.leiosNotify r) cls forget (simulation r) head run
... | es′ , s′ , obs′ , p , _ = s′ , transport {r = r} (trans (sym obs′) obs) p

-- Co-simulation chooses the original peer at each control-state loop head.
data CoRel (r : Role) : Proc → St → Set₁ where
  headC : ∀ {a} → CoRel r (It r (step r a)) (ctl a)

-- There are no first-order silent transitions in the strict wire specification.
coTau : ∀ {r P s s′} → CoRel r P s → ⊥ →
        Σ[ P′ ∈ Proc ] Σ[ t ∈ List Event ] (P ⟹∖√⟨ t ⟩ P′ × Obs t [] × CoRel r P′ s′)
coTau _ ()

-- Realize each legal observed event with original peer wire/API/loop moves.
coEv : ∀ {r P s s′ e} → CoRel r P s → ⊤ → Spec.Step r s e s′ →
       Σ[ P′ ∈ Proc ] Σ[ t ∈ List Event ] (P ⟹∖√⟨ t ⟩ P′ × Obs t (e ∷ []) × CoRel r P′ s′)
coEv {client} {e = Send , RequestNext} (headC {stIdle}) _ refl =
  _ , _ ,
  (∖√-ev (fire {r = client} (sVis {at = _ , apiLPev l d lnpSendRequestNext} {a = tt} refl refl))
    (∖√-ev (fire {r = client} out-fire)
    (∖√-τ (back {r = client}) ∖√-refl)))
  , refl , headC
coEv {client} {e = Send , (BlockAnnouncement x)} (headC {stIdle}) _ ()
coEv {client} {e = Send , (BlockOffer h sl z)} (headC {stIdle}) _ ()
coEv {client} {e = Send , (BlockTxsOffer h sl)} (headC {stIdle}) _ ()
coEv {client} {e = Send , (Votes vs)} (headC {stIdle}) _ ()
coEv {client} {e = Send , Done} (headC {stIdle}) _ refl =
  _ , _ ,
  (∖√-ev (fire {r = client} (sVis {at = _ , apiLPev l d lnpSendDone} {a = tt} refl refl))
    (∖√-ev (fire {r = client} out-fire)
    (∖√-τ (back {r = client}) ∖√-refl)))
  , refl , headC
coEv {client} {e = Recv , RequestNext} (headC {stIdle}) _ ()
coEv {client} {e = Recv , (BlockAnnouncement x)} (headC {stIdle}) _ ()
coEv {client} {e = Recv , (BlockOffer h sl z)} (headC {stIdle}) _ ()
coEv {client} {e = Recv , (BlockTxsOffer h sl)} (headC {stIdle}) _ ()
coEv {client} {e = Recv , (Votes vs)} (headC {stIdle}) _ ()
coEv {client} {e = Recv , Done} (headC {stIdle}) _ ()
coEv {client} {e = Send , RequestNext} (headC {stBusy}) _ ()
coEv {client} {e = Send , (BlockAnnouncement x)} (headC {stBusy}) _ ()
coEv {client} {e = Send , (BlockOffer h sl z)} (headC {stBusy}) _ ()
coEv {client} {e = Send , (BlockTxsOffer h sl)} (headC {stBusy}) _ ()
coEv {client} {e = Send , (Votes vs)} (headC {stBusy}) _ ()
coEv {client} {e = Send , Done} (headC {stBusy}) _ ()
coEv {client} {e = Recv , RequestNext} (headC {stBusy}) _ ()
coEv {client} {e = Recv , (BlockAnnouncement x)} (headC {stBusy}) _ refl =
  _ , _ ,
  (∖√-ev (fire {r = client} (sVis {at = _ , receiveLNP l d} {a = tt , FromResponder , tt , leiosNotifyP (MsgLNPBlockAnnouncement (header tt))} refl refl))
    (∖√-ev (fire {r = client} out-fire)
    (∖√-τ (back {r = client}) ∖√-refl)))
  , refl , headC
coEv {client} {e = Recv , (BlockOffer h sl z)} (headC {stBusy}) _ refl =
  _ , _ ,
  (∖√-ev (fire {r = client} (sVis {at = _ , receiveLNP l d} {a = tt , FromResponder , tt , leiosNotifyP (MsgLNPBlockOffer (0 , 0) tt)} refl refl))
    (∖√-ev (fire {r = client} out-fire)
    (∖√-τ (back {r = client}) ∖√-refl)))
  , refl , headC
coEv {client} {e = Recv , (BlockTxsOffer h sl)} (headC {stBusy}) _ refl =
  _ , _ ,
  (∖√-ev (fire {r = client} (sVis {at = _ , receiveLNP l d} {a = tt , FromResponder , tt , leiosNotifyP (MsgLNPBlockTxsOffer (0 , 0))} refl refl))
    (∖√-ev (fire {r = client} out-fire)
    (∖√-τ (back {r = client}) ∖√-refl)))
  , refl , headC
coEv {client} {e = Recv , (Votes vs)} (headC {stBusy}) _ refl =
  _ , _ ,
  (∖√-ev (fire {r = client} (sVis {at = _ , receiveLNP l d} {a = tt , FromResponder , tt , leiosNotifyP (MsgLNPVotes [])} refl refl))
    (∖√-ev (fire {r = client} out-fire)
    (∖√-τ (back {r = client}) ∖√-refl)))
  , refl , headC
coEv {client} {e = Recv , Done} (headC {stBusy}) _ ()
coEv {client} {e = Send , RequestNext} (headC {stDone}) _ ()
coEv {client} {e = Send , (BlockAnnouncement x)} (headC {stDone}) _ ()
coEv {client} {e = Send , (BlockOffer h sl z)} (headC {stDone}) _ ()
coEv {client} {e = Send , (BlockTxsOffer h sl)} (headC {stDone}) _ ()
coEv {client} {e = Send , (Votes vs)} (headC {stDone}) _ ()
coEv {client} {e = Send , Done} (headC {stDone}) _ ()
coEv {client} {e = Recv , RequestNext} (headC {stDone}) _ ()
coEv {client} {e = Recv , (BlockAnnouncement x)} (headC {stDone}) _ ()
coEv {client} {e = Recv , (BlockOffer h sl z)} (headC {stDone}) _ ()
coEv {client} {e = Recv , (BlockTxsOffer h sl)} (headC {stDone}) _ ()
coEv {client} {e = Recv , (Votes vs)} (headC {stDone}) _ ()
coEv {client} {e = Recv , Done} (headC {stDone}) _ ()
coEv {server} {e = Send , RequestNext} (headC {stIdle}) _ ()
coEv {server} {e = Send , (BlockAnnouncement x)} (headC {stIdle}) _ ()
coEv {server} {e = Send , (BlockOffer h sl z)} (headC {stIdle}) _ ()
coEv {server} {e = Send , (BlockTxsOffer h sl)} (headC {stIdle}) _ ()
coEv {server} {e = Send , (Votes vs)} (headC {stIdle}) _ ()
coEv {server} {e = Send , Done} (headC {stIdle}) _ ()
coEv {server} {e = Recv , RequestNext} (headC {stIdle}) _ refl =
  _ , _ ,
  (∖√-ev (fire {r = server} (sVis {at = _ , receiveLNP l d} {a = tt , FromInitiator , tt , leiosNotifyP MsgLNPRequestNext} refl refl))
    (∖√-τ (back {r = server}) ∖√-refl))
  , refl , headC
coEv {server} {e = Recv , (BlockAnnouncement x)} (headC {stIdle}) _ ()
coEv {server} {e = Recv , (BlockOffer h sl z)} (headC {stIdle}) _ ()
coEv {server} {e = Recv , (BlockTxsOffer h sl)} (headC {stIdle}) _ ()
coEv {server} {e = Recv , (Votes vs)} (headC {stIdle}) _ ()
coEv {server} {e = Recv , Done} (headC {stIdle}) _ refl =
  _ , _ ,
  (∖√-ev (fire {r = server} (sVis {at = _ , receiveLNP l d} {a = tt , FromInitiator , tt , leiosNotifyP MsgLNPDone} refl refl))
    (∖√-ev (fire {r = server} (pfx-fire {a = tt}))
    (∖√-τ (back {r = server}) ∖√-refl)))
  , refl , headC
coEv {server} {e = Send , RequestNext} (headC {stBusy}) _ ()
coEv {server} {e = Send , (BlockAnnouncement x)} (headC {stBusy}) _ refl =
  _ , _ ,
  (∖√-ev (fire {r = server} (sVis {at = _ , apiLPev l d lnpSendBlockAnnouncement} {a = header tt} refl refl))
    (∖√-ev (fire {r = server} out-fire)
    (∖√-τ (back {r = server}) ∖√-refl)))
  , refl , headC
coEv {server} {e = Send , (BlockOffer h sl z)} (headC {stBusy}) _ refl =
  _ , _ ,
  (∖√-ev (fire {r = server} (sVis {at = _ , apiLPev l d lnpSendBlockOffer} {a = (0 , 0) , tt} refl refl))
    (∖√-ev (fire {r = server} out-fire)
    (∖√-τ (back {r = server}) ∖√-refl)))
  , refl , headC
coEv {server} {e = Send , (BlockTxsOffer h sl)} (headC {stBusy}) _ refl =
  _ , _ ,
  (∖√-ev (fire {r = server} (sVis {at = _ , apiLPev l d lnpSendBlockTxsOffer} {a = 0 , 0} refl refl))
    (∖√-ev (fire {r = server} out-fire)
    (∖√-τ (back {r = server}) ∖√-refl)))
  , refl , headC
coEv {server} {e = Send , (Votes vs)} (headC {stBusy}) _ refl =
  _ , _ ,
  (∖√-ev (fire {r = server} (sVis {at = _ , apiLPev l d lnpSendVotes} {a = []} refl refl))
    (∖√-ev (fire {r = server} out-fire)
    (∖√-τ (back {r = server}) ∖√-refl)))
  , refl , headC
coEv {server} {e = Send , Done} (headC {stBusy}) _ ()
coEv {server} {e = Recv , RequestNext} (headC {stBusy}) _ ()
coEv {server} {e = Recv , (BlockAnnouncement x)} (headC {stBusy}) _ ()
coEv {server} {e = Recv , (BlockOffer h sl z)} (headC {stBusy}) _ ()
coEv {server} {e = Recv , (BlockTxsOffer h sl)} (headC {stBusy}) _ ()
coEv {server} {e = Recv , (Votes vs)} (headC {stBusy}) _ ()
coEv {server} {e = Recv , Done} (headC {stBusy}) _ ()
coEv {server} {e = Send , RequestNext} (headC {stDone}) _ ()
coEv {server} {e = Send , (BlockAnnouncement x)} (headC {stDone}) _ ()
coEv {server} {e = Send , (BlockOffer h sl z)} (headC {stDone}) _ ()
coEv {server} {e = Send , (BlockTxsOffer h sl)} (headC {stDone}) _ ()
coEv {server} {e = Send , (Votes vs)} (headC {stDone}) _ ()
coEv {server} {e = Send , Done} (headC {stDone}) _ ()
coEv {server} {e = Recv , RequestNext} (headC {stDone}) _ ()
coEv {server} {e = Recv , (BlockAnnouncement x)} (headC {stDone}) _ ()
coEv {server} {e = Recv , (BlockOffer h sl z)} (headC {stDone}) _ ()
coEv {server} {e = Recv , (BlockTxsOffer h sl)} (headC {stDone}) _ ()
coEv {server} {e = Recv , (Votes vs)} (headC {stDone}) _ ()
coEv {server} {e = Recv , Done} (headC {stDone}) _ ()

-- The local API can supply/deliver the canonical payloads, with no event premise.
cosimulation : (r : Role) → Br.CoSim (Spec.leiosNotify r) cls forget (CoRel r) (λ _ → ⊤)
cosimulation r = record { co-τ = coTau ; co-ev = coEv }

-- Every accepted trace is observed on the original standalone peer at this abstraction.
complete : ∀ r {es} → Spec.HasTrace r idle es →
           ∃[ t ] ∃[ M ] (It r (step r stIdle) ⟹∖√⟨ t ⟩ M × Obs t es)
complete r {es} (_ , run) with Br.complete (Spec.leiosNotify r) cls forget (cosimulation r) headC (universal (λ _ → tt) es) run
... | M , t , p , o , _ = t , M , p , o

-- Both directions relate the checker to the existing client and server, not new transcriptions.
bridge : ∀ r {es} → Spec.HasTrace r idle es ⇔
         (∃[ t ] ∃[ M ] (It r (step r stIdle) ⟹∖√⟨ t ⟩ M × Obs t es))
bridge r = mk⇔ (complete r) (λ { (t , M , p , o) → sound r p o })

-- The client endpoint spells out the existing peer definition.
client-bridge : ∀ {es} → Spec.HasTrace client idle es ⇔
  (∃[ t ] ∃[ M ] (LNPclientStClient l d ⟹∖√⟨ t ⟩ M × Obs t es))
client-bridge = bridge client

-- The server endpoint spells out the existing peer definition.
server-bridge : ∀ {es} → Spec.HasTrace server idle es ⇔
  (∃[ t ] ∃[ M ] (LNPserverStClient l d ⟹∖√⟨ t ⟩ M × Obs t es))
server-bridge = bridge server
