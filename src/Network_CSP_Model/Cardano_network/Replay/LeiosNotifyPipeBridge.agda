{-# OPTIONS --guardedness #-}

-- General kind-level wire correspondence for the new bounded native Notify peers.
open import Cardano_network.Params using (Params)
open import Data.Nat using (ℕ)
open import Cardano_network.Base using (Dir)
import Cardano_network.Net
module Cardano_network.Replay.LeiosNotifyPipeBridge
  (p : Params) (k : ℕ) (l : Cardano_network.Net.Link p) (d : Dir) where

open import Data.Nat using (suc; _<ᵇ_)
open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (universal)
open import Data.Maybe.Properties using (just-injective)
open import Data.List.Properties using (∷-injective)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Process_Trees using (ExtI)
open import Cardano_network.Base using (FromInitiator; FromResponder)
open import Cardano_network.Data p
open import Cardano_network.Net p
open import Cardano_network.LeiosNotifyP p using (LNPEv; sendLNP; receiveLNP; apiLPev; doneLNP)
open import Cardano_network.LeiosNotifyPipe p
open Machine k l d
open import Cardano_network.Replay.LeiosNotifyPipeParts p k l d
import Cardano_network.Replay.LeiosNotifyPipeline as N
import Cardano_network.Replay.LeiosNotifySession as Log
import Semantics.LTS {E = LNPEv} {I = ExtI LNPEv} as LTS
open import Semantics.Deadlock {E = LNPEv} {I = ExtI LNPEv}
  using (_⟹∖√⟨_⟩_; ∖√-refl; ∖√-τ; ∖√-ev)
import Semantics.Replay.Bridge {E = LNPEv} {I = ExtI LNPEv} as Br

-- Native peer agency agrees with the existing replay roles.
role : Peer → N.Role
role consumer = N.client
role producer = N.server

-- The credit-state correspondence preserves the counter and closure exactly.
ctl : State → N.St
ctl (openN n) = N.openN n
ctl closed = N.closed

-- Only the six native message kinds are observed at this bridge boundary.
kind : MessageLeiosNotifyP → N.Kind
kind MsgLNPRequestNext = N.request
kind (MsgLNPBlockAnnouncement _) = N.announcement
kind (MsgLNPBlockOffer _ _) = N.offer
kind (MsgLNPBlockTxsOffer _) = N.txsOffer
kind (MsgLNPVotes _) = N.votes
kind MsgLNPDone = N.doneK

-- Log representatives carry no payload assertion in this control-level bridge.
canonical : MessageLeiosNotifyP → N.Msg
canonical MsgLNPRequestNext = Log.RequestNext
canonical (MsgLNPBlockAnnouncement _) = Log.BlockAnnouncement nothing
canonical (MsgLNPBlockOffer _ _) = Log.BlockOffer 0 0 0
canonical (MsgLNPBlockTxsOffer _) = Log.BlockTxsOffer 0 0
canonical (MsgLNPVotes _) = Log.Votes []
canonical MsgLNPDone = Log.Done

-- Canonical log values retain precisely the native message kind.
canonical-kind : ∀ m → Log.kind (canonical m) ≡ kind m
canonical-kind MsgLNPRequestNext = refl
canonical-kind (MsgLNPBlockAnnouncement _) = refl
canonical-kind (MsgLNPBlockOffer _ _) = refl
canonical-kind (MsgLNPBlockTxsOffer _) = refl
canonical-kind (MsgLNPVotes _) = refl
canonical-kind MsgLNPDone = refl

-- Wire directions are observed; native API delivery and local done are erased.
classify : LTS.Event → Maybe N.Observed
classify (LTS.evLabel _ (sendLNP _ _) (_ , _ , _ , leiosNotifyP m)) = just (N.Send , kind m)
classify (LTS.evLabel _ (receiveLNP _ _) (_ , _ , _ , leiosNotifyP m)) = just (N.Recv , kind m)
classify _ = nothing

-- Match the existing replay observation contract without pretending payload equality.
Obs : List LTS.Event → List N.E → Set
Obs = Br.Obs classify N.forget

-- Request capacity is tested in the native and replay machines by the same predicate.
request-client : ∀ {n} → (n <ᵇ k) ≡ true →
  N.Spec.Step k N.client (N.openN n) (N.Send , Log.RequestNext) (N.openN (suc n))
request-client credit rewrite credit = refl

-- Producer request reception uses the same bound and credit increment.
request-server : ∀ {n} → (n <ᵇ k) ≡ true →
  N.Spec.Step k N.server (N.openN n) (N.Recv , Log.RequestNext) (N.openN (suc n))
request-server credit rewrite credit = refl

-- A native pending output is related to the state before its visible send.
data PhaseRel (r : Peer) : Phase → N.St → Set where
  ready : ∀ {s} → PhaseRel r (head s) (ctl s)
  looping : ∀ {s} → PhaseRel r (loopBack s) (ctl s)
  output : ∀ {md m s q} → N.Spec.Step k (role r) q (N.Send , canonical m) (ctl s) →
    PhaseRel r (sending md m s) q
  delivery : ∀ {m s} → PhaseRel r (delivering m s) (ctl s)
  notice : PhaseRel r doneNotice N.closed

-- Wrap the exact native phase rather than relying on coinductive record equality.
data Rel (r : Peer) : Proc → N.St → Set₁ where
  at : ∀ {s q} → PhaseRel r s q → Rel r (tree r s) q

-- One successful replay transition produces its singleton visible trace.
one : ∀ {r s e t} → N.Spec.Step k (role r) s e t → N.Spec._⇒⟨_⟩_ k (role r) s (e ∷ []) t
one {r} pr = N.Spec.vis {depth = k} {role = role r} pr (N.Spec.done {depth = k} {role = role r})

-- Every native phase rule preserves the credit relation and wire observation.
progress : ∀ {r s q e t} → PhaseRel r s q → Step r s e t →
  Σ[ es ∈ List N.E ] Σ[ q′ ∈ N.St ]
    (Obs (e ∷ []) es × N.Spec._⇒⟨_⟩_ k (role r) q es q′ × PhaseRel r t q′)
progress ready (cRequest credit) = [] , _ , refl , N.Spec.done {depth = k} {role = N.client} , output (request-client credit)
progress ready cDone = [] , _ , refl , N.Spec.done {depth = k} {role = N.client} , output refl
progress ready (cNotification (announcement h)) = (N.Recv , Log.BlockAnnouncement nothing) ∷ [] , _ ,
  refl , one {r = consumer} refl , delivery
progress ready (cNotification (offer pt sz)) = (N.Recv , Log.BlockOffer 0 0 0) ∷ [] , _ ,
  refl , one {r = consumer} refl , delivery
progress ready (cNotification (txsOffer pt)) = (N.Recv , Log.BlockTxsOffer 0 0) ∷ [] , _ ,
  refl , one {r = consumer} refl , delivery
progress ready (cNotification (votes vs)) = (N.Recv , Log.Votes []) ∷ [] , _ ,
  refl , one {r = consumer} refl , delivery
progress ready (sRequest credit) = (N.Recv , Log.RequestNext) ∷ [] , _ , refl ,
  one {r = producer} (request-server credit) , looping
progress ready sDone = (N.Recv , Log.Done) ∷ [] , _ , refl , one {r = producer} refl , notice
progress ready sAnnouncement = [] , _ , refl , N.Spec.done {depth = k} {role = N.server} , output refl
progress ready sOffer = [] , _ , refl , N.Spec.done {depth = k} {role = N.server} , output refl
progress ready sTxsOffer = [] , _ , refl , N.Spec.done {depth = k} {role = N.server} , output refl
progress ready sVotes = [] , _ , refl , N.Spec.done {depth = k} {role = N.server} , output refl
progress {r} (output {m = m} pr) sent = (N.Send , canonical m) ∷ [] , _ ,
  cong (λ kk → (N.Send , kk) ∷ []) (sym (canonical-kind m)) , one {r = r} pr , looping
progress {r} delivery delivered = [] , _ , refl , N.Spec.done {depth = k} {role = role r} , looping
progress {r} notice noticed = [] , _ , refl , N.Spec.done {depth = k} {role = role r} , looping

-- Actual PTree visible steps invert to the certified native phase rules.
simEv : ∀ {r T T′ q e} → Rel r T q → T LTS.─[ LTS.ev (LTS.evl e) ]─► T′ →
  Σ[ es ∈ List N.E ] Σ[ q′ ∈ N.St ]
    (Obs (e ∷ []) es × N.Spec._⇒⟨_⟩_ k (role r) q es q′ × Rel r T′ q′)
simEv (at rel) st with visible-inv st
... | phase , rule , refl with progress rel rule
...   | es , q′ , obs , run , rel′ = es , q′ , obs , run , at rel′

-- Loop-back moves preserve the exact abstract credit count.
simTau : ∀ {r T T′ q} → Rel r T q → T LTS.─[ LTS.τ ]─► T′ →
  Σ[ q′ ∈ N.St ] (N.Spec._⇒⟨_⟩_ k (role r) q [] q′ × Rel r T′ q′)
simTau {r} (at rel) st with tau-inv st
... | phase , back , refl with rel
...   | looping = _ , N.Spec.done {depth = k} {role = role r} , at ready

-- Every reachable native residual is simulated by the existing bounded replay model.
simulation : ∀ r → Br.Sim (N.Spec.leiosNotify k (role r)) classify N.forget (Rel r)
simulation r = record { sim-τ = simTau ; sim-ev = simEv }

-- Replace arbitrary log payloads only when all retained control observations agree.
transport : ∀ {r s t es fs} → map N.forget es ≡ map N.forget fs →
  N.Spec._⇒⟨_⟩_ k (role r) s es t → N.Spec._⇒⟨_⟩_ k (role r) s fs t
transport {r} {fs = []} refl N.Spec.done = N.Spec.done {depth = k} {role = role r}
transport {fs = _ ∷ _} () N.Spec.done
transport _ (N.Spec.tau () _)
transport {fs = []} () (N.Spec.vis _ _)
transport {r} {s} {fs = f ∷ fs} eq (N.Spec.vis st run) = N.Spec.vis {depth = k} {role = role r}
  (trans (cong (N.nextKind k (role r) s) (sym (proj₁ (∷-injective eq)))) st)
  (transport {r = r} (proj₂ (∷-injective eq)) run)

-- Soundness is general in Params, depth and endpoint and needs no payload inhabitant.
sound : ∀ r {events T es} → tree r (head (openN 0)) ⟹∖√⟨ events ⟩ T → Obs events es →
  N.Spec.HasTrace k (role r) N.idle es
sound r run obs with Br.sound (N.Spec.leiosNotify k (role r)) classify N.forget
  (simulation r) (at ready) run
... | es′ , q , obs′ , specRun , _ = q , transport {r = r} (trans (sym obs′) obs) specRun

-- Completeness needs native payload witnesses for nonempty opaque domains.
-- Votes can use the empty list, so no VoteBlob inhabitant is required.
record Payloads : Set where
  constructor payloads
  field
    announcementHeader : Header
    offerPoint : Params.EBHash p × Params.LSlot p
    offerSize : Params.Size p
open Payloads public

-- Every co-simulation boundary is an actual native menu head.
data CoRel (r : Peer) : Proc → N.St → Set₁ where
  headC : ∀ {s} → CoRel r (tree r (head s)) (ctl s)

-- The replay credit model has no silent transitions to realize.
coTau : ∀ {r T q q′} → CoRel r T q → ⊥ →
  ∃[ T′ ] ∃[ events ] (T ⟹∖√⟨ events ⟩ T′ × Obs events [] × CoRel r T′ q′)
coTau _ ()

-- An API-selected message is sent unchanged before the native loop-back.
send-run : ∀ {r s md m t e} → Step r (head s) e (sending md m t) →
  tree r (head s) ⟹∖√⟨ e ∷ LTS.evLabel _ (sendLNP l d) (packet md m) ∷ [] ⟩ tree r (head t)
send-run st = ∖√-ev (fire st) (∖√-ev (fire sent) (∖√-τ (tau-fire back) ∖√-refl))

-- Receiving a notification forwards its exact native payload, then returns to the menu.
delivery-run : ∀ n m → tree consumer (head (openN (suc n))) ⟹∖√⟨
  LTS.evLabel _ (receiveLNP l d) (packet FromResponder (message m)) ∷
  LTS.evLabel _ (apiLPev l d (tag m)) (value m) ∷ [] ⟩
  tree consumer (head (openN n))
delivery-run n m = ∖√-ev (fire (cNotification m))
  (∖√-ev (fire delivered) (∖√-τ (tau-fire back) ∖√-refl))

-- A producer receives one more request credit before returning to its menu.
request-run : ∀ {n} → (n <ᵇ k) ≡ true → tree producer (head (openN n)) ⟹∖√⟨
  LTS.evLabel _ (receiveLNP l d) (packet FromInitiator MsgLNPRequestNext) ∷ [] ⟩
  tree producer (head (openN (suc n)))
request-run credit = ∖√-ev (fire (sRequest credit)) (∖√-τ (tau-fire back) ∖√-refl)

-- Producer closure retains the original peer-local done notification.
done-run : tree producer (head (openN 0)) ⟹∖√⟨
  LTS.evLabel _ (receiveLNP l d) (packet FromInitiator MsgLNPDone) ∷
  LTS.evLabel _ (doneLNP l d) tt ∷ [] ⟩
  tree producer (head closed)
done-run = ∖√-ev (fire sDone) (∖√-ev (fire noticed) (∖√-τ (tau-fire back) ∖√-refl))

-- A successful bounded issue exposes the guard and the unique target credit count.
issue-inv : ∀ n {q} → N.issue k n ≡ just q → (n <ᵇ k) ≡ true × q ≡ N.openN (suc n)
issue-inv n pr with n <ᵇ k
... | false with () ← pr
... | true = refl , sym (just-injective pr)

-- Realize every replay wire event using native API, wire and silent transitions.
coEv : ∀ (w : Payloads) {r T q q′ e} → CoRel r T q → ⊤ → N.Spec.Step k (role r) q e q′ →
  ∃[ T′ ] ∃[ events ] (T ⟹∖√⟨ events ⟩ T′ × Obs events (e ∷ []) × CoRel r T′ q′)
coEv w {consumer} {e = N.Send , Log.RequestNext} (headC {openN n}) _ pr with issue-inv n pr
... | credit , refl = _ , _ , send-run (cRequest credit) , refl , headC
coEv w {consumer} {e = N.Send , Log.Done} (headC {openN 0}) _ refl =
  _ , _ , send-run cDone , refl , headC
coEv w {consumer} {e = N.Send , Log.Done} (headC {openN (suc n)}) _ ()
coEv w {producer} {e = N.Recv , Log.RequestNext} (headC {openN n}) _ pr with issue-inv n pr
... | credit , refl = _ , _ , request-run credit , refl , headC
coEv w {producer} {e = N.Recv , Log.Done} (headC {openN 0}) _ refl =
  _ , _ , done-run , refl , headC
coEv w {producer} {e = N.Recv , Log.Done} (headC {openN (suc n)}) _ ()
coEv w {consumer} {e = N.Recv , (Log.BlockAnnouncement x)} (headC {openN 0}) _ ()
coEv w {consumer} {e = N.Recv , (Log.BlockAnnouncement x)} (headC {openN (suc n)}) _ refl =
  _ , _ , delivery-run n (announcement (announcementHeader w)) , refl , headC
coEv w {consumer} {e = N.Recv , (Log.BlockOffer h sl z)} (headC {openN 0}) _ ()
coEv w {consumer} {e = N.Recv , (Log.BlockOffer h sl z)} (headC {openN (suc n)}) _ refl =
  _ , _ , delivery-run n (offer (offerPoint w) (offerSize w)) , refl , headC
coEv w {consumer} {e = N.Recv , (Log.BlockTxsOffer h sl)} (headC {openN 0}) _ ()
coEv w {consumer} {e = N.Recv , (Log.BlockTxsOffer h sl)} (headC {openN (suc n)}) _ refl =
  _ , _ , delivery-run n (txsOffer (offerPoint w)) , refl , headC
coEv w {consumer} {e = N.Recv , (Log.Votes vs)} (headC {openN 0}) _ ()
coEv w {consumer} {e = N.Recv , (Log.Votes vs)} (headC {openN (suc n)}) _ refl =
  _ , _ , delivery-run n (votes []) , refl , headC
coEv w {producer} {e = N.Send , (Log.BlockAnnouncement x)} (headC {openN 0}) _ ()
coEv w {producer} {e = N.Send , (Log.BlockAnnouncement x)} (headC {openN (suc n)}) _ refl =
  _ , _ , send-run (sAnnouncement {h = announcementHeader w}) , refl , headC
coEv w {producer} {e = N.Send , (Log.BlockOffer h sl z)} (headC {openN 0}) _ ()
coEv w {producer} {e = N.Send , (Log.BlockOffer h sl z)} (headC {openN (suc n)}) _ refl =
  _ , _ , send-run (sOffer {pt = offerPoint w} {sz = offerSize w}) , refl , headC
coEv w {producer} {e = N.Send , (Log.BlockTxsOffer h sl)} (headC {openN 0}) _ ()
coEv w {producer} {e = N.Send , (Log.BlockTxsOffer h sl)} (headC {openN (suc n)}) _ refl =
  _ , _ , send-run (sTxsOffer {pt = offerPoint w}) , refl , headC
coEv w {producer} {e = N.Send , (Log.Votes vs)} (headC {openN 0}) _ ()
coEv w {producer} {e = N.Send , (Log.Votes vs)} (headC {openN (suc n)}) _ refl =
  _ , _ , send-run (sVotes {vs = []}) , refl , headC
coEv w {consumer} {e = N.Recv , Log.RequestNext} (headC {openN 0}) _ ()
coEv w {consumer} {e = N.Recv , Log.RequestNext} (headC {openN (suc n)}) _ ()
coEv w {consumer} {e = N.Recv , Log.Done} (headC {openN 0}) _ ()
coEv w {consumer} {e = N.Recv , Log.Done} (headC {openN (suc n)}) _ ()
coEv w {producer} {e = N.Send , Log.RequestNext} (headC {openN 0}) _ ()
coEv w {producer} {e = N.Send , Log.RequestNext} (headC {openN (suc n)}) _ ()
coEv w {producer} {e = N.Send , Log.Done} (headC {openN 0}) _ ()
coEv w {producer} {e = N.Send , Log.Done} (headC {openN (suc n)}) _ ()
coEv w {consumer} {e = N.Send , (Log.BlockAnnouncement x)} (headC {openN 0}) _ ()
coEv w {consumer} {e = N.Send , (Log.BlockAnnouncement x)} (headC {openN (suc n)}) _ ()
coEv w {consumer} {e = N.Send , (Log.BlockOffer h sl z)} (headC {openN 0}) _ ()
coEv w {consumer} {e = N.Send , (Log.BlockOffer h sl z)} (headC {openN (suc n)}) _ ()
coEv w {consumer} {e = N.Send , (Log.BlockTxsOffer h sl)} (headC {openN 0}) _ ()
coEv w {consumer} {e = N.Send , (Log.BlockTxsOffer h sl)} (headC {openN (suc n)}) _ ()
coEv w {consumer} {e = N.Send , (Log.Votes vs)} (headC {openN 0}) _ ()
coEv w {consumer} {e = N.Send , (Log.Votes vs)} (headC {openN (suc n)}) _ ()
coEv w {producer} {e = N.Recv , (Log.BlockAnnouncement x)} (headC {openN 0}) _ ()
coEv w {producer} {e = N.Recv , (Log.BlockAnnouncement x)} (headC {openN (suc n)}) _ ()
coEv w {producer} {e = N.Recv , (Log.BlockOffer h sl z)} (headC {openN 0}) _ ()
coEv w {producer} {e = N.Recv , (Log.BlockOffer h sl z)} (headC {openN (suc n)}) _ ()
coEv w {producer} {e = N.Recv , (Log.BlockTxsOffer h sl)} (headC {openN 0}) _ ()
coEv w {producer} {e = N.Recv , (Log.BlockTxsOffer h sl)} (headC {openN (suc n)}) _ ()
coEv w {producer} {e = N.Recv , (Log.Votes vs)} (headC {openN 0}) _ ()
coEv w {producer} {e = N.Recv , (Log.Votes vs)} (headC {openN (suc n)}) _ ()
coEv w {consumer} (headC {closed}) _ ()
coEv w {producer} (headC {closed}) _ ()

-- The explicit payload witnesses discharge every opaque-domain completeness premise.
cosimulation : ∀ w r → Br.CoSim (N.Spec.leiosNotify k (role r)) classify N.forget (CoRel r) (λ _ → ⊤)
cosimulation w r = record { co-τ = coTau ; co-ev = coEv w }

-- Every locally accepted control trace has one native pipelined peer execution.
complete : ∀ w r {es} → N.Spec.HasTrace k (role r) N.idle es →
  ∃[ events ] ∃[ T ] (tree r (head (openN 0)) ⟹∖√⟨ events ⟩ T × Obs events es)
complete w r {es} (_ , run) with Br.complete (N.Spec.leiosNotify k (role r)) classify N.forget
  (cosimulation w r) headC (universal (λ _ → tt) es) run
... | T , events , native , obs , _ = events , T , native , obs

-- General finite wire-control equivalence for both roles and every capacity.
bridge : ∀ w r {es} → N.Spec.HasTrace k (role r) N.idle es ⇔
  (∃[ events ] ∃[ T ] (tree r (head (openN 0)) ⟹∖√⟨ events ⟩ T × Obs events es))
bridge w r = mk⇔ (complete w r) (λ { (events , T , run , obs) → sound r run obs })

-- The consumer endpoint names the public bounded native peer definition.
client-bridge : ∀ w {es} → N.Spec.HasTrace k N.client N.idle es ⇔
  (∃[ events ] ∃[ T ] (client k l d ⟹∖√⟨ events ⟩ T × Obs events es))
client-bridge w = bridge w consumer

-- The producer endpoint names the public bounded native peer definition.
server-bridge : ∀ w {es} → N.Spec.HasTrace k N.server N.idle es ⇔
  (∃[ events ] ∃[ T ] (server k l d ⟹∖√⟨ events ⟩ T × Obs events es))
server-bridge w = bridge w producer
