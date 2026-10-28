{-# OPTIONS --guardedness #-}

-- Exact retained-field local bridge for native peers at summary-preserving parameters.
open import Cardano_network.Replay.LeiosNotifyExactParams renaming (exactParams to p)
open import Data.Nat using (ℕ)
open import Cardano_network.Base using (Dir)
import Cardano_network.Net
module Cardano_network.Replay.LeiosNotifyExactLocal
  (k : ℕ) (l : Cardano_network.Net.Link p) (d : Dir) where

open import Data.Nat using (suc; _<ᵇ_)
open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (universal)
open import Data.Maybe.Properties using (just-injective)
open import Data.List.Properties using (∷-injective; map-id)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Function using (id)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
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

open import Cardano_network.Replay.LeiosNotifyExactObservation public

-- The identity observation equates all parsed fields, rather than only kinds.
Obs : List LTS.Event → List N.E → Set
Obs = Br.Obs classify id

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
progress ready (cNotification (announcement h)) = (N.Recv , Log.BlockAnnouncement (headerSummary h)) ∷ [] , _ ,
  refl , one {r = consumer} refl , delivery
progress ready (cNotification (offer (h , sl) sz)) = (N.Recv , Log.BlockOffer h sl sz) ∷ [] , _ ,
  refl , one {r = consumer} refl , delivery
progress ready (cNotification (txsOffer (h , sl))) = (N.Recv , Log.BlockTxsOffer h sl) ∷ [] , _ ,
  refl , one {r = consumer} refl , delivery
progress ready (cNotification (votes vs)) = (N.Recv , Log.Votes vs) ∷ [] , _ ,
  refl , one {r = consumer} refl , delivery
progress ready (sRequest credit) = (N.Recv , Log.RequestNext) ∷ [] , _ , refl ,
  one {r = producer} (request-server credit) , looping
progress ready sDone = (N.Recv , Log.Done) ∷ [] , _ , refl , one {r = producer} refl , notice
progress ready sAnnouncement = [] , _ , refl , N.Spec.done {depth = k} {role = N.server} , output refl
progress ready sOffer = [] , _ , refl , N.Spec.done {depth = k} {role = N.server} , output refl
progress ready sTxsOffer = [] , _ , refl , N.Spec.done {depth = k} {role = N.server} , output refl
progress ready sVotes = [] , _ , refl , N.Spec.done {depth = k} {role = N.server} , output refl
progress {r} (output {m = m} pr) sent = (N.Send , canonical m) ∷ [] , _ ,
  refl , one {r = r} pr , looping
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
simulation : ∀ r → Br.Sim (N.Spec.leiosNotify k (role r)) classify id (Rel r)
simulation r = record { sim-τ = simTau ; sim-ev = simEv }

-- Exact observation equality transports the produced replay run to the input rows.
sound : ∀ r {events T es} → tree r (head (openN 0)) ⟹∖√⟨ events ⟩ T → Obs events es →
  N.Spec.HasTrace k (role r) N.idle es
sound r run obs with Br.sound (N.Spec.leiosNotify k (role r)) classify id
  (simulation r) (at ready) run
... | es′ , q , obs′ , specRun , _ = q , subst
  (λ fs → N.Spec._⇒⟨_⟩_ k (role r) N.idle fs q)
  (trans (sym (map-id es′)) (trans (sym obs′) (trans obs (map-id _)))) specRun

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
coEv : ∀ {r T q q′ e} → CoRel r T q → ⊤ → N.Spec.Step k (role r) q e q′ →
  ∃[ T′ ] ∃[ events ] (T ⟹∖√⟨ events ⟩ T′ × Obs events (e ∷ []) × CoRel r T′ q′)
coEv {consumer} {e = N.Send , Log.RequestNext} (headC {openN n}) _ pr with issue-inv n pr
... | credit , refl = _ , _ , send-run (cRequest credit) , refl , headC
coEv {consumer} {e = N.Send , Log.Done} (headC {openN 0}) _ refl =
  _ , _ , send-run cDone , refl , headC
coEv {consumer} {e = N.Send , Log.Done} (headC {openN (suc n)}) _ ()
coEv {producer} {e = N.Recv , Log.RequestNext} (headC {openN n}) _ pr with issue-inv n pr
... | credit , refl = _ , _ , request-run credit , refl , headC
coEv {producer} {e = N.Recv , Log.Done} (headC {openN 0}) _ refl =
  _ , _ , done-run , refl , headC
coEv {producer} {e = N.Recv , Log.Done} (headC {openN (suc n)}) _ ()
coEv {consumer} {e = N.Recv , (Log.BlockAnnouncement x)} (headC {openN 0}) _ ()
coEv {consumer} {e = N.Recv , (Log.BlockAnnouncement x)} (headC {openN (suc n)}) _ refl =
  _ , _ , delivery-run n (announcement (header x)) , refl , headC
coEv {consumer} {e = N.Recv , (Log.BlockOffer h sl z)} (headC {openN 0}) _ ()
coEv {consumer} {e = N.Recv , (Log.BlockOffer h sl z)} (headC {openN (suc n)}) _ refl =
  _ , _ , delivery-run n (offer (h , sl) z) , refl , headC
coEv {consumer} {e = N.Recv , (Log.BlockTxsOffer h sl)} (headC {openN 0}) _ ()
coEv {consumer} {e = N.Recv , (Log.BlockTxsOffer h sl)} (headC {openN (suc n)}) _ refl =
  _ , _ , delivery-run n (txsOffer (h , sl)) , refl , headC
coEv {consumer} {e = N.Recv , (Log.Votes vs)} (headC {openN 0}) _ ()
coEv {consumer} {e = N.Recv , (Log.Votes vs)} (headC {openN (suc n)}) _ refl =
  _ , _ , delivery-run n (votes vs) , refl , headC
coEv {producer} {e = N.Send , (Log.BlockAnnouncement x)} (headC {openN 0}) _ ()
coEv {producer} {e = N.Send , (Log.BlockAnnouncement x)} (headC {openN (suc n)}) _ refl =
  _ , _ , send-run (sAnnouncement {h = header x}) , refl , headC
coEv {producer} {e = N.Send , (Log.BlockOffer h sl z)} (headC {openN 0}) _ ()
coEv {producer} {e = N.Send , (Log.BlockOffer h sl z)} (headC {openN (suc n)}) _ refl =
  _ , _ , send-run (sOffer {pt = h , sl} {sz = z}) , refl , headC
coEv {producer} {e = N.Send , (Log.BlockTxsOffer h sl)} (headC {openN 0}) _ ()
coEv {producer} {e = N.Send , (Log.BlockTxsOffer h sl)} (headC {openN (suc n)}) _ refl =
  _ , _ , send-run (sTxsOffer {pt = h , sl}) , refl , headC
coEv {producer} {e = N.Send , (Log.Votes vs)} (headC {openN 0}) _ ()
coEv {producer} {e = N.Send , (Log.Votes vs)} (headC {openN (suc n)}) _ refl =
  _ , _ , send-run (sVotes {vs = vs}) , refl , headC
coEv {consumer} {e = N.Recv , Log.RequestNext} (headC {openN 0}) _ ()
coEv {consumer} {e = N.Recv , Log.RequestNext} (headC {openN (suc n)}) _ ()
coEv {consumer} {e = N.Recv , Log.Done} (headC {openN 0}) _ ()
coEv {consumer} {e = N.Recv , Log.Done} (headC {openN (suc n)}) _ ()
coEv {producer} {e = N.Send , Log.RequestNext} (headC {openN 0}) _ ()
coEv {producer} {e = N.Send , Log.RequestNext} (headC {openN (suc n)}) _ ()
coEv {producer} {e = N.Send , Log.Done} (headC {openN 0}) _ ()
coEv {producer} {e = N.Send , Log.Done} (headC {openN (suc n)}) _ ()
coEv {consumer} {e = N.Send , (Log.BlockAnnouncement x)} (headC {openN 0}) _ ()
coEv {consumer} {e = N.Send , (Log.BlockAnnouncement x)} (headC {openN (suc n)}) _ ()
coEv {consumer} {e = N.Send , (Log.BlockOffer h sl z)} (headC {openN 0}) _ ()
coEv {consumer} {e = N.Send , (Log.BlockOffer h sl z)} (headC {openN (suc n)}) _ ()
coEv {consumer} {e = N.Send , (Log.BlockTxsOffer h sl)} (headC {openN 0}) _ ()
coEv {consumer} {e = N.Send , (Log.BlockTxsOffer h sl)} (headC {openN (suc n)}) _ ()
coEv {consumer} {e = N.Send , (Log.Votes vs)} (headC {openN 0}) _ ()
coEv {consumer} {e = N.Send , (Log.Votes vs)} (headC {openN (suc n)}) _ ()
coEv {producer} {e = N.Recv , (Log.BlockAnnouncement x)} (headC {openN 0}) _ ()
coEv {producer} {e = N.Recv , (Log.BlockAnnouncement x)} (headC {openN (suc n)}) _ ()
coEv {producer} {e = N.Recv , (Log.BlockOffer h sl z)} (headC {openN 0}) _ ()
coEv {producer} {e = N.Recv , (Log.BlockOffer h sl z)} (headC {openN (suc n)}) _ ()
coEv {producer} {e = N.Recv , (Log.BlockTxsOffer h sl)} (headC {openN 0}) _ ()
coEv {producer} {e = N.Recv , (Log.BlockTxsOffer h sl)} (headC {openN (suc n)}) _ ()
coEv {producer} {e = N.Recv , (Log.Votes vs)} (headC {openN 0}) _ ()
coEv {producer} {e = N.Recv , (Log.Votes vs)} (headC {openN (suc n)}) _ ()
coEv {consumer} (headC {closed}) _ ()
coEv {producer} (headC {closed}) _ ()

-- The summary carriers provide witnesses for every normalized event.
cosimulation : ∀ r → Br.CoSim (N.Spec.leiosNotify k (role r)) classify id (CoRel r) (λ _ → ⊤)
cosimulation r = record { co-τ = coTau ; co-ev = coEv }

-- Every locally accepted exact-field trace has one native peer execution.
complete : ∀ r {es} → N.Spec.HasTrace k (role r) N.idle es →
  ∃[ events ] ∃[ T ] (tree r (head (openN 0)) ⟹∖√⟨ events ⟩ T × Obs events es)
complete r {es} (_ , run) with Br.complete (N.Spec.leiosNotify k (role r)) classify id
  (cosimulation r) headC (universal (λ _ → tt) es) run
... | T , events , native , obs , _ = events , T , native , obs

-- Exact finite summary-field equivalence for both roles and every capacity.
bridge : ∀ r {es} → N.Spec.HasTrace k (role r) N.idle es ⇔
  (∃[ events ] ∃[ T ] (tree r (head (openN 0)) ⟹∖√⟨ events ⟩ T × Obs events es))
bridge r = mk⇔ (complete r) (λ { (events , T , run , obs) → sound r run obs })

-- The consumer endpoint names the public bounded native peer definition.
client-bridge : ∀ {es} → N.Spec.HasTrace k N.client N.idle es ⇔
  (∃[ events ] ∃[ T ] (client k l d ⟹∖√⟨ events ⟩ T × Obs events es))
client-bridge = bridge consumer

-- The producer endpoint names the public bounded native peer definition.
server-bridge : ∀ {es} → N.Spec.HasTrace k N.server N.idle es ⇔
  (∃[ events ] ∃[ T ] (server k l d ⟹∖√⟨ events ⟩ T × Obs events es))
server-bridge = bridge producer
