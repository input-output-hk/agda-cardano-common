{-# OPTIONS --safe #-}

-- Finite adequate successor menus reuse the original node selectors at every raw state.
open import Relation.Binary.Definitions using (DecidableEquality)
open import Data.List using (List)
module Cardano_network.LeiosNotifyPipeLookahead.NodeDriverWireCoreExecution
  (Notification : Set) (notificationEq : DecidableEquality Notification)
  (basis : List Notification) where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥-elim)
open import Data.List using ([]; _∷_; _++_; map; concat; length; upTo)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using
  (∈-map⁺; ∈-map⁻; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-concat⁺′; ∈-upTo⁺)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s; z≤n)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification ⊤ as C
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.CreditModel Notification 1000 as Q
import Cardano_network.LeiosNotifyPipeLookahead.NodeModel Notification 1000 as Server
import Cardano_network.LeiosNotifyPipeLookahead.NodeClientModel Notification ⊤ as Client
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverModel Notification as Node
import Cardano_network.LeiosNotifyPipeLookahead.ClientExecution Notification ⊤ notificationEq as CE
import Cardano_network.LeiosNotifyPipeLookahead.Enumeration Notification as SE
import Cardano_network.LeiosNotifyPipeLookahead.DriverExecution Notification ⊤ notificationEq as DE
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverExecution Notification notificationEq as Exec
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverWireCore Notification as Core
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverWireCoreBridge Notification as Bridge
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverWireCoreBasis Notification basis as Basis
open import Cardano_network.LeiosNotifyPipeLookahead.Selection using (select; select-complete)

-- Successor certificates retain original visible source rules before targets are projected.
VisibleMove : Core.State → D.Event → Set
VisibleMove s row = Σ[ t ∈ Core.State ] Core.Visible s row t

-- Hidden certificates retain both the actual core rule and its sole offer-membership condition.
Move : Core.State → Set
Move s = Σ[ t ∈ Core.State ] Basis.Tau s t

-- The original visible selector is queried on the canonical representative, not recopied.
afterMoves : (s : Core.State) (row : D.Event) → List (VisibleMove s row)
afterMoves s@(Core.core raw queue live) row with Exec.visible-step (Core.canonical s) (Node.wire row)
... | nothing = []
... | just (target , proof) = (Core.erase target , Bridge.erase-visible proof) ∷ []

-- Visible replay targets have zero or one independently certified exact successor.
after : Core.State → D.Event → List Core.State
after s row = map proj₁ (afterMoves s row)

-- Every returned visible target is an original wire rule at the same core states.
after-sound : ∀ {s row t} → t ∈ after s row → Core.Visible s row t
after-sound member with ∈-map⁻ proj₁ member
... | (_ , proof) , _ , refl = proof

-- Original visible-rule completeness identifies only targets, never certificate identities.
after-complete : ∀ {s row t} → Core.Visible s row t → t ∈ after s row
after-complete {s = s@(Core.core raw queue live)} {row} {t} proof
  with Exec.visible-step (Core.canonical s) (Node.wire row) | Exec.visible-complete proof
... | just (_ , _) | refl = here (sym (Core.erase-embed t false false))

-- A successful finite-list selector always names an in-range index.
selected-bound : ∀ {a b} {A : Set a} {B : Set b} {f : A → B} {xs n value} →
  Maybe.map f (select xs n) ≡ just value → n < length xs
selected-bound {xs = []} ()
selected-bound {xs = _ ∷ _} {n = zero} _ = s≤s z≤n
selected-bound {xs = _ ∷ xs} {n = suc n} same = s≤s (selected-bound {xs = xs} {n = n} same)

-- All non-indexed operation families have fixed data-only selector candidates.
fixedChoices : List Exec.Choice
fixedChoices = Exec.accept ∷ Exec.excessive ∷ Exec.queued ∷ Exec.continue ∷ Exec.terminate ∷
  Exec.transport (DE.writeClient D.request) ∷ Exec.transport (DE.writeClient D.quit) ∷
  Exec.transport (DE.writeServer D.done) ∷ Exec.transport DE.readClient ∷ Exec.transport DE.readServer ∷ []

-- Reply commit candidates use only the actual currently selected reply, even outside the basis.
selectedChoices : D.State → List Exec.Choice
selectedChoices raw with S.sender (D.serverState raw)
... | S.selected reply = Exec.transport (DE.writeServer (D.reply reply)) ∷ []
... | _ = []

-- Scheduling indices range over actual finite menus; generic callback/ready transport bypasses are absent.
choices : D.State → List Exec.Choice
choices raw = map Exec.client (upTo (length (CE.internalMoves (D.clientState raw)))) ++
  (map Exec.server (upTo (length (S.internalMoves (D.serverState raw)))) ++
    (fixedChoices ++ selectedChoices raw))

-- Every original client scheduling index embeds in the joint candidate list.
client-listed : ∀ raw {n} → n < length (CE.internalMoves (D.clientState raw)) → Exec.client n ∈ choices raw
client-listed raw bounded = ∈-++⁺ˡ (∈-map⁺ Exec.client (∈-upTo⁺ bounded))

-- Every original server scheduling index remains available independently of client work.
server-listed : ∀ raw {n} → n < length (S.internalMoves (D.serverState raw)) → Exec.server n ∈ choices raw
server-listed raw bounded = ∈-++⁺ʳ (map Exec.client (upTo (length (CE.internalMoves (D.clientState raw)))))
  (∈-++⁺ˡ (∈-map⁺ Exec.server (∈-upTo⁺ bounded)))

-- Fixed choices are tested against original guards rather than being unconditionally enabled.
fixed-listed : ∀ raw {choice} → choice ∈ fixedChoices → choice ∈ choices raw
fixed-listed raw member = ∈-++⁺ʳ (map Exec.client (upTo (length (CE.internalMoves (D.clientState raw)))))
  (∈-++⁺ʳ (map Exec.server (upTo (length (S.internalMoves (D.serverState raw))))) (∈-++⁺ˡ member))

-- The actual selected reply is the final candidate family, without basis membership filtering.
selected-listed : ∀ raw {choice} → choice ∈ selectedChoices raw → choice ∈ choices raw
selected-listed raw member = ∈-++⁺ʳ (map Exec.client (upTo (length (CE.internalMoves (D.clientState raw)))))
  (∈-++⁺ʳ (map Exec.server (upTo (length (S.internalMoves (D.serverState raw)))))
    (∈-++⁺ʳ fixedChoices member))

-- Every selector produced by original source completeness is contained in the finite candidates.
choose-listed : ∀ {s t} (proof : Node.Tau s t) → Exec.choose proof ∈ choices (Node.driverState s)
choose-listed (Node.clientSchedule {raw = raw} (Client.schedule proof))
  with select-complete (CE.target-complete proof)
... | n , same = client-listed raw (selected-bound {f = proj₁} {xs = CE.internalMoves (D.clientState raw)} same)
choose-listed (Node.serverSchedule {raw = raw} (Server.schedule proof allowed))
  with select-complete (SE.target-complete proof)
... | n , same = server-listed raw (selected-bound {f = proj₁} {xs = S.internalMoves (D.serverState raw)} same)
choose-listed (Node.serverSchedule {raw = raw} (Server.admitAccepted _)) = fixed-listed raw (here refl)
choose-listed (Node.serverSchedule {raw = raw} (Server.admitExcessive _)) = fixed-listed raw (there (here refl))
choose-listed (Node.serverSchedule {raw = raw} (Server.nextQueued _ _)) = fixed-listed raw (there (there (here refl)))
choose-listed (Node.continueReady {raw = raw} _) = fixed-listed raw (there (there (there (here refl))))
choose-listed (Node.terminateReady {raw = raw} _) = fixed-listed raw (there (there (there (there (here refl)))))
choose-listed (Node.transport (D.clientInternal _) ())
choose-listed (Node.transport (D.serverInternal _) ())
choose-listed (Node.transport (D.clientCallback _ _) ())
choose-listed (Node.transport (D.serverCallback _) ())
choose-listed (Node.transport {raw = raw} (D.commitClient {m = D.request} _) _) =
  fixed-listed raw (there (there (there (there (there (here refl))))))
choose-listed (Node.transport {raw = raw} (D.commitClient {m = D.quit} _) _) =
  fixed-listed raw (there (there (there (there (there (there (here refl)))))))
choose-listed (Node.transport {raw = raw} (D.commitServer {m = D.done} _) _) =
  fixed-listed raw (there (there (there (there (there (there (there (here refl))))))))
choose-listed (Node.transport {raw = raw@(D.pair c (S.state r w (S.selected reply) completed flag) cs sc pc ps rc rs)}
  (D.commitServer {m = D.reply .reply} (S.send active)) _) = selected-listed raw (here refl)
choose-listed (Node.transport {raw = raw} (D.decodeClient _) _) =
  fixed-listed raw (there (there (there (there (there (there (there (there (here refl)))))))))
choose-listed (Node.transport {raw = raw} (D.decodeServer _) _) =
  fixed-listed raw (there (there (there (there (there (there (there (there (there (here refl))))))))))

-- Erased original hidden rules are operational core steps and therefore basis-unrestricted.
operational-allowed : ∀ {s t} (proof : Node.Tau s t) → Basis.Allowed (Bridge.erase-operational proof)
operational-allowed (Node.clientSchedule _) = tt
operational-allowed (Node.continueReady _) = tt
operational-allowed (Node.terminateReady _) = tt
operational-allowed (Node.serverSchedule _) = tt
operational-allowed (Node.transport _ _) = tt

-- Every operational candidate is interpreted by the unchanged original full-policy selector.
operationalOne : (s : Core.State) → Bool → Bool → Exec.Choice → List (Move s)
operationalOne s@(Core.core raw queue live) forecast halt choice with Exec.hidden-step (Core.embed s forecast halt) choice
... | nothing = []
... | just (target , proof) = (Core.erase target , Bridge.erase-operational proof , operational-allowed proof) ∷ []

-- All four external snapshots cover existential operational choices without retaining flag cycles.
snapshots : List (Bool × Bool)
snapshots = (false , false) ∷ (false , true) ∷ (true , false) ∷ (true , true) ∷ []

-- A chosen source snapshot always appears in the fixed four-element list.
snapshot-listed : ∀ forecast halt → (forecast , halt) ∈ snapshots
snapshot-listed false false = here refl
snapshot-listed false true = there (here refl)
snapshot-listed true false = there (there (here refl))
snapshot-listed true true = there (there (there (here refl)))

-- Snapshot and operation candidates are finite even with an infinite notification carrier.
operationalMoves : (s : Core.State) → List (Move s)
operationalMoves s = concat (map (λ { (forecast , halt) →
  concat (map (operationalOne s forecast halt) (choices (Core.driverState s))) }) snapshots)

-- Finite offered-value choices retain their actual membership certificates and duplicate positions.
offerChoices : (values : List Notification) → (∀ {value} → value ∈ values → value ∈ basis) →
  List (Σ[ value ∈ Notification ] value ∈ basis)
offerChoices [] include = []
offerChoices (value ∷ values) include = (value , include (here refl)) ∷
  offerChoices values (λ member → include (there member))

-- Every basis value is listed, with some valid certificate rather than a fixed proof identity.
offer-choice-listed : (values : List Notification) (include : ∀ {value} → value ∈ values → value ∈ basis) →
  ∀ {value} → value ∈ values → value ∈ map proj₁ (offerChoices values include)
offer-choice-listed (_ ∷ _) include (here refl) = here refl
offer-choice-listed (_ ∷ values) include (there member) = there (offer-choice-listed values (λ proof → include (there proof)) member)

-- Positive credit and the original active guard are both checked before retaining an offer.
offerOne : (s : Core.State) → (Σ[ value ∈ Notification ] value ∈ basis) → List (Move s)
offerOne (Core.core raw (Q.credits zero queued) live) candidate = []
offerOne s@(Core.core raw (Q.credits (suc n) queued) live) (value , member)
  with Exec.visible-step (Core.canonical s) (Node.eligible value)
... | nothing = []
... | just (target , proof@(Node.applicationInput _)) = (Core.erase target , Core.offered proof (λ ()) , member) ∷ []

-- Only newly supplied eligible notifications range over the declared finite payload basis.
offerMoves : (s : Core.State) → List (Move s)
offerMoves s = concat (map (offerOne s) (offerChoices basis (λ member → member)))

-- A normal handler is queried only with its currently selected exact notification.
handlerOne : (s : Core.State) → Notification → List (Move s)
handlerOne s@(Core.core raw queue live) value with Exec.visible-step (Core.canonical s) (Node.handledNormal value)
... | nothing = []
... | just (target , proof@(Node.normalHandler _)) = (Core.erase target , Core.handled proof , tt) ∷ []

-- Stored normal values are never restricted by the offer basis, including arbitrary raw states.
handlerMoves : (s : Core.State) → List (Move s)
handlerMoves s with C.receiver (D.clientState (Core.driverState s))
... | C.handling (S.normal value) = handlerOne s value
... | _ = []

-- The existing selected-Cancel fault is tested independently of all other operation families.
rejectedMoves : (s : Core.State) → List (Move s)
rejectedMoves s@(Core.core raw queue live) with Exec.visible-step (Core.canonical s) Node.rejectedCancel
... | nothing = []
... | just (target , proof@(Node.canceledHandlerExit _)) = (Core.erase target , Core.rejected proof , tt) ∷ []

-- Every hidden family retains its independent guarded successor certificates.
menus : (s : Core.State) → List (List (Move s))
menus s = operationalMoves s ∷ offerMoves s ∷ handlerMoves s ∷ rejectedMoves s ∷ []

-- Concatenation retains independent alternatives instead of imposing a scheduling priority.
moves : (s : Core.State) → List (Move s)
moves s = concat (menus s)

-- Replay consumes the finite projected target list, preserving possible duplicates.
taus : Core.State → List Core.State
taus s = map proj₁ (moves s)

-- Every enumerated hidden target retains the original restricted source rule.
taus-sound : ∀ {s t} → t ∈ taus s → Basis.Tau s t
taus-sound member with ∈-map⁻ proj₁ member
... | (_ , proof) , _ , refl = proof

-- A family target embeds through certificate projection and menu concatenation.
listed : ∀ {s t menu} → menu ∈ menus s → t ∈ map proj₁ menu → t ∈ taus s
listed family target with ∈-map⁻ proj₁ target
... | move , member , refl = ∈-map⁺ proj₁ (∈-concat⁺′ member family)

-- Candidate and target membership compose through a finite map/concatenation.
part-listed : ∀ {s} {A : Set} {values : List A} (part : A → List (Move s)) {value t} →
  value ∈ values → t ∈ map proj₁ (part value) → t ∈ map proj₁ (concat (map part values))
part-listed part candidate target with ∈-map⁻ proj₁ target
... | move , member , refl = ∈-map⁺ proj₁ (∈-concat⁺′ member (∈-map⁺ part candidate))

-- An original operational selector target appears even when its certificate is reconstructed.
operationalOne-complete : ∀ {s t forecast halt choice} →
  Maybe.map proj₁ (Exec.hidden-step (Core.embed s forecast halt) choice) ≡ just (Core.embed t forecast halt) →
  t ∈ map proj₁ (operationalOne s forecast halt choice)
operationalOne-complete {s = s@(Core.core raw queue live)} {t} {forecast} {halt} {choice} same
  with Exec.hidden-step (Core.embed s forecast halt) choice | same
... | just (_ , _) | refl = here (sym (Core.erase-embed t forecast halt))

-- Every existential source snapshot and original operation has a listed exact core target.
operational-complete : ∀ {s t forecast halt} → Node.Tau (Core.embed s forecast halt) (Core.embed t forecast halt) →
  t ∈ map proj₁ (operationalMoves s)
operational-complete {s = s@(Core.core raw queue live)} {t} {forecast} {halt} proof =
  part-listed (λ { (f , h) → concat (map (operationalOne s f h) (choices raw)) }) (snapshot-listed forecast halt)
    (part-listed (operationalOne s forecast halt) (choose-listed proof) (operationalOne-complete (Exec.chosen-complete proof)))

-- Positive offers are included for every independent guarded source target and basis witness.
offerOne-complete : ∀ {s t value} (member : value ∈ basis) →
  Node.Step (Core.canonical s) (Node.eligible value) (Core.canonical t) → Q.free (Core.queueState s) ≢ zero →
  t ∈ map proj₁ (offerOne s (value , member))
offerOne-complete {s = Core.core raw (Q.credits zero queued) live} member proof nonzero = ⊥-elim (nonzero refl)
offerOne-complete {s = s@(Core.core raw (Q.credits (suc n) queued) live)} {t} {value} member proof nonzero
  with Exec.visible-step (Core.canonical s) (Node.eligible value) | Exec.visible-complete proof
... | just (_ , Node.applicationInput _) | refl =
  here (sym (Core.erase-embed t false false))

-- Independent membership chooses some listed offer certificate, preserving the same target.
offer-complete : ∀ {s t value} → Node.Step (Core.canonical s) (Node.eligible value) (Core.canonical t) →
  Q.free (Core.queueState s) ≢ zero → value ∈ basis → t ∈ map proj₁ (offerMoves s)
offer-complete {s} {t} {value} proof nonzero member
  with ∈-map⁻ proj₁ (offer-choice-listed basis (λ present → present) member)
... | (_ , actual) , candidate , refl = part-listed (offerOne s) candidate (offerOne-complete actual proof nonzero)

-- Normal handling reconstructs only its exact target and keeps arbitrary stored values.
handlerOne-complete : ∀ {s t value} → Node.Step (Core.canonical s) (Node.handledNormal value) (Core.canonical t) →
  t ∈ map proj₁ (handlerOne s value)
handlerOne-complete {s = s@(Core.core raw queue live)} {t} {value} proof
  with Exec.visible-step (Core.canonical s) (Node.handledNormal value) | Exec.visible-complete proof
... | just (_ , Node.normalHandler _) | refl =
  here (sym (Core.erase-embed t false false))

-- Source handler rules force the one selected normal payload used by the handler menu.
handler-complete : ∀ {s t value} → Node.Step (Core.canonical s) (Node.handledNormal value) (Core.canonical t) →
  t ∈ map proj₁ (handlerMoves s)
handler-complete proof@(Node.normalHandler (Client.handled (C.delivered _))) = handlerOne-complete proof

-- Abnormal Cancel handling retains its exact failed-client target.
rejected-complete : ∀ {s t} → Node.Step (Core.canonical s) Node.rejectedCancel (Core.canonical t) →
  t ∈ map proj₁ (rejectedMoves s)
rejected-complete {s = s@(Core.core raw queue live)} {t} proof
  with Exec.visible-step (Core.canonical s) Node.rejectedCancel | Exec.visible-complete proof
... | just (_ , Node.canceledHandlerExit _) | refl =
  here (sym (Core.erase-embed t false false))

-- All restricted hidden rules are covered at every state, with no extra state invariant.
taus-complete : ∀ {s t} → Basis.Tau s t → t ∈ taus s
taus-complete (Core.operational {forecast = forecast} {halt = halt} proof , _) =
  listed (here refl) (operational-complete {forecast = forecast} {halt = halt} proof)
taus-complete (Core.offered proof nonzero , member) = listed (there (here refl)) (offer-complete proof nonzero member)
taus-complete (Core.handled proof , _) = listed (there (there (here refl))) (handler-complete proof)
taus-complete (Core.rejected proof , _) = listed (there (there (there (here refl)))) (rejected-complete proof)
