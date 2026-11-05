{-# OPTIONS --guardedness #-}

-- Acquisition continuation provenance. The two marks retain captures through
-- arbitrary counter wrappers and do not assert freshness of shared heaps.
module ConnectionManagement.Properties.OutboundOriginCore where

open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Class.DecEq using (_≟_)
open import Data.Maybe.Properties using (just-injective)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Function using (case_of_)
open import ConnectionManagement.Domain using (WorkerId; EntryId; PromiseId; ident; connection)
open import ConnectionManagement.Store using (put; delete; lookup)
import ConnectionManagement.State as S
import ConnectionManagement.Machine as M
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.OutboundAcquire as A

promiseMark : A.PC → Maybe (EntryId × PromiseId)
promiseMark (A.count next) = promiseMark next
promiseMark (A.openSocket entry promise) = just (entry , promise)
promiseMark (A.configureSocket entry promise) = just (entry , promise)
promiseMark (A.bindSocket entry promise) = just (entry , promise)
promiseMark (A.connectSocket entry promise) = just (entry , promise)
promiseMark (A.localAddress entry promise) = just (entry , promise)
promiseMark (A.updateAddress entry promise key) = just (entry , promise)
promiseMark (A.forkHandler entry promise key) = just (entry , promise)
promiseMark _ = nothing
entryMark : A.PC → Maybe EntryId
entryMark (A.count next) = entryMark next
entryMark (A.allocatePromise entry) = just entry
entryMark _ = nothing

-- Lookup at the final fork is converted to stored-row membership. Tracking all
-- rows avoids a uniqueness premise: delete can expose a shadowed row.
record Marked {Value : Set} (mark : A.PC → Maybe Value) (rows : A.Runtime)
  (caller : WorkerId) (request : A.Request) (value : Value) : Set where
 constructor marked
 field
  savedFrame : A.Frame
  member : (caller , savedFrame) ∈ rows
  request-equal : A.req savedFrame ≡ request
  marked-PC : mark (A.pc savedFrame) ≡ just value

lookup-member : ∀ (caller : WorkerId) (rows : A.Runtime) {savedFrame : A.Frame} → lookup caller rows ≡ just savedFrame → (caller , savedFrame) ∈ rows
lookup-member caller [] ()
lookup-member caller ((other , savedFrame) ∷ rows) actual with caller ≟ other
... | yes refl = here (cong (λ saved → caller , saved) (sym (just-injective actual)))
... | no _ = there (lookup-member caller rows actual)

private
 delete-member : ∀ (caller : WorkerId) (rows : A.Runtime) {binding : WorkerId × A.Frame} → binding ∈ delete caller rows → binding ∈ rows
 delete-member caller [] ()
 delete-member caller ((other , savedFrame) ∷ rows) member with caller ≟ other
 ... | yes _ = there member
 delete-member caller ((other , savedFrame) ∷ rows) (here same) | no _ = here same
 delete-member caller ((other , savedFrame) ∷ rows) (there member) | no _ = there (delete-member caller rows member)

put-member : ∀ (caller : WorkerId) (newFrame : A.Frame) (rows : A.Runtime) {binding : WorkerId × A.Frame} → binding ∈ put caller newFrame rows →
  binding ≡ (caller , newFrame) ⊎ binding ∈ rows
put-member caller newFrame [] (here same) = inj₁ same
put-member caller newFrame [] (there ())
put-member caller newFrame ((other , savedFrame) ∷ rows) member with caller ≟ other
... | yes refl with member
...   | here same = inj₁ same
...   | there member′ = inj₂ (there member′)
put-member caller newFrame ((other , savedFrame) ∷ rows) (here same) | no _ = inj₂ (here same)
put-member caller newFrame ((other , savedFrame) ∷ rows) (there member) | no _ with put-member caller newFrame rows member
... | inj₁ same = inj₁ same
... | inj₂ prior = inj₂ (there prior)

-- These laws compose only backward preservation, not creator events.
record Backwards (before after : A.Runtime) : Set where
 constructor backwards
 field
  promise-back : ∀ caller request entry promise → Marked promiseMark after caller request (entry , promise) → Marked promiseMark before caller request (entry , promise)
  entry-back : ∀ caller request entry → Marked entryMark after caller request entry → Marked entryMark before caller request entry
backwards-refl : ∀ rows → Backwards rows rows
backwards-refl rows = backwards (λ caller request entry promise observed → observed) (λ caller request entry observed → observed)
backwards-trans : ∀ {before middle after} → Backwards before middle → Backwards middle after → Backwards before after
backwards-trans first second = backwards
  (λ caller request entry promise observed → Backwards.promise-back first caller request entry promise (Backwards.promise-back second caller request entry promise observed))
  (λ caller request entry observed → Backwards.entry-back first caller request entry (Backwards.entry-back second caller request entry observed))
same-backwards : ∀ {before after} → after ≡ before → Backwards before after
same-backwards refl = backwards-refl _
removed-backwards : ∀ caller rows → Backwards rows (delete caller rows)
removed-backwards caller rows = backwards
  (λ other request entry promise → λ { (marked savedFrame member sameRequest found) → marked savedFrame (delete-member caller rows member) sameRequest found })
  (λ other request entry → λ { (marked savedFrame member sameRequest found) → marked savedFrame (delete-member caller rows member) sameRequest found })
begun-backwards : ∀ caller request rows → Backwards rows (put caller (A.frame request A.selecting) rows)
begun-backwards caller request rows = backwards promiseBack entryBack
 where
 promiseBack : ∀ other req entry promise → Marked promiseMark (put caller (A.frame request A.selecting) rows) other req (entry , promise) → Marked promiseMark rows other req (entry , promise)
 promiseBack other req entry promise (marked savedFrame member sameRequest found) with put-member caller (A.frame request A.selecting) rows member
 ... | inj₁ refl = case found of λ ()
 ... | inj₂ prior = marked savedFrame prior sameRequest found
 entryBack : ∀ other req entry → Marked entryMark (put caller (A.frame request A.selecting) rows) other req entry → Marked entryMark rows other req entry
 entryBack other req entry (marked savedFrame member sameRequest found) with put-member caller (A.frame request A.selecting) rows member
 ... | inj₁ refl = case found of λ ()
 ... | inj₂ prior = marked savedFrame prior sameRequest found

-- Active runtime updates have at most one writer per actual outer event.
-- Detached cleanup may change the shared world while this runtime is unchanged.
data Effect (before after : O.Configuration) : Set where
 continued : Backwards (O.acquiring before) (O.acquiring after) → Effect before after
 same : O.acquiring after ≡ O.acquiring before → Effect before after
 removed : ∀ caller → O.acquiring after ≡ delete caller (O.acquiring before) → Effect before after
 begun : ∀ caller request → O.acquiring after ≡ put caller (A.frame request A.selecting) (O.acquiring before) → Effect before after
 advanced : ∀ caller action oldFrame newFrame →
   lookup caller (O.acquiring before) ≡ just oldFrame →
   A.step caller (M.responder (O.core before)) action oldFrame (M.world (O.core before)) ≡
     just (newFrame , M.world (O.core after)) →
   O.acquiring after ≡ put caller newFrame (O.acquiring before) → Effect before after

-- A successful source step either carries a marked continuation backwards,
-- allocates its promise, or creates its fresh entry reservation.
data Step (action : A.Action) (before : A.Frame) (world : S.State) (after : A.Frame) : Set where
 preserved : A.req after ≡ A.req before →
   (∀ entry promise → promiseMark (A.pc after) ≡ just (entry , promise) → promiseMark (A.pc before) ≡ just (entry , promise)) →
   (∀ entry → entryMark (A.pc after) ≡ just entry → entryMark (A.pc before) ≡ just entry) →
   Step action before world after
 allocated : ∀ entry → action ≡ A.newPromise → A.req after ≡ A.req before →
   A.pc before ≡ A.allocatePromise entry → A.pc after ≡ A.openSocket entry (ident (S.nextPromise world)) →
   Step action before world after
 reserved : action ≡ A.select nothing → A.req after ≡ A.req before → A.pc before ≡ A.selecting →
   A.pc after ≡ A.count (A.allocatePromise (ident (S.nextEntry (S.cm world)))) →
   Step action before world after

private
 none-step : ∀ {action before world after} → A.req after ≡ A.req before →
   promiseMark (A.pc after) ≡ nothing → entryMark (A.pc after) ≡ nothing → Step action before world after
 none-step sameRequest noPromise noEntry = preserved sameRequest
   (λ entry promise found → case trans (sym noPromise) found of λ ())
   (λ entry found → case trans (sym noEntry) found of λ ())

open import Data.Bool using (true; false)
open import Data.Maybe.Properties using (just-injective)
import ConnectionManagement.Rules.OutboundCases as C
import ConnectionManagement.Rules.InformationChannel as Queue

private
 module Source where
  open S using (cm; mapCell; full; taken; entries; nextEntry; nextPromise; handshakeResults; countIncoming; sockets; handlers; negotiated; query; handlerError; handshakeError; handshakeQuery; noResponderMode; responderMode; inboundInfo; newConnection; newConnectionInfo; unnegotiated; reservedOutbound; outboundUni; outboundDup; outboundIdle; inboundIdle; inboundActive; duplexActive; terminating; terminated)
  open import ConnectionManagement.Domain using (inbound; outbound)

  result-step : ∀ {action f s} {pair pair′ : A.Frame × S.State} → just pair ≡ just pair′ → Step action f s (proj₁ pair) → Step action f s (proj₁ pair′)
  result-step {action} {f} {s} eq = subst (λ pair → Step action f s (proj₁ pair)) (just-injective eq)
  choice-step : ∀ action first e d f s {out} → A.applyChoice first e d f s ≡ just out → Step action f s (proj₁ out)
  choice-step action first e C.retry f s ()
  choice-step action first e (C.waitInbound k) f s eq = result-step eq (none-step refl refl refl)
  choice-step action true e (C.refuse err) f s eq = result-step eq (none-step refl refl refl)
  choice-step action false e (C.refuse err) f s eq = result-step eq (none-step refl refl refl)
  choice-step action first e (C.gone result) f s eq = result-step eq (none-step refl refl refl)
  choice-step action true e (C.reuse st result) f s eq = result-step eq (none-step refl refl refl)
  choice-step action false e (C.reuse st result) f s eq = result-step eq (none-step refl refl refl)

  known-step : ∀ chosen m f s {out} → A.pc f ≡ A.selecting → A.selectKnown chosen m f s ≡ just out → Step (A.select chosen) f s (proj₁ out)
  known-step (just e) m f s pcEq eq with lookup e (entries (cm s))
  ... | nothing = case eq of λ ()
  ... | just st = choice-step (A.select (just e)) true e (C.acquireCase st) f s eq
  known-step nothing m f s pcEq eq with A.provenance (A.req f)
  ... | inbound = result-step eq (none-step refl refl refl)
  ... | outbound with lookup (ident (nextEntry (cm s))) (entries (cm s))
  ...   | just _ = case eq of λ ()
  ...   | nothing = result-step eq (reserved refl refl pcEq refl)
  selection-step : ∀ chosen f s {out} → A.pc f ≡ A.selecting → A.selectEntry chosen f s ≡ just out → Step (A.select chosen) f s (proj₁ out)
  selection-step chosen f s pcEq eq with mapCell (cm s)
  ... | taken _ = case eq of λ ()
  ... | full m with A.validSelection (A.peer (A.req f)) chosen m
  ...   | false = case eq of λ ()
  ...   | true = known-step chosen m f s pcEq eq
  success-step : ∀ mode e k h flow f s {out} →
    A.commitSuccess mode e k h flow f s ≡ just out → Step A.commitHandshake f s (proj₁ out)
  success-step mode e k h flow f s eq with lookup e (entries (cm s))
  ... | nothing = case eq of λ ()
  ... | just st with C.successCase k (A.child (A.req f)) h flow st
  ...   | C.decision replacement notify (C.raised err) = result-step eq (none-step refl refl refl)
  ...   | C.decision replacement false (C.connected k′ flow′ h′) with replacement
  ...     | nothing = result-step eq (none-step refl refl refl)
  ...     | just _ = result-step eq (none-step refl refl refl)
  success-step mode e k h flow f s eq | just st | C.decision replacement false (C.disconnected k′ reason) with replacement
  ... | nothing = result-step eq (none-step refl refl refl)
  ... | just _ = result-step eq (none-step refl refl refl)
  success-step noResponderMode e k h flow f s eq | just st | C.decision replacement true result with result | replacement
  ... | C.connected _ _ _ | nothing = result-step eq (none-step refl refl refl)
  ... | C.connected _ _ _ | just _ = result-step eq (none-step refl refl refl)
  ... | C.disconnected _ _ | nothing = result-step eq (none-step refl refl refl)
  ... | C.disconnected _ _ | just _ = result-step eq (none-step refl refl refl)
  ... | C.raised _ | _ = result-step eq (none-step refl refl refl)
  success-step responderMode e k h flow f s eq | just st | C.decision replacement true result
    with Queue.writeMessage (newConnection (newConnectionInfo outbound k flow h)) (inboundInfo s) in enqueued | result | replacement
  ... | nothing | C.connected _ _ _ | _ rewrite enqueued = case eq of λ ()
  ... | nothing | C.disconnected _ _ | _ rewrite enqueued = case eq of λ ()
  ... | just queue | C.connected _ _ _ | nothing rewrite enqueued = result-step eq (none-step refl refl refl)
  ... | just queue | C.connected _ _ _ | just _ rewrite enqueued = result-step eq (none-step refl refl refl)
  ... | just queue | C.disconnected _ _ | nothing rewrite enqueued = result-step eq (none-step refl refl refl)
  ... | just queue | C.disconnected _ _ | just _ rewrite enqueued = result-step eq (none-step refl refl refl)
  ... | _ | C.raised _ | _ = result-step eq (none-step refl refl refl)

  -- Error/query completion likewise releases the frame's captured reference.
  error-step : ∀ e k reason f s {out} → A.commitError e k reason f s ≡ just out →
    Step A.commitHandshake f s (proj₁ out)
  error-step e k reason f s eq with lookup e (entries (cm s)) | mapCell (cm s)
  ... | nothing | _ = case eq of λ ()
  ... | just _ | taken _ = case eq of λ ()
  ... | just st | full m = result-step eq (none-step refl refl refl)

  step-classify : ∀ caller mode action f s {out} → A.step caller mode action f s ≡ just out → Step action f s (proj₁ out)
  step-classify caller mode (A.select chosen) f s eq with A.pc f in pcEq
  ... | A.selecting = selection-step chosen f s pcEq eq
  step-classify caller mode (A.select chosen) f s eq | (A.count p) = case eq of λ ()
  step-classify caller mode (A.select chosen) f s eq | (A.allocatePromise e) = case eq of λ ()
  step-classify caller mode (A.select chosen) f s eq | (A.openSocket e p) = case eq of λ ()
  step-classify caller mode (A.select chosen) f s eq | (A.configureSocket e p) = case eq of λ ()
  step-classify caller mode (A.select chosen) f s eq | (A.bindSocket e p) = case eq of λ ()
  step-classify caller mode (A.select chosen) f s eq | (A.connectSocket e p) = case eq of λ ()
  step-classify caller mode (A.select chosen) f s eq | (A.localAddress e p) = case eq of λ ()
  step-classify caller mode (A.select chosen) f s eq | (A.updateAddress e p k) = case eq of λ ()
  step-classify caller mode (A.select chosen) f s eq | (A.forkHandler e p k) = case eq of λ ()
  step-classify caller mode (A.select chosen) f s eq | (A.connectedCommit e p k) = case eq of λ ()
  step-classify caller mode (A.select chosen) f s eq | (A.awaitResult e p k) = case eq of λ ()
  step-classify caller mode (A.select chosen) f s eq | (A.commitResult e k result) = case eq of λ ()
  step-classify caller mode (A.select chosen) f s eq | (A.waitingInbound e k) = case eq of λ ()
  step-classify caller mode (A.select chosen) f s eq | (A.closeError e err′) = case eq of λ ()
  step-classify caller mode (A.select chosen) f s eq | (A.removeError e err′) = case eq of λ ()
  step-classify caller mode (A.select chosen) f s eq | (A.complete result) = case eq of λ ()
  step-classify caller mode A.readCounters f s eq with A.pc f in pcEq | mapCell (cm s)
  ... | A.count next | full m with countIncoming (entries (cm s)) m
  ...   | nothing = case eq of λ ()
  ...   | just _ = result-step eq (preserved {before = f} {after = record f { pc = next }} refl (λ entry promise found → trans (cong promiseMark pcEq) found) (λ entry found → trans (cong entryMark pcEq) found))
  step-classify caller mode A.readCounters f s eq | A.selecting | _ = case eq of λ ()
  step-classify caller mode A.readCounters f s eq | (A.allocatePromise e) | _ = case eq of λ ()
  step-classify caller mode A.readCounters f s eq | (A.openSocket e p) | _ = case eq of λ ()
  step-classify caller mode A.readCounters f s eq | (A.configureSocket e p) | _ = case eq of λ ()
  step-classify caller mode A.readCounters f s eq | (A.bindSocket e p) | _ = case eq of λ ()
  step-classify caller mode A.readCounters f s eq | (A.connectSocket e p) | _ = case eq of λ ()
  step-classify caller mode A.readCounters f s eq | (A.localAddress e p) | _ = case eq of λ ()
  step-classify caller mode A.readCounters f s eq | (A.updateAddress e p k) | _ = case eq of λ ()
  step-classify caller mode A.readCounters f s eq | (A.forkHandler e p k) | _ = case eq of λ ()
  step-classify caller mode A.readCounters f s eq | (A.connectedCommit e p k) | _ = case eq of λ ()
  step-classify caller mode A.readCounters f s eq | (A.awaitResult e p k) | _ = case eq of λ ()
  step-classify caller mode A.readCounters f s eq | (A.commitResult e k result) | _ = case eq of λ ()
  step-classify caller mode A.readCounters f s eq | (A.waitingInbound e k) | _ = case eq of λ ()
  step-classify caller mode A.readCounters f s eq | (A.closeError e err′) | _ = case eq of λ ()
  step-classify caller mode A.readCounters f s eq | (A.removeError e err′) | _ = case eq of λ ()
  step-classify caller mode A.readCounters f s eq | (A.complete result) | _ = case eq of λ ()
  step-classify caller mode A.readCounters f s eq | (A.count p) | taken w = case eq of λ ()
  step-classify caller mode A.newPromise f s eq with A.pc f in pcEq
  ... | A.allocatePromise e with lookup (ident (nextPromise s)) (handshakeResults s)
  ...   | just _ = case eq of λ ()
  ...   | nothing = result-step eq (allocated e refl refl pcEq refl)
  step-classify caller mode A.newPromise f s eq | A.selecting = case eq of λ ()
  step-classify caller mode A.newPromise f s eq | (A.count p) = case eq of λ ()
  step-classify caller mode A.newPromise f s eq | (A.openSocket e p) = case eq of λ ()
  step-classify caller mode A.newPromise f s eq | (A.configureSocket e p) = case eq of λ ()
  step-classify caller mode A.newPromise f s eq | (A.bindSocket e p) = case eq of λ ()
  step-classify caller mode A.newPromise f s eq | (A.connectSocket e p) = case eq of λ ()
  step-classify caller mode A.newPromise f s eq | (A.localAddress e p) = case eq of λ ()
  step-classify caller mode A.newPromise f s eq | (A.updateAddress e p k) = case eq of λ ()
  step-classify caller mode A.newPromise f s eq | (A.forkHandler e p k) = case eq of λ ()
  step-classify caller mode A.newPromise f s eq | (A.connectedCommit e p k) = case eq of λ ()
  step-classify caller mode A.newPromise f s eq | (A.awaitResult e p k) = case eq of λ ()
  step-classify caller mode A.newPromise f s eq | (A.commitResult e k result) = case eq of λ ()
  step-classify caller mode A.newPromise f s eq | (A.waitingInbound e k) = case eq of λ ()
  step-classify caller mode A.newPromise f s eq | (A.closeError e err′) = case eq of λ ()
  step-classify caller mode A.newPromise f s eq | (A.removeError e err′) = case eq of λ ()
  step-classify caller mode A.newPromise f s eq | (A.complete result) = case eq of λ ()
  step-classify caller mode A.openOK f s eq with A.pc f in pcEq | lookup (A.socketRef (A.req f)) (sockets s)
  ... | A.openSocket e p | nothing = result-step eq (preserved {before = f} {after = record f { pc = A.configureSocket e p }} refl (λ entry promise found → trans (cong promiseMark pcEq) found) (λ entry found → trans (cong entryMark pcEq) found))
  step-classify caller mode A.openOK f s eq | A.selecting | _ = case eq of λ ()
  step-classify caller mode A.openOK f s eq | (A.count p) | _ = case eq of λ ()
  step-classify caller mode A.openOK f s eq | (A.allocatePromise e) | _ = case eq of λ ()
  step-classify caller mode A.openOK f s eq | (A.configureSocket e p) | _ = case eq of λ ()
  step-classify caller mode A.openOK f s eq | (A.bindSocket e p) | _ = case eq of λ ()
  step-classify caller mode A.openOK f s eq | (A.connectSocket e p) | _ = case eq of λ ()
  step-classify caller mode A.openOK f s eq | (A.localAddress e p) | _ = case eq of λ ()
  step-classify caller mode A.openOK f s eq | (A.updateAddress e p k) | _ = case eq of λ ()
  step-classify caller mode A.openOK f s eq | (A.forkHandler e p k) | _ = case eq of λ ()
  step-classify caller mode A.openOK f s eq | (A.connectedCommit e p k) | _ = case eq of λ ()
  step-classify caller mode A.openOK f s eq | (A.awaitResult e p k) | _ = case eq of λ ()
  step-classify caller mode A.openOK f s eq | (A.commitResult e k result) | _ = case eq of λ ()
  step-classify caller mode A.openOK f s eq | (A.waitingInbound e k) | _ = case eq of λ ()
  step-classify caller mode A.openOK f s eq | (A.closeError e err′) | _ = case eq of λ ()
  step-classify caller mode A.openOK f s eq | (A.removeError e err′) | _ = case eq of λ ()
  step-classify caller mode A.openOK f s eq | (A.complete result) | _ = case eq of λ ()
  step-classify caller mode A.openOK f s eq | (A.openSocket e p) | just sock = case eq of λ ()
  step-classify caller mode A.configureOK f s eq with A.pc f in pcEq | A.bindLocal (A.req f)
  ... | A.configureSocket e p | nothing = result-step eq (preserved {before = f} {after = record f { pc = A.connectSocket e p }} refl (λ entry promise found → trans (cong promiseMark pcEq) found) (λ entry found → trans (cong entryMark pcEq) found))
  ... | A.configureSocket e p | just _ = result-step eq (preserved {before = f} {after = record f { pc = A.bindSocket e p }} refl (λ entry promise found → trans (cong promiseMark pcEq) found) (λ entry found → trans (cong entryMark pcEq) found))
  step-classify caller mode A.configureOK f s eq | A.selecting | _ = case eq of λ ()
  step-classify caller mode A.configureOK f s eq | (A.count p) | _ = case eq of λ ()
  step-classify caller mode A.configureOK f s eq | (A.allocatePromise e) | _ = case eq of λ ()
  step-classify caller mode A.configureOK f s eq | (A.openSocket e p) | _ = case eq of λ ()
  step-classify caller mode A.configureOK f s eq | (A.bindSocket e p) | _ = case eq of λ ()
  step-classify caller mode A.configureOK f s eq | (A.connectSocket e p) | _ = case eq of λ ()
  step-classify caller mode A.configureOK f s eq | (A.localAddress e p) | _ = case eq of λ ()
  step-classify caller mode A.configureOK f s eq | (A.updateAddress e p k) | _ = case eq of λ ()
  step-classify caller mode A.configureOK f s eq | (A.forkHandler e p k) | _ = case eq of λ ()
  step-classify caller mode A.configureOK f s eq | (A.connectedCommit e p k) | _ = case eq of λ ()
  step-classify caller mode A.configureOK f s eq | (A.awaitResult e p k) | _ = case eq of λ ()
  step-classify caller mode A.configureOK f s eq | (A.commitResult e k result) | _ = case eq of λ ()
  step-classify caller mode A.configureOK f s eq | (A.waitingInbound e k) | _ = case eq of λ ()
  step-classify caller mode A.configureOK f s eq | (A.closeError e err′) | _ = case eq of λ ()
  step-classify caller mode A.configureOK f s eq | (A.removeError e err′) | _ = case eq of λ ()
  step-classify caller mode A.configureOK f s eq | (A.complete result) | _ = case eq of λ ()
  step-classify caller mode A.bindOK f s eq with A.pc f in pcEq
  ... | A.bindSocket e p = result-step eq (preserved {before = f} {after = record f { pc = A.connectSocket e p }} refl (λ entry promise found → trans (cong promiseMark pcEq) found) (λ entry found → trans (cong entryMark pcEq) found))
  step-classify caller mode A.bindOK f s eq | A.selecting = case eq of λ ()
  step-classify caller mode A.bindOK f s eq | (A.count p) = case eq of λ ()
  step-classify caller mode A.bindOK f s eq | (A.allocatePromise e) = case eq of λ ()
  step-classify caller mode A.bindOK f s eq | (A.openSocket e p) = case eq of λ ()
  step-classify caller mode A.bindOK f s eq | (A.configureSocket e p) = case eq of λ ()
  step-classify caller mode A.bindOK f s eq | (A.connectSocket e p) = case eq of λ ()
  step-classify caller mode A.bindOK f s eq | (A.localAddress e p) = case eq of λ ()
  step-classify caller mode A.bindOK f s eq | (A.updateAddress e p k) = case eq of λ ()
  step-classify caller mode A.bindOK f s eq | (A.forkHandler e p k) = case eq of λ ()
  step-classify caller mode A.bindOK f s eq | (A.connectedCommit e p k) = case eq of λ ()
  step-classify caller mode A.bindOK f s eq | (A.awaitResult e p k) = case eq of λ ()
  step-classify caller mode A.bindOK f s eq | (A.commitResult e k result) = case eq of λ ()
  step-classify caller mode A.bindOK f s eq | (A.waitingInbound e k) = case eq of λ ()
  step-classify caller mode A.bindOK f s eq | (A.closeError e err′) = case eq of λ ()
  step-classify caller mode A.bindOK f s eq | (A.removeError e err′) = case eq of λ ()
  step-classify caller mode A.bindOK f s eq | (A.complete result) = case eq of λ ()
  step-classify caller mode A.connectOK f s eq with A.pc f in pcEq
  ... | A.connectSocket e p = result-step eq (preserved {before = f} {after = record f { pc = A.localAddress e p }} refl (λ entry promise found → trans (cong promiseMark pcEq) found) (λ entry found → trans (cong entryMark pcEq) found))
  step-classify caller mode A.connectOK f s eq | A.selecting = case eq of λ ()
  step-classify caller mode A.connectOK f s eq | (A.count p) = case eq of λ ()
  step-classify caller mode A.connectOK f s eq | (A.allocatePromise e) = case eq of λ ()
  step-classify caller mode A.connectOK f s eq | (A.openSocket e p) = case eq of λ ()
  step-classify caller mode A.connectOK f s eq | (A.configureSocket e p) = case eq of λ ()
  step-classify caller mode A.connectOK f s eq | (A.bindSocket e p) = case eq of λ ()
  step-classify caller mode A.connectOK f s eq | (A.localAddress e p) = case eq of λ ()
  step-classify caller mode A.connectOK f s eq | (A.updateAddress e p k) = case eq of λ ()
  step-classify caller mode A.connectOK f s eq | (A.forkHandler e p k) = case eq of λ ()
  step-classify caller mode A.connectOK f s eq | (A.connectedCommit e p k) = case eq of λ ()
  step-classify caller mode A.connectOK f s eq | (A.awaitResult e p k) = case eq of λ ()
  step-classify caller mode A.connectOK f s eq | (A.commitResult e k result) = case eq of λ ()
  step-classify caller mode A.connectOK f s eq | (A.waitingInbound e k) = case eq of λ ()
  step-classify caller mode A.connectOK f s eq | (A.closeError e err′) = case eq of λ ()
  step-classify caller mode A.connectOK f s eq | (A.removeError e err′) = case eq of λ ()
  step-classify caller mode A.connectOK f s eq | (A.complete result) = case eq of λ ()
  step-classify caller mode (A.gotLocal local) f s eq with A.pc f in pcEq
  ... | A.localAddress e p = result-step eq (preserved {before = f} {after = record f { pc = A.updateAddress e p (connection local (A.peer (A.req f))) }} refl (λ entry promise found → trans (cong promiseMark pcEq) found) (λ entry found → trans (cong entryMark pcEq) found))
  step-classify caller mode (A.gotLocal local) f s eq | A.selecting = case eq of λ ()
  step-classify caller mode (A.gotLocal local) f s eq | (A.count p) = case eq of λ ()
  step-classify caller mode (A.gotLocal local) f s eq | (A.allocatePromise e) = case eq of λ ()
  step-classify caller mode (A.gotLocal local) f s eq | (A.openSocket e p) = case eq of λ ()
  step-classify caller mode (A.gotLocal local) f s eq | (A.configureSocket e p) = case eq of λ ()
  step-classify caller mode (A.gotLocal local) f s eq | (A.bindSocket e p) = case eq of λ ()
  step-classify caller mode (A.gotLocal local) f s eq | (A.connectSocket e p) = case eq of λ ()
  step-classify caller mode (A.gotLocal local) f s eq | (A.updateAddress e p k) = case eq of λ ()
  step-classify caller mode (A.gotLocal local) f s eq | (A.forkHandler e p k) = case eq of λ ()
  step-classify caller mode (A.gotLocal local) f s eq | (A.connectedCommit e p k) = case eq of λ ()
  step-classify caller mode (A.gotLocal local) f s eq | (A.awaitResult e p k) = case eq of λ ()
  step-classify caller mode (A.gotLocal local) f s eq | (A.commitResult e k result) = case eq of λ ()
  step-classify caller mode (A.gotLocal local) f s eq | (A.waitingInbound e k) = case eq of λ ()
  step-classify caller mode (A.gotLocal local) f s eq | (A.closeError e err′) = case eq of λ ()
  step-classify caller mode (A.gotLocal local) f s eq | (A.removeError e err′) = case eq of λ ()
  step-classify caller mode (A.gotLocal local) f s eq | (A.complete result) = case eq of λ ()
  step-classify caller mode A.updateLocalAddress f s eq with A.pc f in pcEq | mapCell (cm s)
  ... | A.updateAddress e p k | full m with A.updateLocal k m
  ...   | true , m′ = result-step eq (preserved {before = f} {after = record f { pc = A.forkHandler e p k }} refl (λ entry promise found → trans (cong promiseMark pcEq) found) (λ entry found → trans (cong entryMark pcEq) found))
  ...   | false , m′ = result-step eq (none-step refl refl refl)
  step-classify caller mode A.updateLocalAddress f s eq | A.selecting | _ = case eq of λ ()
  step-classify caller mode A.updateLocalAddress f s eq | (A.count p) | _ = case eq of λ ()
  step-classify caller mode A.updateLocalAddress f s eq | (A.allocatePromise e) | _ = case eq of λ ()
  step-classify caller mode A.updateLocalAddress f s eq | (A.openSocket e p) | _ = case eq of λ ()
  step-classify caller mode A.updateLocalAddress f s eq | (A.configureSocket e p) | _ = case eq of λ ()
  step-classify caller mode A.updateLocalAddress f s eq | (A.bindSocket e p) | _ = case eq of λ ()
  step-classify caller mode A.updateLocalAddress f s eq | (A.connectSocket e p) | _ = case eq of λ ()
  step-classify caller mode A.updateLocalAddress f s eq | (A.localAddress e p) | _ = case eq of λ ()
  step-classify caller mode A.updateLocalAddress f s eq | (A.forkHandler e p k) | _ = case eq of λ ()
  step-classify caller mode A.updateLocalAddress f s eq | (A.connectedCommit e p k) | _ = case eq of λ ()
  step-classify caller mode A.updateLocalAddress f s eq | (A.awaitResult e p k) | _ = case eq of λ ()
  step-classify caller mode A.updateLocalAddress f s eq | (A.commitResult e k result) | _ = case eq of λ ()
  step-classify caller mode A.updateLocalAddress f s eq | (A.waitingInbound e k) | _ = case eq of λ ()
  step-classify caller mode A.updateLocalAddress f s eq | (A.closeError e err′) | _ = case eq of λ ()
  step-classify caller mode A.updateLocalAddress f s eq | (A.removeError e err′) | _ = case eq of λ ()
  step-classify caller mode A.updateLocalAddress f s eq | (A.complete result) | _ = case eq of λ ()
  step-classify caller mode A.updateLocalAddress f s eq | (A.updateAddress e p k) | taken w = case eq of λ ()
  step-classify caller mode A.forkOK f s eq with A.pc f in pcEq | lookup (A.child (A.req f)) (handlers s)
  ... | A.forkHandler e p k | nothing = result-step eq (none-step refl refl refl)
  step-classify caller mode A.forkOK f s eq | A.selecting | _ = case eq of λ ()
  step-classify caller mode A.forkOK f s eq | (A.count p) | _ = case eq of λ ()
  step-classify caller mode A.forkOK f s eq | (A.allocatePromise e) | _ = case eq of λ ()
  step-classify caller mode A.forkOK f s eq | (A.openSocket e p) | _ = case eq of λ ()
  step-classify caller mode A.forkOK f s eq | (A.configureSocket e p) | _ = case eq of λ ()
  step-classify caller mode A.forkOK f s eq | (A.bindSocket e p) | _ = case eq of λ ()
  step-classify caller mode A.forkOK f s eq | (A.connectSocket e p) | _ = case eq of λ ()
  step-classify caller mode A.forkOK f s eq | (A.localAddress e p) | _ = case eq of λ ()
  step-classify caller mode A.forkOK f s eq | (A.updateAddress e p k) | _ = case eq of λ ()
  step-classify caller mode A.forkOK f s eq | (A.connectedCommit e p k) | _ = case eq of λ ()
  step-classify caller mode A.forkOK f s eq | (A.awaitResult e p k) | _ = case eq of λ ()
  step-classify caller mode A.forkOK f s eq | (A.commitResult e k result) | _ = case eq of λ ()
  step-classify caller mode A.forkOK f s eq | (A.waitingInbound e k) | _ = case eq of λ ()
  step-classify caller mode A.forkOK f s eq | (A.closeError e err′) | _ = case eq of λ ()
  step-classify caller mode A.forkOK f s eq | (A.removeError e err′) | _ = case eq of λ ()
  step-classify caller mode A.forkOK f s eq | (A.complete result) | _ = case eq of λ ()
  step-classify caller mode A.forkOK f s eq | (A.forkHandler e p k) | just h = case eq of λ ()
  step-classify caller mode A.commitConnected f s eq with A.pc f in pcEq
  ... | A.connectedCommit e p k with lookup e (entries (cm s)) in found
  ...   | nothing = case eq of λ ()
  ...   | just reservedOutbound = result-step eq (none-step refl refl refl)
  ...   | just (unnegotiated inbound _ _) = result-step eq (none-step refl refl refl)
  ...   | just old@(unnegotiated outbound _ _) = result-step eq (none-step refl refl refl)
  ...   | just old@(outboundUni _ _ _) = result-step eq (none-step refl refl refl)
  ...   | just old@(outboundDup _ _ _ _) = result-step eq (none-step refl refl refl)
  ...   | just old@(outboundIdle _ _ _ _) = result-step eq (none-step refl refl refl)
  ...   | just old@(inboundIdle _ _ _ _) = result-step eq (none-step refl refl refl)
  ...   | just old@(inboundActive _ _ _ _) = result-step eq (none-step refl refl refl)
  ...   | just old@(duplexActive _ _ _) = result-step eq (none-step refl refl refl)
  ...   | just old@(terminating _ _ _) = result-step eq (none-step refl refl refl)
  ...   | just old@(terminated _) = result-step eq (none-step refl refl refl)
  step-classify caller mode A.commitConnected f s eq | A.selecting = case eq of λ ()
  step-classify caller mode A.commitConnected f s eq | (A.count p) = case eq of λ ()
  step-classify caller mode A.commitConnected f s eq | (A.allocatePromise e) = case eq of λ ()
  step-classify caller mode A.commitConnected f s eq | (A.openSocket e p) = case eq of λ ()
  step-classify caller mode A.commitConnected f s eq | (A.configureSocket e p) = case eq of λ ()
  step-classify caller mode A.commitConnected f s eq | (A.bindSocket e p) = case eq of λ ()
  step-classify caller mode A.commitConnected f s eq | (A.connectSocket e p) = case eq of λ ()
  step-classify caller mode A.commitConnected f s eq | (A.localAddress e p) = case eq of λ ()
  step-classify caller mode A.commitConnected f s eq | (A.updateAddress e p k) = case eq of λ ()
  step-classify caller mode A.commitConnected f s eq | (A.forkHandler e p k) = case eq of λ ()
  step-classify caller mode A.commitConnected f s eq | (A.awaitResult e p k) = case eq of λ ()
  step-classify caller mode A.commitConnected f s eq | (A.commitResult e k result) = case eq of λ ()
  step-classify caller mode A.commitConnected f s eq | (A.waitingInbound e k) = case eq of λ ()
  step-classify caller mode A.commitConnected f s eq | (A.closeError e err′) = case eq of λ ()
  step-classify caller mode A.commitConnected f s eq | (A.removeError e err′) = case eq of λ ()
  step-classify caller mode A.commitConnected f s eq | (A.complete result) = case eq of λ ()
  step-classify caller mode A.readResult f s eq with A.pc f in pcEq
  ... | A.awaitResult e p k with lookup p (handshakeResults s)
  ...   | nothing = case eq of λ ()
  ...   | just result = result-step eq (none-step refl refl refl)
  step-classify caller mode A.readResult f s eq | A.selecting = case eq of λ ()
  step-classify caller mode A.readResult f s eq | (A.count p) = case eq of λ ()
  step-classify caller mode A.readResult f s eq | (A.allocatePromise e) = case eq of λ ()
  step-classify caller mode A.readResult f s eq | (A.openSocket e p) = case eq of λ ()
  step-classify caller mode A.readResult f s eq | (A.configureSocket e p) = case eq of λ ()
  step-classify caller mode A.readResult f s eq | (A.bindSocket e p) = case eq of λ ()
  step-classify caller mode A.readResult f s eq | (A.connectSocket e p) = case eq of λ ()
  step-classify caller mode A.readResult f s eq | (A.localAddress e p) = case eq of λ ()
  step-classify caller mode A.readResult f s eq | (A.updateAddress e p k) = case eq of λ ()
  step-classify caller mode A.readResult f s eq | (A.forkHandler e p k) = case eq of λ ()
  step-classify caller mode A.readResult f s eq | (A.connectedCommit e p k) = case eq of λ ()
  step-classify caller mode A.readResult f s eq | (A.commitResult e k result) = case eq of λ ()
  step-classify caller mode A.readResult f s eq | (A.waitingInbound e k) = case eq of λ ()
  step-classify caller mode A.readResult f s eq | (A.closeError e err′) = case eq of λ ()
  step-classify caller mode A.readResult f s eq | (A.removeError e err′) = case eq of λ ()
  step-classify caller mode A.readResult f s eq | (A.complete result) = case eq of λ ()
  step-classify caller mode A.commitHandshake f s eq with A.pc f in pcEq
  ... | A.commitResult e k (negotiated h flow) = success-step mode e k h flow f s eq
  ... | A.commitResult e k query = error-step e k handshakeQuery f s eq
  ... | A.commitResult e k (handlerError cls err) = error-step e k (handshakeError cls err) f s eq
  step-classify caller mode A.commitHandshake f s eq | A.selecting = case eq of λ ()
  step-classify caller mode A.commitHandshake f s eq | (A.count p) = case eq of λ ()
  step-classify caller mode A.commitHandshake f s eq | (A.allocatePromise e) = case eq of λ ()
  step-classify caller mode A.commitHandshake f s eq | (A.openSocket e p) = case eq of λ ()
  step-classify caller mode A.commitHandshake f s eq | (A.configureSocket e p) = case eq of λ ()
  step-classify caller mode A.commitHandshake f s eq | (A.bindSocket e p) = case eq of λ ()
  step-classify caller mode A.commitHandshake f s eq | (A.connectSocket e p) = case eq of λ ()
  step-classify caller mode A.commitHandshake f s eq | (A.localAddress e p) = case eq of λ ()
  step-classify caller mode A.commitHandshake f s eq | (A.updateAddress e p k) = case eq of λ ()
  step-classify caller mode A.commitHandshake f s eq | (A.forkHandler e p k) = case eq of λ ()
  step-classify caller mode A.commitHandshake f s eq | (A.connectedCommit e p k) = case eq of λ ()
  step-classify caller mode A.commitHandshake f s eq | (A.awaitResult e p k) = case eq of λ ()
  step-classify caller mode A.commitHandshake f s eq | (A.waitingInbound e k) = case eq of λ ()
  step-classify caller mode A.commitHandshake f s eq | (A.closeError e err′) = case eq of λ ()
  step-classify caller mode A.commitHandshake f s eq | (A.removeError e err′) = case eq of λ ()
  step-classify caller mode A.commitHandshake f s eq | (A.complete result) = case eq of λ ()
  step-classify caller mode A.waitNegotiated f s eq with A.pc f in pcEq
  ... | A.waitingInbound e k with lookup e (entries (cm s)) in found
  ...   | nothing = case eq of λ ()
  ...   | just st = choice-step A.waitNegotiated false e (C.waitCase k st) f s eq
  step-classify caller mode A.waitNegotiated f s eq | A.selecting = case eq of λ ()
  step-classify caller mode A.waitNegotiated f s eq | (A.count p) = case eq of λ ()
  step-classify caller mode A.waitNegotiated f s eq | (A.allocatePromise e) = case eq of λ ()
  step-classify caller mode A.waitNegotiated f s eq | (A.openSocket e p) = case eq of λ ()
  step-classify caller mode A.waitNegotiated f s eq | (A.configureSocket e p) = case eq of λ ()
  step-classify caller mode A.waitNegotiated f s eq | (A.bindSocket e p) = case eq of λ ()
  step-classify caller mode A.waitNegotiated f s eq | (A.connectSocket e p) = case eq of λ ()
  step-classify caller mode A.waitNegotiated f s eq | (A.localAddress e p) = case eq of λ ()
  step-classify caller mode A.waitNegotiated f s eq | (A.updateAddress e p k) = case eq of λ ()
  step-classify caller mode A.waitNegotiated f s eq | (A.forkHandler e p k) = case eq of λ ()
  step-classify caller mode A.waitNegotiated f s eq | (A.connectedCommit e p k) = case eq of λ ()
  step-classify caller mode A.waitNegotiated f s eq | (A.awaitResult e p k) = case eq of λ ()
  step-classify caller mode A.waitNegotiated f s eq | (A.commitResult e k result) = case eq of λ ()
  step-classify caller mode A.waitNegotiated f s eq | (A.closeError e err′) = case eq of λ ()
  step-classify caller mode A.waitNegotiated f s eq | (A.removeError e err′) = case eq of λ ()
  step-classify caller mode A.waitNegotiated f s eq | (A.complete result) = case eq of λ ()
  step-classify caller mode (A.failIO err) f s eq with A.pc f in pcEq
  ... | A.openSocket e p = result-step eq (none-step refl refl refl)
  ... | A.configureSocket e p = result-step eq (none-step refl refl refl)
  ... | A.bindSocket e p = result-step eq (none-step refl refl refl)
  ... | A.connectSocket e p = result-step eq (none-step refl refl refl)
  ... | A.localAddress e p = result-step eq (none-step refl refl refl)
  ... | A.forkHandler e p k = result-step eq (none-step refl refl refl)
  step-classify caller mode (A.failIO err) f s eq | A.selecting = case eq of λ ()
  step-classify caller mode (A.failIO err) f s eq | (A.count p) = case eq of λ ()
  step-classify caller mode (A.failIO err) f s eq | (A.allocatePromise e) = case eq of λ ()
  step-classify caller mode (A.failIO err) f s eq | (A.updateAddress e p k) = case eq of λ ()
  step-classify caller mode (A.failIO err) f s eq | (A.connectedCommit e p k) = case eq of λ ()
  step-classify caller mode (A.failIO err) f s eq | (A.awaitResult e p k) = case eq of λ ()
  step-classify caller mode (A.failIO err) f s eq | (A.commitResult e k result) = case eq of λ ()
  step-classify caller mode (A.failIO err) f s eq | (A.waitingInbound e k) = case eq of λ ()
  step-classify caller mode (A.failIO err) f s eq | (A.closeError e err′) = case eq of λ ()
  step-classify caller mode (A.failIO err) f s eq | (A.removeError e err′) = case eq of λ ()
  step-classify caller mode (A.failIO err) f s eq | (A.complete result) = case eq of λ ()
  step-classify caller mode A.closeOK f s eq with A.pc f in pcEq
  ... | A.closeError e err = result-step eq (none-step refl refl refl)
  step-classify caller mode A.closeOK f s eq | A.selecting = case eq of λ ()
  step-classify caller mode A.closeOK f s eq | (A.count p) = case eq of λ ()
  step-classify caller mode A.closeOK f s eq | (A.allocatePromise e) = case eq of λ ()
  step-classify caller mode A.closeOK f s eq | (A.openSocket e p) = case eq of λ ()
  step-classify caller mode A.closeOK f s eq | (A.configureSocket e p) = case eq of λ ()
  step-classify caller mode A.closeOK f s eq | (A.bindSocket e p) = case eq of λ ()
  step-classify caller mode A.closeOK f s eq | (A.connectSocket e p) = case eq of λ ()
  step-classify caller mode A.closeOK f s eq | (A.localAddress e p) = case eq of λ ()
  step-classify caller mode A.closeOK f s eq | (A.updateAddress e p k) = case eq of λ ()
  step-classify caller mode A.closeOK f s eq | (A.forkHandler e p k) = case eq of λ ()
  step-classify caller mode A.closeOK f s eq | (A.connectedCommit e p k) = case eq of λ ()
  step-classify caller mode A.closeOK f s eq | (A.awaitResult e p k) = case eq of λ ()
  step-classify caller mode A.closeOK f s eq | (A.commitResult e k result) = case eq of λ ()
  step-classify caller mode A.closeOK f s eq | (A.waitingInbound e k) = case eq of λ ()
  step-classify caller mode A.closeOK f s eq | (A.removeError e err′) = case eq of λ ()
  step-classify caller mode A.closeOK f s eq | (A.complete result) = case eq of λ ()
  step-classify caller mode (A.closeFailed err) f s eq with A.pc f in pcEq
  ... | A.closeError e _ = result-step eq (none-step refl refl refl)
  step-classify caller mode (A.closeFailed err) f s eq | A.selecting = case eq of λ ()
  step-classify caller mode (A.closeFailed err) f s eq | (A.count p) = case eq of λ ()
  step-classify caller mode (A.closeFailed err) f s eq | (A.allocatePromise e) = case eq of λ ()
  step-classify caller mode (A.closeFailed err) f s eq | (A.openSocket e p) = case eq of λ ()
  step-classify caller mode (A.closeFailed err) f s eq | (A.configureSocket e p) = case eq of λ ()
  step-classify caller mode (A.closeFailed err) f s eq | (A.bindSocket e p) = case eq of λ ()
  step-classify caller mode (A.closeFailed err) f s eq | (A.connectSocket e p) = case eq of λ ()
  step-classify caller mode (A.closeFailed err) f s eq | (A.localAddress e p) = case eq of λ ()
  step-classify caller mode (A.closeFailed err) f s eq | (A.updateAddress e p k) = case eq of λ ()
  step-classify caller mode (A.closeFailed err) f s eq | (A.forkHandler e p k) = case eq of λ ()
  step-classify caller mode (A.closeFailed err) f s eq | (A.connectedCommit e p k) = case eq of λ ()
  step-classify caller mode (A.closeFailed err) f s eq | (A.awaitResult e p k) = case eq of λ ()
  step-classify caller mode (A.closeFailed err) f s eq | (A.commitResult e k result) = case eq of λ ()
  step-classify caller mode (A.closeFailed err) f s eq | (A.waitingInbound e k) = case eq of λ ()
  step-classify caller mode (A.closeFailed err) f s eq | (A.removeError e err′) = case eq of λ ()
  step-classify caller mode (A.closeFailed err) f s eq | (A.complete result) = case eq of λ ()
  step-classify caller mode A.removeReservation f s eq with A.pc f in pcEq | mapCell (cm s)
  ... | A.removeError e err | full m = result-step eq (none-step refl refl refl)
  step-classify caller mode A.removeReservation f s eq | A.selecting | _ = case eq of λ ()
  step-classify caller mode A.removeReservation f s eq | (A.count p) | _ = case eq of λ ()
  step-classify caller mode A.removeReservation f s eq | (A.allocatePromise e) | _ = case eq of λ ()
  step-classify caller mode A.removeReservation f s eq | (A.openSocket e p) | _ = case eq of λ ()
  step-classify caller mode A.removeReservation f s eq | (A.configureSocket e p) | _ = case eq of λ ()
  step-classify caller mode A.removeReservation f s eq | (A.bindSocket e p) | _ = case eq of λ ()
  step-classify caller mode A.removeReservation f s eq | (A.connectSocket e p) | _ = case eq of λ ()
  step-classify caller mode A.removeReservation f s eq | (A.localAddress e p) | _ = case eq of λ ()
  step-classify caller mode A.removeReservation f s eq | (A.updateAddress e p k) | _ = case eq of λ ()
  step-classify caller mode A.removeReservation f s eq | (A.forkHandler e p k) | _ = case eq of λ ()
  step-classify caller mode A.removeReservation f s eq | (A.connectedCommit e p k) | _ = case eq of λ ()
  step-classify caller mode A.removeReservation f s eq | (A.awaitResult e p k) | _ = case eq of λ ()
  step-classify caller mode A.removeReservation f s eq | (A.commitResult e k result) | _ = case eq of λ ()
  step-classify caller mode A.removeReservation f s eq | (A.waitingInbound e k) | _ = case eq of λ ()
  step-classify caller mode A.removeReservation f s eq | (A.closeError e err′) | _ = case eq of λ ()
  step-classify caller mode A.removeReservation f s eq | (A.complete result) | _ = case eq of λ ()
  step-classify caller mode A.removeReservation f s eq | (A.removeError e err′) | taken w = case eq of λ ()
  step-classify caller mode A.returnResult f s ()

step-classify : ∀ caller mode action f s {out} → A.step caller mode action f s ≡ just out → Step action f s (proj₁ out)
step-classify = Source.step-classify

import ConnectionManagement.Rules.OutboundRelease as R

private
 acquire-effect : ∀ caller action before {after} → O.advanceAcquire caller action before ≡ just after → Effect before after
 acquire-effect caller A.returnResult before actual with lookup caller (O.acquiring before)
 ... | nothing = case actual of λ ()
 ... | just f with A.pc f
 ...   | A.complete result = subst (Effect before) (just-injective actual) (removed caller refl)
 ...   | A.selecting = case actual of λ ()
 ...   | A.count next = case actual of λ ()
 ...   | A.allocatePromise e = case actual of λ ()
 ...   | A.openSocket e p = case actual of λ ()
 ...   | A.configureSocket e p = case actual of λ ()
 ...   | A.bindSocket e p = case actual of λ ()
 ...   | A.connectSocket e p = case actual of λ ()
 ...   | A.localAddress e p = case actual of λ ()
 ...   | A.updateAddress e p k = case actual of λ ()
 ...   | A.forkHandler e p k = case actual of λ ()
 ...   | A.connectedCommit e p k = case actual of λ ()
 ...   | A.awaitResult e p k = case actual of λ ()
 ...   | A.commitResult e k result = case actual of λ ()
 ...   | A.waitingInbound e k = case actual of λ ()
 ...   | A.closeError e err = case actual of λ ()
 ...   | A.removeError e err = case actual of λ ()
 acquire-effect caller (A.select selected) before actual with lookup caller (O.acquiring before) in owned
 ... | nothing = case actual of λ ()
 ... | just f with A.step caller (M.responder (O.core before)) (A.select selected) f (M.world (O.core before)) in stepped
 ...   | nothing = case actual of λ ()
 ...   | just (f′ , world′) = subst (Effect before) (just-injective actual) (advanced caller (A.select selected) f f′ owned stepped refl)
 acquire-effect caller A.readCounters before actual with lookup caller (O.acquiring before) in owned
 ... | nothing = case actual of λ ()
 ... | just f with A.step caller (M.responder (O.core before)) A.readCounters f (M.world (O.core before)) in stepped
 ...   | nothing = case actual of λ ()
 ...   | just (f′ , world′) = subst (Effect before) (just-injective actual) (advanced caller A.readCounters f f′ owned stepped refl)
 acquire-effect caller A.newPromise before actual with lookup caller (O.acquiring before) in owned
 ... | nothing = case actual of λ ()
 ... | just f with A.step caller (M.responder (O.core before)) A.newPromise f (M.world (O.core before)) in stepped
 ...   | nothing = case actual of λ ()
 ...   | just (f′ , world′) = subst (Effect before) (just-injective actual) (advanced caller A.newPromise f f′ owned stepped refl)
 acquire-effect caller A.openOK before actual with lookup caller (O.acquiring before) in owned
 ... | nothing = case actual of λ ()
 ... | just f with A.step caller (M.responder (O.core before)) A.openOK f (M.world (O.core before)) in stepped
 ...   | nothing = case actual of λ ()
 ...   | just (f′ , world′) = subst (Effect before) (just-injective actual) (advanced caller A.openOK f f′ owned stepped refl)
 acquire-effect caller A.configureOK before actual with lookup caller (O.acquiring before) in owned
 ... | nothing = case actual of λ ()
 ... | just f with A.step caller (M.responder (O.core before)) A.configureOK f (M.world (O.core before)) in stepped
 ...   | nothing = case actual of λ ()
 ...   | just (f′ , world′) = subst (Effect before) (just-injective actual) (advanced caller A.configureOK f f′ owned stepped refl)
 acquire-effect caller A.bindOK before actual with lookup caller (O.acquiring before) in owned
 ... | nothing = case actual of λ ()
 ... | just f with A.step caller (M.responder (O.core before)) A.bindOK f (M.world (O.core before)) in stepped
 ...   | nothing = case actual of λ ()
 ...   | just (f′ , world′) = subst (Effect before) (just-injective actual) (advanced caller A.bindOK f f′ owned stepped refl)
 acquire-effect caller A.connectOK before actual with lookup caller (O.acquiring before) in owned
 ... | nothing = case actual of λ ()
 ... | just f with A.step caller (M.responder (O.core before)) A.connectOK f (M.world (O.core before)) in stepped
 ...   | nothing = case actual of λ ()
 ...   | just (f′ , world′) = subst (Effect before) (just-injective actual) (advanced caller A.connectOK f f′ owned stepped refl)
 acquire-effect caller (A.gotLocal address) before actual with lookup caller (O.acquiring before) in owned
 ... | nothing = case actual of λ ()
 ... | just f with A.step caller (M.responder (O.core before)) (A.gotLocal address) f (M.world (O.core before)) in stepped
 ...   | nothing = case actual of λ ()
 ...   | just (f′ , world′) = subst (Effect before) (just-injective actual) (advanced caller (A.gotLocal address) f f′ owned stepped refl)
 acquire-effect caller A.updateLocalAddress before actual with lookup caller (O.acquiring before) in owned
 ... | nothing = case actual of λ ()
 ... | just f with A.step caller (M.responder (O.core before)) A.updateLocalAddress f (M.world (O.core before)) in stepped
 ...   | nothing = case actual of λ ()
 ...   | just (f′ , world′) = subst (Effect before) (just-injective actual) (advanced caller A.updateLocalAddress f f′ owned stepped refl)
 acquire-effect caller A.forkOK before actual with lookup caller (O.acquiring before) in owned
 ... | nothing = case actual of λ ()
 ... | just f with A.step caller (M.responder (O.core before)) A.forkOK f (M.world (O.core before)) in stepped
 ...   | nothing = case actual of λ ()
 ...   | just (f′ , world′) = subst (Effect before) (just-injective actual) (advanced caller A.forkOK f f′ owned stepped refl)
 acquire-effect caller A.commitConnected before actual with lookup caller (O.acquiring before) in owned
 ... | nothing = case actual of λ ()
 ... | just f with A.step caller (M.responder (O.core before)) A.commitConnected f (M.world (O.core before)) in stepped
 ...   | nothing = case actual of λ ()
 ...   | just (f′ , world′) = subst (Effect before) (just-injective actual) (advanced caller A.commitConnected f f′ owned stepped refl)
 acquire-effect caller A.readResult before actual with lookup caller (O.acquiring before) in owned
 ... | nothing = case actual of λ ()
 ... | just f with A.step caller (M.responder (O.core before)) A.readResult f (M.world (O.core before)) in stepped
 ...   | nothing = case actual of λ ()
 ...   | just (f′ , world′) = subst (Effect before) (just-injective actual) (advanced caller A.readResult f f′ owned stepped refl)
 acquire-effect caller A.commitHandshake before actual with lookup caller (O.acquiring before) in owned
 ... | nothing = case actual of λ ()
 ... | just f with A.step caller (M.responder (O.core before)) A.commitHandshake f (M.world (O.core before)) in stepped
 ...   | nothing = case actual of λ ()
 ...   | just (f′ , world′) = subst (Effect before) (just-injective actual) (advanced caller A.commitHandshake f f′ owned stepped refl)
 acquire-effect caller (A.failIO err) before actual with lookup caller (O.acquiring before) in owned
 ... | nothing = case actual of λ ()
 ... | just f with A.step caller (M.responder (O.core before)) (A.failIO err) f (M.world (O.core before)) in stepped
 ...   | nothing = case actual of λ ()
 ...   | just (f′ , world′) = subst (Effect before) (just-injective actual) (advanced caller (A.failIO err) f f′ owned stepped refl)
 acquire-effect caller (A.closeFailed err) before actual with lookup caller (O.acquiring before) in owned
 ... | nothing = case actual of λ ()
 ... | just f with A.step caller (M.responder (O.core before)) (A.closeFailed err) f (M.world (O.core before)) in stepped
 ...   | nothing = case actual of λ ()
 ...   | just (f′ , world′) = subst (Effect before) (just-injective actual) (advanced caller (A.closeFailed err) f f′ owned stepped refl)
 acquire-effect caller A.closeOK before actual with lookup caller (O.acquiring before) in owned
 ... | nothing = case actual of λ ()
 ... | just f with A.step caller (M.responder (O.core before)) A.closeOK f (M.world (O.core before)) in stepped
 ...   | nothing = case actual of λ ()
 ...   | just (f′ , world′) = subst (Effect before) (just-injective actual) (advanced caller A.closeOK f f′ owned stepped refl)
 acquire-effect caller A.removeReservation before actual with lookup caller (O.acquiring before) in owned
 ... | nothing = case actual of λ ()
 ... | just f with A.step caller (M.responder (O.core before)) A.removeReservation f (M.world (O.core before)) in stepped
 ...   | nothing = case actual of λ ()
 ...   | just (f′ , world′) = subst (Effect before) (just-injective actual) (advanced caller A.removeReservation f f′ owned stepped refl)
 acquire-effect caller A.waitNegotiated before actual with lookup caller (O.acquiring before) in owned
 ... | nothing = case actual of λ ()
 ... | just f with A.step caller (M.responder (O.core before)) A.waitNegotiated f (M.world (O.core before)) in stepped
 ...   | nothing = case actual of λ ()
 ...   | just (f′ , world′) = subst (Effect before) (just-injective actual) (advanced caller A.waitNegotiated f f′ owned stepped refl)
 release-effect : ∀ caller action before {after} → O.advanceRelease caller action before ≡ just after → Effect before after
 release-effect caller R.returnResult before actual with lookup caller (O.releasing before)
 ... | nothing = case actual of λ ()
 ... | just f with R.pc f
 ...   | R.complete result = subst (Effect before) (just-injective actual) (same refl)
 ...   | R.transaction = case actual of λ ()
 ...   | R.check condition next = case actual of λ ()
 ...   | R.count next = case actual of λ ()
 ...   | R.armTimer e w = case actual of λ ()
 ...   | R.waitIdle e w = case actual of λ ()
 ...   | R.timeoutWrite e w = case actual of λ ()
 ...   | R.cancel w next = case actual of λ ()
 ...   | R.delivering w next = case actual of λ ()
 ...   | R.prune choices result = case actual of λ ()
 release-effect caller R.transactionStep before actual with lookup caller (O.releasing before) | O.canDeliver R.transactionStep before
 ... | nothing | _ = case actual of λ ()
 ... | just f | false = case actual of λ ()
 ... | just f | true with R.step (M.promotionHardLimit (O.core before)) R.transactionStep f (M.world (O.core before))
 ...   | nothing = case actual of λ ()
 ...   | just (f′ , world′) = subst (Effect before) (just-injective actual) (same refl)
 release-effect caller R.checkAssertion before actual with lookup caller (O.releasing before) | O.canDeliver R.checkAssertion before
 ... | nothing | _ = case actual of λ ()
 ... | just f | false = case actual of λ ()
 ... | just f | true with R.step (M.promotionHardLimit (O.core before)) R.checkAssertion f (M.world (O.core before))
 ...   | nothing = case actual of λ ()
 ...   | just (f′ , world′) = subst (Effect before) (just-injective actual) (same refl)
 release-effect caller R.readCounters before actual with lookup caller (O.releasing before) | O.canDeliver R.readCounters before
 ... | nothing | _ = case actual of λ ()
 ... | just f | false = case actual of λ ()
 ... | just f | true with R.step (M.promotionHardLimit (O.core before)) R.readCounters f (M.world (O.core before))
 ...   | nothing = case actual of λ ()
 ...   | just (f′ , world′) = subst (Effect before) (just-injective actual) (same refl)
 release-effect caller R.registerTimer before actual with lookup caller (O.releasing before) | O.canDeliver R.registerTimer before
 ... | nothing | _ = case actual of λ ()
 ... | just f | false = case actual of λ ()
 ... | just f | true with R.step (M.promotionHardLimit (O.core before)) R.registerTimer f (M.world (O.core before))
 ...   | nothing = case actual of λ ()
 ...   | just (f′ , world′) = subst (Effect before) (just-injective actual) (same refl)
 release-effect caller R.expireTimer before actual with lookup caller (O.releasing before) | O.canDeliver R.expireTimer before
 ... | nothing | _ = case actual of λ ()
 ... | just f | false = case actual of λ ()
 ... | just f | true with R.step (M.promotionHardLimit (O.core before)) R.expireTimer f (M.world (O.core before))
 ...   | nothing = case actual of λ ()
 ...   | just (f′ , world′) = subst (Effect before) (just-injective actual) (same refl)
 release-effect caller R.selectWakeup before actual with lookup caller (O.releasing before) | O.canDeliver R.selectWakeup before
 ... | nothing | _ = case actual of λ ()
 ... | just f | false = case actual of λ ()
 ... | just f | true with R.step (M.promotionHardLimit (O.core before)) R.selectWakeup f (M.world (O.core before))
 ...   | nothing = case actual of λ ()
 ...   | just (f′ , world′) = subst (Effect before) (just-injective actual) (same refl)
 release-effect caller R.commitTimeout before actual with lookup caller (O.releasing before) | O.canDeliver R.commitTimeout before
 ... | nothing | _ = case actual of λ ()
 ... | just f | false = case actual of λ ()
 ... | just f | true with R.step (M.promotionHardLimit (O.core before)) R.commitTimeout f (M.world (O.core before))
 ...   | nothing = case actual of λ ()
 ...   | just (f′ , world′) = subst (Effect before) (just-injective actual) (same refl)
 release-effect caller R.requestCancellation before actual with lookup caller (O.releasing before) | O.canDeliver R.requestCancellation before
 ... | nothing | _ = case actual of λ ()
 ... | just f | false = case actual of λ ()
 ... | just f | true with R.step (M.promotionHardLimit (O.core before)) R.requestCancellation f (M.world (O.core before))
 ...   | nothing = case actual of λ ()
 ...   | just (f′ , world′) = subst (Effect before) (just-injective actual) (same refl)
 release-effect caller (R.transactionPruning scores) before actual with lookup caller (O.releasing before) | O.canDeliver (R.transactionPruning scores) before
 ... | nothing | _ = case actual of λ ()
 ... | just f | false = case actual of λ ()
 ... | just f | true with R.step (M.promotionHardLimit (O.core before)) (R.transactionPruning scores) f (M.world (O.core before))
 ...   | nothing = case actual of λ ()
 ...   | just (f′ , world′) = subst (Effect before) (just-injective actual) (same refl)
 release-effect caller (R.cancellationDelivered worker) before actual with lookup caller (O.releasing before) | O.canDeliver (R.cancellationDelivered worker) before
 ... | nothing | _ = case actual of λ ()
 ... | just f | false = case actual of λ ()
 ... | just f | true with R.step (M.promotionHardLimit (O.core before)) (R.cancellationDelivered worker) f (M.world (O.core before))
 ...   | nothing = case actual of λ ()
 ...   | just (f′ , world′) = subst (Effect before) (just-injective actual) (same refl)

-- Preserve the actual active source operation under every outbound dispatcher arm.
advance-effect : ∀ action before {after} → O.advance action before ≡ just after → Effect before after
advance-effect (O.inbound action) before actual with M.advance action (O.core before)
... | nothing = case actual of λ ()
... | just core′ = subst (Effect before) (just-injective actual) (same refl)
advance-effect (O.beginAcquire caller request) before actual with lookup caller (O.acquiring before) | lookup caller (O.releasing before)
... | just _ | _ = case actual of λ ()
... | nothing | just _ = case actual of λ ()
... | nothing | nothing = subst (Effect before) (just-injective actual) (begun caller request refl)
advance-effect (O.acquire caller action) before actual = acquire-effect caller action before actual
advance-effect (O.beginRelease caller key) before actual with lookup caller (O.acquiring before) | lookup caller (O.releasing before)
... | just _ | _ = case actual of λ ()
... | nothing | just _ = case actual of λ ()
... | nothing | nothing = subst (Effect before) (just-injective actual) (same refl)
advance-effect (O.release caller action) before actual = release-effect caller action before actual
