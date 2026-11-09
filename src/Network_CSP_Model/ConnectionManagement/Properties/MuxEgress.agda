{-# OPTIONS --guardedness #-}

-- Local observations of the M1 batch accounting kernel. These certify actual
-- model steps; grant ledgers, bearer execution and Haskell refinement are not
-- conclusions of the component lemmas.
module ConnectionManagement.Properties.MuxEgress where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Integer using (ℤ; +_; -[1+_]; _≤_; +≤+)
import Data.Integer as Int
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.All.Properties as AllProperties
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; zero; suc; z≤n)
import Data.Nat as Nat
import Data.Nat.Properties as NatProperties
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans; sym; subst)
open import Class.DecEq using (DecEq; _≟_)
open import Class.DecEq.Instances using (DecEq-ℕ)
open import ConnectionManagement.Store using (Store; lookup; put; delete)
open import ConnectionManagement.Properties.Entries using (lookup-put)
open import ConnectionManagement.Properties.Stores using (put-values; put-unique; UniqueKeys; lookup-put-other; apart-lookup; lookup-head)
import ConnectionManagement.Rules.MuxEgress as Model

-- Boolean zero is the signed source-cell test, not truncated subtraction.
zero-observation : ∀ n → Model.isZero n ≡ true → n ≡ + 0
zero-observation n actual with n Int.≟ + 0
... | yes same = same
... | no _ = case actual of λ ()
positive-result : ∀ n → Model.positive n ≡ true → Σ ℕ (λ k → n ≡ + (suc k))
positive-result (+ zero) actual = case actual of λ ()
positive-result (+ (suc n)) actual = n , refl
positive-result -[1+ n ] actual = case actual of λ ()

module Kernel (Key : Set) ⦃ keyEquality : DecEq Key ⦄ where
 module E = Model.Kernel Key

 -- A true readiness query supplies the actual wanton and its persistent cell.
 record ProtocolReady (w : ℕ) (s : E.State) : Set where
  constructor ready-protocol
  field wanton : E.Wanton
        cell : E.Cell
        wanton-found : lookup w (E.wantons s) ≡ just wanton
        cell-found : lookup (E.key wanton) (E.cells s) ≡ just cell
        want-empty : E.payload wanton ≡ 0
        held-zero : E.keyHeld cell ≡ + 0
 protocol-ready : ∀ w s → E.protocolReady w s ≡ true → ProtocolReady w s
 protocol-ready w s actual with lookup w (E.wantons s) in found
 ... | nothing = case actual of λ ()
 ... | just f with lookup (E.key f) (E.cells s) in cellFound | E.payload f in empty
 ...   | nothing | _ = case actual of λ ()
 ...   | just c | zero = ready-protocol f c found cellFound empty (zero-observation (E.keyHeld c) actual)
 ...   | just c | suc _ = case actual of λ ()

 record DrainReady (s : E.State) : Set where
  constructor ready-drain
  field queues-empty : E.queuesEmpty (E.queues s) ≡ true
        held-zero : E.runHeld s ≡ + 0
 drain-ready : ∀ s → E.drainReady s ≡ true → DrainReady s
 drain-ready s actual with E.queuesEmpty (E.queues s) in empty | Model.isZero (E.runHeld s) in held
 ... | true | true = ready-drain empty (zero-observation (E.runHeld s) held)
 ... | true | false = case actual of λ ()
 ... | false | _ = case actual of λ ()

 -- Failure marks only this captured batch. In particular it cannot manufacture
 -- successful sent-byte accounting, held release, or a grant refund.
 record Failure (ident : ℕ) (before after : E.State) : Set where
  constructor failed-batch
  field captured : E.Batch
        found : lookup ident (E.batches before) ≡ just captured
        origin-phase : E.phase captured ≡ E.building ⊎ E.phase captured ≡ E.ready
        after-shape : after ≡ E.failUpdate ident captured (lookup ident (E.waits before)) before
        cells-same : E.cells after ≡ E.cells before
        held-same : E.runHeld after ≡ E.runHeld before
        wantons-same : E.wantons after ≡ E.wantons before
        queues-same : E.queues after ≡ E.queues before
 failure : ∀ ident before {after} → E.step (E.writeFailed ident) before ≡ just after → Failure ident before after
 failure ident before actual with lookup ident (E.batches before) in found
 ... | nothing = case actual of λ ()
 ... | just b with E.phase b in phase | E.failable (lookup ident (E.waits before))
 ...   | E.building | _ = case just-injective actual of λ { refl → failed-batch b found (inj₁ phase) refl refl refl refl refl }
 ...   | E.ready | true = case just-injective actual of λ { refl → failed-batch b found (inj₂ phase) refl refl refl refl refl }
 ...   | E.ready | false = case actual of λ ()
 ...   | E.failed | _ = case actual of λ ()
 ...   | E.written | _ = case actual of λ ()

 -- Successful accounting observes a ready, unconsumed batch and the actual
 -- all-member accounting transaction. It does not assert a muxer body return.
 record Write (ident : ℕ) (before after : E.State) : Set where
  constructor wrote-batch
  field captured : E.Batch
        cellsAfter : Store Key E.Cell
        found : lookup ident (E.batches before) ≡ just captured
        ready-before : E.phase captured ≡ E.ready
        no-pending : E.pending captured ≡ nothing
        held-positive : Model.positive (E.runHeld before) ≡ true
        write-enabled-wait : Model.writeEnabled (Model.modeOf (E.layout before) (E.lane captured)) (lookup ident (E.waits before)) ≡ true
        actual-account : E.account (E.members captured) (E.cells before) ≡ just cellsAfter
        after-shape : after ≡ record before
          { cells = cellsAfter; runHeld = E.runHeld before Int.- + 1
          ; batches = put ident (record captured { phase = E.written }) (E.batches before)
          ; waits = delete ident (E.waits before) }
 write : ∀ ident before {after} → E.step (E.writeAccount ident) before ≡ just after → Write ident before after
 write ident before actual with lookup ident (E.batches before) in found
 ... | nothing = case actual of λ ()
 ... | just b with E.phase b in phase | E.pending b in pending | Model.positive (E.runHeld before) in held |
   Model.writeEnabled (Model.modeOf (E.layout before) (E.lane b)) (lookup ident (E.waits before)) in enabled
 ...   | E.ready | nothing | true | true with E.account (E.members b) (E.cells before) in accounted
 ...     | nothing = case actual of λ ()
 ...     | just cs = case just-injective actual of λ { refl → wrote-batch b cs found phase pending held enabled accounted refl }
 write ident before actual | just b | E.building | _ | _ | _ = case actual of λ ()
 write ident before actual | just b | E.ready | just _ | _ | _ = case actual of λ ()
 write ident before actual | just b | E.ready | nothing | false | _ = case actual of λ ()
 write ident before actual | just b | E.ready | nothing | true | false = case actual of λ ()
 write ident before actual | just b | E.failed | _ | _ | _ = case actual of λ ()
 write ident before actual | just b | E.written | _ | _ | _ = case actual of λ ()

 -- Written and failed historical batches cannot be mistaken for a fresh write.
 written-refused : ∀ ident s b → lookup ident (E.batches s) ≡ just b → E.phase b ≡ E.written →
  E.step (E.writeAccount ident) s ≡ nothing
 written-refused ident s b found phase rewrite found | phase = refl
 failed-refused : ∀ ident s b → lookup ident (E.batches s) ≡ just b → E.phase b ≡ E.failed →
  E.step (E.writeAccount ident) s ≡ nothing
 failed-refused ident s b found phase rewrite found | phase = refl

 -- A repeat refusal follows the actual output, without a caller-supplied phase.
 write-once : ∀ ident before {after} → E.step (E.writeAccount ident) before ≡ just after →
  E.step (E.writeAccount ident) after ≡ nothing
 write-once ident before actual with write ident before actual
 ... | wrote-batch b cs found phase pending held enabled accounted refl =
  written-refused ident (record before
   { cells = cs; runHeld = E.runHeld before Int.- + 1
   ; batches = put ident (record b { phase = E.written }) (E.batches before)
   ; waits = delete ident (E.waits before) })
   (record b { phase = E.written })
   (lookup-put ident (record b { phase = E.written }) (E.batches before)) refl
 failure-not-write : ∀ ident before {after} → E.step (E.writeFailed ident) before ≡ just after →
  E.step (E.writeAccount ident) after ≡ nothing
 failure-not-write ident before actual with failure ident before actual
 ... | failed-batch b found phase refl sameCells sameHeld sameWantons sameQueues =
  failed-refused ident (E.failUpdate ident b (lookup ident (E.waits before)) before)
   (record b { phase = E.failed })
   (lookup-put ident (record b { phase = E.failed }) (E.batches before)) refl

 -- M4 wait stages change only the batch's wait entry and the write lock;
 -- batches, cells, held counts, queues and wantons are untouched.
 advance-shape : ∀ ident a s {t} → E.step (E.advance ident a) s ≡ just t →
  Σ (Store ℕ Model.Wait) (λ W → Σ (Maybe ℕ) (λ L → t ≡ record s { waits = W; lockHolder = L }))
 advance-shape ident a s actual with lookup ident (E.batches s)
 ... | nothing = case actual of λ ()
 ... | just b with E.phase b | Model.nextWait (Model.modeOf (E.layout s) (E.lane b)) (lookup ident (E.waits s)) a
 ...   | E.ready | just w with a | E.lockHolder s
 ...     | Model.takeLock | just _ = case actual of λ ()
 ...     | Model.takeLock | nothing = case just-injective actual of λ { refl → _ , _ , refl }
 ...     | Model.returnWrite | _ = case just-injective actual of λ { refl → _ , _ , refl }
 ...     | Model.openGate | _ = case just-injective actual of λ { refl → _ , _ , refl }
 ...     | Model.grantFast | _ = case just-injective actual of λ { refl → _ , _ , refl }
 ...     | Model.queueRequest | _ = case just-injective actual of λ { refl → _ , _ , refl }
 ...     | Model.armTimer | _ = case just-injective actual of λ { refl → _ , _ , refl }
 ...     | Model.grantQueued | _ = case just-injective actual of λ { refl → _ , _ , refl }
 ...     | Model.disarmTimer | _ = case just-injective actual of λ { refl → _ , _ , refl }
 advance-shape ident a s actual | just b | E.ready | nothing = case actual of λ ()
 advance-shape ident a s actual | just b | E.building | _ = case actual of λ ()
 advance-shape ident a s actual | just b | E.failed | _ = case actual of λ ()
 advance-shape ident a s actual | just b | E.written | _ = case actual of λ ()

 -- A finite executable path records every actual kernel step. Concrete
 -- controls can reuse this variable-state proof instead of expanding nested
 -- transition constructors at closed snapshots.
 data Runs : E.State → List E.Action → E.State → Set where
  stop : ∀ {s} → Runs s [] s
  more : ∀ {s t u a as} → E.step a s ≡ just t → Runs t as u → Runs s (a ∷ as) u
 execute : List E.Action → E.State → Maybe E.State
 execute [] s = just s
 execute (a ∷ as) s with E.step a s
 ... | nothing = nothing
 ... | just t = execute as t
 execute-runs : ∀ as s {t} → execute as s ≡ just t → Runs s as t
 execute-runs [] s actual = case just-injective actual of λ { refl → stop }
 execute-runs (a ∷ as) s actual with E.step a s in advanced
 ... | nothing = case actual of λ ()
 ... | just next = more advanced (execute-runs as next actual)

 -- Store-fold update laws are independent of protocol/handler runtime. They
 -- count each historical batch row once and need no unique queue-pointer axiom.
 count : (E.Batch → ℕ) → Store ℕ E.Batch → ℕ
 count f [] = 0
 count f ((_ , b) ∷ bs) = f b Nat.+ count f bs
 count-put-same : ∀ f ident replacement bs old → lookup ident bs ≡ just old →
  f replacement ≡ f old → count f (put ident replacement bs) ≡ count f bs
 count-put-same f ident replacement [] old found same = case found of λ ()
 count-put-same f ident replacement ((q , b) ∷ bs) old found same with ident ≟ q
 ... | yes _ rewrite just-injective found | same = refl
 ... | no _ = cong (λ n → f b Nat.+ n) (count-put-same f ident replacement bs old found same)
 count-put-fresh : ∀ f ident replacement bs → lookup ident bs ≡ nothing →
  count f (put ident replacement bs) ≡ count f bs Nat.+ f replacement
 count-put-fresh f ident replacement [] found = NatProperties.+-identityʳ (f replacement)
 count-put-fresh f ident replacement ((q , b) ∷ bs) found with ident ≟ q
 ... | yes _ = case found of λ ()
 ... | no _ = trans (cong (λ n → f b Nat.+ n) (count-put-fresh f ident replacement bs found))
  (sym (NatProperties.+-assoc (f b) (count f bs) (f replacement)))
 count-put-minus : ∀ f ident replacement bs old → lookup ident bs ≡ just old →
  f old ≡ suc (f replacement) → count f bs ≡ suc (count f (put ident replacement bs))
 count-put-minus f ident replacement [] old found minus = case found of λ ()
 count-put-minus f ident replacement ((q , b) ∷ bs) old found minus with ident ≟ q
 ... | yes _ rewrite just-injective found | minus = refl
 ... | no _ = trans (cong (λ n → f b Nat.+ n) (count-put-minus f ident replacement bs old found minus))
  (NatProperties.+-suc (f b) (count f (put ident replacement bs)))
 count-put-plus : ∀ f ident replacement bs old → lookup ident bs ≡ just old →
  f replacement ≡ suc (f old) → count f (put ident replacement bs) ≡ suc (count f bs)
 count-put-plus f ident replacement [] old found plus = case found of λ ()
 count-put-plus f ident replacement ((q , b) ∷ bs) old found plus with ident ≟ q
 ... | yes _ rewrite just-injective found | plus = refl
 ... | no _ = trans (cong (λ n → f b Nat.+ n) (count-put-plus f ident replacement bs old found plus))
  (NatProperties.+-suc (f b) (count f bs))

 outstanding : E.Batch → ℕ
 outstanding b = phaseCount (E.phase b)
  where
  phaseCount : E.Phase → ℕ
  phaseCount E.written = 0
  phaseCount _ = 1
 globalCount : E.State → ℕ
 globalCount s = count outstanding (E.batches s)
 GlobalOwnership : E.State → Set
 GlobalOwnership s = E.runHeld s ≡ + (globalCount s)

 -- Nonnegative signed representation is derived from the number of owned
 -- batches. Source Int overflow remains outside the stated execution profile.
 global-nonnegative : ∀ s → GlobalOwnership s → + 0 ≤ E.runHeld s
 global-nonnegative s owns rewrite owns = +≤+ z≤n
 positive-predecessor : ∀ n → Model.positive n ≡ true → Σ ℕ (λ k → n Int.- + 1 ≡ + k)
 positive-predecessor (+ zero) actual = case actual of λ ()
 positive-predecessor (+ (suc n)) actual = n , refl
 positive-predecessor -[1+ n ] actual = case actual of λ ()
 write-no-underflow : ∀ ident before {after} → E.step (E.writeAccount ident) before ≡ just after →
  + 0 ≤ E.runHeld after
 write-no-underflow ident before actual with write ident before actual
 ... | wrote-batch b cs found phase pending held enabled accounted refl with positive-predecessor (E.runHeld before) held
 ...   | n , same rewrite same = +≤+ z≤n

 initial-global : ∀ plan limit bound keys {s} → E.initial plan limit bound keys ≡ just s → GlobalOwnership s
 initial-global plan limit bound keys actual with E.makeCells plan keys
 ... | nothing = case actual of λ ()
 ... | just cs = case just-injective actual of λ { refl → refl }

 global-write : ∀ ident before {after} → E.step (E.writeAccount ident) before ≡ just after →
  GlobalOwnership before → GlobalOwnership after
 global-write ident before actual owns with write ident before actual
 ... | wrote-batch b cs found phase pending held enabled accounted refl = result
  where
  decrement : count outstanding (E.batches before) ≡
   suc (count outstanding (put ident (record b { phase = E.written }) (E.batches before)))
  decrement = count-put-minus outstanding ident (record b { phase = E.written })
   (E.batches before) b found phaseValue
   where
   phaseValue : outstanding b ≡ 1
   phaseValue rewrite phase = refl
  result : GlobalOwnership (record before
   { cells = cs; runHeld = E.runHeld before Int.- + 1
   ; batches = put ident (record b { phase = E.written }) (E.batches before)
   ; waits = delete ident (E.waits before) })
  result rewrite owns | decrement = refl

 global-failure : ∀ ident before {after} → E.step (E.writeFailed ident) before ≡ just after →
  GlobalOwnership before → GlobalOwnership after
 global-failure ident before actual owns with failure ident before actual
 ... | failed-batch b found phase refl sameCells sameHeld sameWantons sameQueues =
  trans owns (cong +_ (sym (count-put-same outstanding ident (record b { phase = E.failed })
   (E.batches before) b found sameValue)))
  where
  phase-value : E.phase b ≡ E.building ⊎ E.phase b ≡ E.ready →
   outstanding (record b { phase = E.failed }) ≡ outstanding b
  phase-value (inj₁ building) rewrite building = refl
  phase-value (inj₂ ready) rewrite ready = refl
  sameValue : outstanding (record b { phase = E.failed }) ≡ outstanding b
  sameValue = phase-value phase

 global-create : ∀ w k s {t} → E.step (E.createWanton w k) s ≡ just t →
  GlobalOwnership s → GlobalOwnership t
 global-create w k s actual owns with lookup w (E.wantons s) | lookup k (E.cells s)
 ... | nothing | just _ = case just-injective actual of λ { refl → owns }
 ... | nothing | nothing = case actual of λ ()
 ... | just _ | _ = case actual of λ ()
 global-send : ∀ w bytes s {t} → E.step (E.appendPayload w bytes) s ≡ just t →
  GlobalOwnership s → GlobalOwnership t
 global-send w bytes s actual owns with lookup w (E.wantons s)
 ... | nothing = case actual of λ ()
 ... | just f with Relation.Nullary.does (E.payload f Nat.<? Model.softLimit)
 ...   | false = case actual of λ ()
 ...   | true with E.payload f
 ...     | suc _ = case just-injective actual of λ { refl → owns }
 ...     | zero with lookup (E.key f) (E.cells s)
 ...       | nothing = case actual of λ ()
 ...       | just c with lookup (E.fixedLane c) (E.queues s)
 ...         | nothing = case actual of λ ()
 ...         | just q with Relation.Nullary.does (Data.List.length q Nat.<? 100)
 ...           | false = case actual of λ ()
 ...           | true = case just-injective actual of λ { refl → owns }

 global-open : ∀ l s {t} → E.step (E.takeFirst l) s ≡ just t →
  GlobalOwnership s → GlobalOwnership t
 global-open l s actual owns with E.laneBusy l (E.batches s) | lookup l (E.queues s) |
  lookup (E.nextBatch s) (E.batches s) in fresh
 ... | false | just (w ∷ rest) | nothing with lookup w (E.wantons s)
 ...   | nothing = case actual of λ ()
 ...   | just f with lookup (E.key f) (E.cells s)
 ...     | nothing = case actual of λ ()
 ...     | just c = case just-injective actual of λ { refl →
  trans (cong (λ n → n Int.+ + 1) owns)
   (cong +_ (sym (count-put-fresh outstanding (E.nextBatch s) created (E.batches s) fresh))) }
  where
  created = E.batch l ((E.key f , Model.headerBytes Nat.+ (E.fragmentLimit s Nat.⊓ E.payload f)) ∷ [])
   nothing E.building 1
 global-open l s actual owns | true | _ | _ = case actual of λ ()
 global-open l s actual owns | false | nothing | _ = case actual of λ ()
 global-open l s actual owns | false | just [] | _ = case actual of λ ()
 global-open l s actual owns | false | just (_ ∷ _) | just _ = case actual of λ ()

 global-batch-change : ∀ ident before after old replacement →
  lookup ident (E.batches before) ≡ just old → outstanding replacement ≡ outstanding old →
  E.batches after ≡ put ident replacement (E.batches before) →
  E.runHeld after ≡ E.runHeld before → GlobalOwnership before → GlobalOwnership after
 global-batch-change ident before after old replacement found same changed held owns =
  trans held (trans owns (cong +_ (sym (trans (cong (count outstanding) changed)
   (count-put-same outstanding ident replacement (E.batches before) old found same)))))
 global-finish : ∀ ident s {t} → E.step (E.finishBatch ident) s ≡ just t →
  GlobalOwnership s → GlobalOwnership t
 global-finish ident s {t} actual owns with lookup ident (E.batches s) in found
 ... | nothing = case actual of λ ()
 ... | just b with E.phase b in phase | E.pending b | E.belowCaps b s
 ...   | E.building | nothing | false = case just-injective actual of λ { refl →
  global-batch-change ident s t b (record b { phase = E.ready }) found same refl refl owns }
  where
  same : outstanding (record b { phase = E.ready }) ≡ outstanding b
  same rewrite phase = refl
 ...   | E.building | nothing | true = case actual of λ ()
 ...   | E.building | just _ | _ = case actual of λ ()
 ...   | E.ready | _ | _ = case actual of λ ()
 ...   | E.failed | _ | _ = case actual of λ ()
 ...   | E.written | _ | _ = case actual of λ ()
 global-select : ∀ ident s {t} → E.step (E.selectDemand ident) s ≡ just t →
  GlobalOwnership s → GlobalOwnership t
 global-select ident s {t} actual owns with lookup ident (E.batches s) in found
 ... | nothing = case actual of λ ()
 ... | just b with E.phase b in phase | E.pending b | E.belowCaps b s
 ...   | E.building | nothing | true with lookup (E.lane b) (E.queues s)
 ...     | nothing = case actual of λ ()
 ...     | just [] = case just-injective actual of λ { refl →
  global-batch-change ident s t b (record b { phase = E.ready }) found same refl refl owns }
  where
  same : outstanding (record b { phase = E.ready }) ≡ outstanding b
  same rewrite phase = refl
 ...     | just (w ∷ rest) = case just-injective actual of λ { refl →
  global-batch-change ident s t b (record b { pending = just w }) found refl refl refl owns }
 global-select ident s actual owns | just b | E.building | nothing | false = case actual of λ ()
 global-select ident s actual owns | just b | E.building | just _ | _ = case actual of λ ()
 global-select ident s actual owns | just b | E.ready | _ | _ = case actual of λ ()
 global-select ident s actual owns | just b | E.failed | _ | _ = case actual of λ ()
 global-select ident s actual owns | just b | E.written | _ | _ = case actual of λ ()

 previousBytes : Maybe ℕ → ℕ
 previousBytes nothing = 0
 previousBytes (just n) = n
 global-extend : ∀ ident s {t} → E.step (E.takeFragment ident) s ≡ just t →
  GlobalOwnership s → GlobalOwnership t
 global-extend ident s {t} actual owns with lookup ident (E.batches s) in found
 ... | nothing = case actual of λ ()
 ... | just b with E.phase b | E.pending b
 ...   | E.building | just w with lookup w (E.wantons s) | lookup (E.lane b) (E.queues s)
 ...     | just f | just q with lookup (E.key f) (E.cells s) | lookup (E.key f) (E.members b)
 ...       | just c | nothing with E.canRequeue (E.payload f Nat.∸ (E.fragmentLimit s Nat.⊓ E.payload f)) q
 ...         | false = case actual of λ ()
 ...         | true = case just-injective actual of λ { refl →
  global-batch-change ident s t b replacement found refl refl refl owns }
  where
  replacement = record b
   { members = put (E.key f) (Model.headerBytes Nat.+ (E.fragmentLimit s Nat.⊓ E.payload f) Nat.+ previousBytes nothing) (E.members b)
   ; pending = nothing; sdus = suc (E.sdus b) }
 global-extend ident s {t} actual owns | just b | E.building | just w | just f | just q | just c | just oldBytes with E.canRequeue (E.payload f Nat.∸ (E.fragmentLimit s Nat.⊓ E.payload f)) q
 ...         | false = case actual of λ ()
 ...         | true = case just-injective actual of λ { refl →
  global-batch-change ident s t b replacement found refl refl refl owns }
  where
  replacement = record b
   { members = put (E.key f) (Model.headerBytes Nat.+ (E.fragmentLimit s Nat.⊓ E.payload f) Nat.+ previousBytes (just oldBytes)) (E.members b)
   ; pending = nothing; sdus = suc (E.sdus b) }
 global-extend ident s actual owns | just b | E.building | just w | just f | just q | nothing | _ = case actual of λ ()
 global-extend ident s actual owns | just b | E.building | just w | nothing | _ = case actual of λ ()
 global-extend ident s actual owns | just b | E.building | just w | just _ | nothing = case actual of λ ()
 global-extend ident s actual owns | just b | E.building | nothing = case actual of λ ()
 global-extend ident s actual owns | just b | E.ready | _ = case actual of λ ()
 global-extend ident s actual owns | just b | E.failed | _ = case actual of λ ()
 global-extend ident s actual owns | just b | E.written | _ = case actual of λ ()

 global-advance : ∀ ident a s {t} → E.step (E.advance ident a) s ≡ just t → GlobalOwnership s → GlobalOwnership t
 global-advance ident a s actual owns with advance-shape ident a s actual
 ... | W , L , refl = owns
 global-step : ∀ action s {t} → E.step action s ≡ just t → GlobalOwnership s → GlobalOwnership t
 global-step (E.createWanton w k) = global-create w k
 global-step (E.appendPayload w n) = global-send w n
 global-step (E.takeFirst lane) = global-open lane
 global-step (E.selectDemand ident) = global-select ident
 global-step (E.takeFragment ident) = global-extend ident
 global-step (E.finishBatch ident) = global-finish ident
 global-step (E.writeAccount ident) = global-write ident
 global-step (E.writeFailed ident) = global-failure ident
 global-step (E.advance ident a) = global-advance ident a
 global-runs : ∀ {s actions t} → Runs s actions t → GlobalOwnership s → GlobalOwnership t
 global-runs stop owns = owns
 global-runs (more {s = s} {a = action} actual path) owns = global-runs path (global-step action s actual owns)
 from-initial-global : ∀ {plan limit bound keys start actions current} →
  E.initial plan limit bound keys ≡ just start → Runs start actions current → GlobalOwnership current
 from-initial-global {plan} {limit} {bound} {keys} initialized path =
  global-runs path (initial-global plan limit bound keys initialized)

 CellNonnegative : E.Cell → Set
 CellNonnegative c = + 0 ≤ E.keyHeld c
 CellsNonnegative : E.State → Set
 CellsNonnegative s = All (λ binding → CellNonnegative (proj₂ binding)) (E.cells s)
 lookup-value : ∀ (P : E.Cell → Set) (k : Key) (cs : Store Key E.Cell) (c : E.Cell) → All (λ binding → P (proj₂ binding)) cs →
  lookup k cs ≡ just c → P c
 lookup-value P k [] c [] found = case found of λ ()
 lookup-value P k ((q , old) ∷ cs) c (head ∷ rest) found with k ≟ q
 ... | yes _ = case just-injective found of λ { refl → head }
 ... | no _ = lookup-value P k cs c rest found
 lookup-nonnegative : ∀ (k : Key) (cs : Store Key E.Cell) (c : E.Cell) → All (λ binding → CellNonnegative (proj₂ binding)) cs →
  lookup k cs ≡ just c → CellNonnegative c
 lookup-nonnegative = lookup-value CellNonnegative
 increment-nonnegative : ∀ n → + 0 ≤ n → + 0 ≤ n Int.+ + 1
 increment-nonnegative (+ n) (+≤+ nonnegative) = +≤+ z≤n
 decrement-nonnegative : ∀ n → Model.positive n ≡ true → + 0 ≤ n Int.- + 1
 decrement-nonnegative n positive with positive-predecessor n positive
 ... | k , same rewrite same = +≤+ z≤n
 account-nonnegative : ∀ members cs {after} → E.account members cs ≡ just after →
  All (λ binding → CellNonnegative (proj₂ binding)) cs →
  All (λ binding → CellNonnegative (proj₂ binding)) after
 account-nonnegative [] cs actual valid = case just-injective actual of λ { refl → valid }
 account-nonnegative ((k , bytes) ∷ members) cs actual valid with lookup k cs
 ... | nothing = case actual of λ ()
 ... | just c with Model.positive (E.keyHeld c) in positive
 ...   | false = case actual of λ ()
 ...   | true = account-nonnegative members
  (put k (E.cell (E.fixedLane c) (E.keyHeld c Int.- + 1) (E.sent c Nat.+ bytes)) cs) actual
  (put-values CellNonnegative k
   (E.cell (E.fixedLane c) (E.keyHeld c Int.- + 1) (E.sent c Nat.+ bytes)) cs
   (decrement-nonnegative (E.keyHeld c) positive) valid)

 makeCells-nonnegative : ∀ plan keys cs → E.makeCells plan keys ≡ just cs →
  All (λ binding → CellNonnegative (proj₂ binding)) cs
 makeCells-nonnegative plan [] cs actual = case just-injective actual of λ { refl → [] }
 makeCells-nonnegative plan ((k , requested) ∷ keys) cs actual with E.makeCells plan keys in tail
 ... | nothing = case actual of λ ()
 ... | just rest with lookup k rest
 ...   | just _ = case actual of λ ()
 ...   | nothing = case just-injective actual of λ { refl → (+≤+ z≤n) ∷ makeCells-nonnegative plan keys rest tail }
 initial-cells-nonnegative : ∀ plan limit bound keys {s} → E.initial plan limit bound keys ≡ just s → CellsNonnegative s
 initial-cells-nonnegative plan limit bound keys actual with E.makeCells plan keys in made
 ... | nothing = case actual of λ ()
 ... | just cs = case just-injective actual of λ { refl → makeCells-nonnegative plan keys cs made }
 cells-write : ∀ ident before {after} → E.step (E.writeAccount ident) before ≡ just after →
  CellsNonnegative before → CellsNonnegative after
 cells-write ident before actual valid with write ident before actual
 ... | wrote-batch b cs found phase pending held enabled accounted refl = account-nonnegative (E.members b) (E.cells before) accounted valid

 present : Maybe ℕ → ℕ
 present nothing = 0
 present (just _) = 1
 membership : Key → E.Batch → ℕ
 membership k b = outstanding b Nat.* present (lookup k (E.members b))
 KeyOwnership : E.State → Set
 KeyOwnership s = ∀ k c → lookup k (E.cells s) ≡ just c →
  E.keyHeld c ≡ + (count (membership k) (E.batches s))
 makeCells-zero : ∀ plan keys cs → E.makeCells plan keys ≡ just cs →
  All (λ binding → E.keyHeld (proj₂ binding) ≡ + 0) cs
 makeCells-zero plan [] cs actual = case just-injective actual of λ { refl → [] }
 makeCells-zero plan ((k , requested) ∷ keys) cs actual with E.makeCells plan keys in tail
 ... | nothing = case actual of λ ()
 ... | just rest with lookup k rest
 ...   | just _ = case actual of λ ()
 ...   | nothing = case just-injective actual of λ { refl → refl ∷ makeCells-zero plan keys rest tail }
 initial-key-ownership : ∀ plan limit bound keys {s} → E.initial plan limit bound keys ≡ just s → KeyOwnership s
 initial-key-ownership plan limit bound keys actual with E.makeCells plan keys in made
 ... | nothing = case actual of λ ()
 ... | just cs = case just-injective actual of λ { refl → λ k c found →
  lookup-value (λ cell → E.keyHeld cell ≡ + 0) k cs c (makeCells-zero plan keys cs made) found }

 -- Batch membership is a set of source keys, although the demand queues are
 -- deliberately lists and may repeat a wanton identity.
 BatchMembersUnique : E.Batch → Set
 BatchMembersUnique b = UniqueKeys (E.members b)
 MembersUnique : E.State → Set
 MembersUnique s = All (λ binding → BatchMembersUnique (proj₂ binding)) (E.batches s)
 lookup-batch-value : ∀ (P : E.Batch → Set) (ident : ℕ) (bs : Store ℕ E.Batch) (b : E.Batch) →
  All (λ binding → P (proj₂ binding)) bs → lookup ident bs ≡ just b → P b
 lookup-batch-value P ident [] b [] found = case found of λ ()
 lookup-batch-value P ident ((q , old) ∷ bs) b (head ∷ rest) found with ident ≟ q
 ... | yes _ = case just-injective found of λ { refl → head }
 ... | no _ = lookup-batch-value P ident bs b rest found
 members-change : ∀ ident before after replacement → BatchMembersUnique replacement →
  E.batches after ≡ put ident replacement (E.batches before) → MembersUnique before → MembersUnique after
 members-change ident before after replacement unique changed valid rewrite changed =
  put-values BatchMembersUnique ident replacement (E.batches before) unique valid
 members-from-old : ∀ ident before after old replacement →
  lookup ident (E.batches before) ≡ just old → E.members replacement ≡ E.members old →
  E.batches after ≡ put ident replacement (E.batches before) → MembersUnique before → MembersUnique after
 members-from-old ident before after old replacement found same changed valid =
  members-change ident before after replacement
   (subst UniqueKeys (sym same) (lookup-batch-value BatchMembersUnique ident (E.batches before) old valid found)) changed valid
 initial-members : ∀ plan limit bound keys {s} → E.initial plan limit bound keys ≡ just s → MembersUnique s
 initial-members plan limit bound keys actual with E.makeCells plan keys
 ... | nothing = case actual of λ ()
 ... | just cs = case just-injective actual of λ { refl → [] }
 members-write : ∀ ident before {after} → E.step (E.writeAccount ident) before ≡ just after →
  MembersUnique before → MembersUnique after
 members-write ident before {after} actual valid with write ident before actual
 ... | wrote-batch b cs found phase pending held enabled accounted refl =
  members-from-old ident before after b (record b { phase = E.written }) found refl refl valid
 members-failure : ∀ ident before {after} → E.step (E.writeFailed ident) before ≡ just after →
  MembersUnique before → MembersUnique after
 members-failure ident before {after} actual valid with failure ident before actual
 ... | failed-batch b found phase refl sameCells sameHeld sameWantons sameQueues =
  members-from-old ident before after b (record b { phase = E.failed }) found refl refl valid

 members-create : ∀ w k s {t} → E.step (E.createWanton w k) s ≡ just t →
  MembersUnique s → MembersUnique t
 members-create w k s actual owns with lookup w (E.wantons s) | lookup k (E.cells s)
 ... | nothing | just _ = case just-injective actual of λ { refl → owns }
 ... | nothing | nothing = case actual of λ ()
 ... | just _ | _ = case actual of λ ()
 members-send : ∀ w bytes s {t} → E.step (E.appendPayload w bytes) s ≡ just t →
  MembersUnique s → MembersUnique t
 members-send w bytes s actual owns with lookup w (E.wantons s)
 ... | nothing = case actual of λ ()
 ... | just f with Relation.Nullary.does (E.payload f Nat.<? Model.softLimit)
 ...   | false = case actual of λ ()
 ...   | true with E.payload f
 ...     | suc _ = case just-injective actual of λ { refl → owns }
 ...     | zero with lookup (E.key f) (E.cells s)
 ...       | nothing = case actual of λ ()
 ...       | just c with lookup (E.fixedLane c) (E.queues s)
 ...         | nothing = case actual of λ ()
 ...         | just q with Relation.Nullary.does (Data.List.length q Nat.<? 100)
 ...           | false = case actual of λ ()
 ...           | true = case just-injective actual of λ { refl → owns }

 members-open : ∀ l s {t} → E.step (E.takeFirst l) s ≡ just t → MembersUnique s → MembersUnique t
 members-open l s {t} actual valid with E.laneBusy l (E.batches s) | lookup l (E.queues s) |
  lookup (E.nextBatch s) (E.batches s)
 ... | false | just (w ∷ rest) | nothing with lookup w (E.wantons s)
 ...   | nothing = case actual of λ ()
 ...   | just f with lookup (E.key f) (E.cells s)
 ...     | nothing = case actual of λ ()
 ...     | just c = case just-injective actual of λ { refl →
  members-change (E.nextBatch s) s t created ([] ∷ []) refl valid }
  where
  created = E.batch l ((E.key f , Model.headerBytes Nat.+ (E.fragmentLimit s Nat.⊓ E.payload f)) ∷ [])
   nothing E.building 1
 members-open l s actual valid | true | _ | _ = case actual of λ ()
 members-open l s actual valid | false | nothing | _ = case actual of λ ()
 members-open l s actual valid | false | just [] | _ = case actual of λ ()
 members-open l s actual valid | false | just (_ ∷ _) | just _ = case actual of λ ()
 members-finish : ∀ ident s {t} → E.step (E.finishBatch ident) s ≡ just t → MembersUnique s → MembersUnique t
 members-finish ident s {t} actual valid with lookup ident (E.batches s) in found
 ... | nothing = case actual of λ ()
 ... | just b with E.phase b | E.pending b | E.belowCaps b s
 ...   | E.building | nothing | false = case just-injective actual of λ { refl →
  members-from-old ident s t b (record b { phase = E.ready }) found refl refl valid }
 ...   | E.building | nothing | true = case actual of λ ()
 ...   | E.building | just _ | _ = case actual of λ ()
 ...   | E.ready | _ | _ = case actual of λ ()
 ...   | E.failed | _ | _ = case actual of λ ()
 ...   | E.written | _ | _ = case actual of λ ()
 members-select : ∀ ident s {t} → E.step (E.selectDemand ident) s ≡ just t → MembersUnique s → MembersUnique t
 members-select ident s {t} actual valid with lookup ident (E.batches s) in found
 ... | nothing = case actual of λ ()
 ... | just b with E.phase b | E.pending b | E.belowCaps b s
 ...   | E.building | nothing | true with lookup (E.lane b) (E.queues s)
 ...     | nothing = case actual of λ ()
 ...     | just [] = case just-injective actual of λ { refl →
  members-from-old ident s t b (record b { phase = E.ready }) found refl refl valid }
 ...     | just (w ∷ rest) = case just-injective actual of λ { refl →
  members-from-old ident s t b (record b { pending = just w }) found refl refl valid }
 members-select ident s actual valid | just b | E.building | nothing | false = case actual of λ ()
 members-select ident s actual valid | just b | E.building | just _ | _ = case actual of λ ()
 members-select ident s actual valid | just b | E.ready | _ | _ = case actual of λ ()
 members-select ident s actual valid | just b | E.failed | _ | _ = case actual of λ ()
 members-select ident s actual valid | just b | E.written | _ | _ = case actual of λ ()
 members-extend : ∀ ident s {t} → E.step (E.takeFragment ident) s ≡ just t → MembersUnique s → MembersUnique t
 members-extend ident s {t} actual valid with lookup ident (E.batches s) in found
 ... | nothing = case actual of λ ()
 ... | just b with E.phase b | E.pending b
 ...   | E.building | just w with lookup w (E.wantons s) | lookup (E.lane b) (E.queues s)
 ...     | just f | just q with lookup (E.key f) (E.cells s) | lookup (E.key f) (E.members b)
 ...       | just c | nothing with E.canRequeue (E.payload f Nat.∸ (E.fragmentLimit s Nat.⊓ E.payload f)) q
 ...         | false = case actual of λ ()
 ...         | true = case just-injective actual of λ { refl →
  members-change ident s t replacement newUnique refl valid }
  where
  total = Model.headerBytes Nat.+ (E.fragmentLimit s Nat.⊓ E.payload f) Nat.+ previousBytes nothing
  replacement = record b { members = put (E.key f) total (E.members b); pending = nothing; sdus = suc (E.sdus b) }
  newUnique : BatchMembersUnique replacement
  newUnique = put-unique (E.key f) total (E.members b)
   (lookup-batch-value BatchMembersUnique ident (E.batches s) b valid found)
 members-extend ident s {t} actual valid | just b | E.building | just w | just f | just q | just c | just oldBytes with E.canRequeue (E.payload f Nat.∸ (E.fragmentLimit s Nat.⊓ E.payload f)) q
 ...         | false = case actual of λ ()
 ...         | true = case just-injective actual of λ { refl →
  members-change ident s t replacement newUnique refl valid }
  where
  total = Model.headerBytes Nat.+ (E.fragmentLimit s Nat.⊓ E.payload f) Nat.+ previousBytes (just oldBytes)
  replacement = record b { members = put (E.key f) total (E.members b); pending = nothing; sdus = suc (E.sdus b) }
  newUnique : BatchMembersUnique replacement
  newUnique = put-unique (E.key f) total (E.members b)
   (lookup-batch-value BatchMembersUnique ident (E.batches s) b valid found)
 members-extend ident s actual valid | just b | E.building | just w | just f | just q | nothing | _ = case actual of λ ()
 members-extend ident s actual valid | just b | E.building | just w | nothing | _ = case actual of λ ()
 members-extend ident s actual valid | just b | E.building | just w | just _ | nothing = case actual of λ ()
 members-extend ident s actual valid | just b | E.building | nothing = case actual of λ ()
 members-extend ident s actual valid | just b | E.ready | _ = case actual of λ ()
 members-extend ident s actual valid | just b | E.failed | _ = case actual of λ ()
 members-extend ident s actual valid | just b | E.written | _ = case actual of λ ()
 members-advance : ∀ ident a s {t} → E.step (E.advance ident a) s ≡ just t → MembersUnique s → MembersUnique t
 members-advance ident a s actual valid with advance-shape ident a s actual
 ... | W , L , refl = valid
 members-step : ∀ action s {t} → E.step action s ≡ just t → MembersUnique s → MembersUnique t
 members-step (E.createWanton w k) = members-create w k
 members-step (E.appendPayload w n) = members-send w n
 members-step (E.takeFirst lane) = members-open lane
 members-step (E.selectDemand ident) = members-select ident
 members-step (E.takeFragment ident) = members-extend ident
 members-step (E.finishBatch ident) = members-finish ident
 members-step (E.writeAccount ident) = members-write ident
 members-step (E.writeFailed ident) = members-failure ident
 members-step (E.advance ident a) = members-advance ident a
 members-runs : ∀ {s actions t} → Runs s actions t → MembersUnique s → MembersUnique t
 members-runs stop valid = valid
 members-runs (more {s = s} {a = action} actual path) valid = members-runs path (members-step action s actual valid)
 from-initial-members : ∀ {plan limit bound keys start actions current} →
  E.initial plan limit bound keys ≡ just start → Runs start actions current → MembersUnique current
 from-initial-members {plan} {limit} {bound} {keys} initialized path =
  members-runs path (initial-members plan limit bound keys initialized)

 -- Accounting a distinct member set changes exactly its source-key cells.
 -- The unrelated-key frame is valid without a store- or queue-uniqueness axiom.
 account-unrelated : ∀ queried members cs {after} → lookup queried members ≡ nothing →
  E.account members cs ≡ just after → lookup queried after ≡ lookup queried cs
 account-unrelated queried [] cs absent actual = case just-injective actual of λ { refl → refl }
 account-unrelated queried ((k , bytes) ∷ members) cs absent actual with queried ≟ k
 ... | yes _ = case absent of λ ()
 ... | no different with lookup k cs
 ...   | nothing = case actual of λ ()
 ...   | just c with Model.positive (E.keyHeld c)
 ...     | false = case actual of λ ()
 ...     | true = trans
  (account-unrelated queried members
   (put k (E.cell (E.fixedLane c) (E.keyHeld c Int.- + 1) (E.sent c Nat.+ bytes)) cs) absent actual)
  (lookup-put-other k queried (E.cell (E.fixedLane c) (E.keyHeld c Int.- + 1) (E.sent c Nat.+ bytes)) cs different)
 releasedHeld : Maybe ℕ → ℤ → ℤ
 releasedHeld nothing n = n
 releasedHeld (just _) n = n Int.- + 1
 creditedSent : Maybe ℕ → ℕ → ℕ
 creditedSent nothing n = n
 creditedSent (just bytes) n = n Nat.+ bytes
 record AccountedCell (queried : Key) (members : Store Key ℕ) (old : E.Cell) (after : Store Key E.Cell) : Set where
  constructor accounted-cell
  field current : E.Cell
        found-current : lookup queried after ≡ just current
        held-shape : E.keyHeld current ≡ releasedHeld (lookup queried members) (E.keyHeld old)
        sent-shape : E.sent current ≡ creditedSent (lookup queried members) (E.sent old)
        lane-same : E.fixedLane current ≡ E.fixedLane old
 -- Equal lookups of the member store describe the same accounted cell.
 accounted-retarget : ∀ queried ms ms′ old after → lookup queried ms′ ≡ lookup queried ms →
  AccountedCell queried ms old after → AccountedCell queried ms′ old after
 accounted-retarget queried ms ms′ old after same (accounted-cell current found held sent lane) =
  accounted-cell current found
   (trans held (cong (λ m → releasedHeld m (E.keyHeld old)) (sym same)))
   (trans sent (cong (λ m → creditedSent m (E.sent old)) (sym same))) lane
 lookup-cons-other : ∀ (q k : Key) (v : ℕ) ms → q ≢ k → lookup q ((k , v) ∷ ms) ≡ lookup q ms
 lookup-cons-other q k v ms different with q ≟ k
 ... | yes same = ⊥-elim (different same)
 ... | no _ = refl
 account-cell : ∀ queried members cs old {after} → UniqueKeys members → lookup queried cs ≡ just old →
  E.account members cs ≡ just after → AccountedCell queried members old after
 account-cell queried [] cs old [] beforeFound actual = case just-injective actual of λ
  { refl → accounted-cell old beforeFound refl refl refl }
 account-cell queried ((k , bytes) ∷ members) cs old (apart ∷ unique) beforeFound actual with queried ≟ k
 ... | yes refl with lookup k cs in selected
 ...   | nothing = case actual of λ ()
 ...   | just c with Model.positive (E.keyHeld c)
 ...     | false = case actual of λ ()
 ...     | true = case just-injective beforeFound of λ { refl →
  accounted-cell (E.cell (E.fixedLane old) (E.keyHeld old Int.- + 1) (E.sent old Nat.+ bytes))
   (trans (account-unrelated k members
    (put k (E.cell (E.fixedLane old) (E.keyHeld old Int.- + 1) (E.sent old Nat.+ bytes)) cs)
    (apart-lookup k members apart) actual)
    (lookup-put k (E.cell (E.fixedLane old) (E.keyHeld old Int.- + 1) (E.sent old Nat.+ bytes)) cs))
   (sym (cong (λ m → releasedHeld m (E.keyHeld old)) (lookup-head k bytes members)))
   (sym (cong (λ m → creditedSent m (E.sent old)) (lookup-head k bytes members))) refl }
 account-cell queried ((k , bytes) ∷ members) cs old (apart ∷ unique) beforeFound actual | no different with lookup k cs
 ... | nothing = case actual of λ ()
 ... | just c with Model.positive (E.keyHeld c)
 ...   | false = case actual of λ ()
 ...   | true = accounted-retarget queried members ((k , bytes) ∷ members) old _
  (lookup-cons-other queried k bytes members different) (account-cell queried members
  (put k (E.cell (E.fixedLane c) (E.keyHeld c Int.- + 1) (E.sent c Nat.+ bytes)) cs) old unique
  (trans (lookup-put-other k queried (E.cell (E.fixedLane c) (E.keyHeld c Int.- + 1) (E.sent c Nat.+ bytes)) cs different) beforeFound)
  actual)

 -- Reverse domain preservation is needed when a post-state lookup selects the
 -- cell. The writer only replaces cells that actually existed before it.
 account-origin : ∀ queried members cs {after current} → E.account members cs ≡ just after →
  lookup queried after ≡ just current → Σ E.Cell (λ old → lookup queried cs ≡ just old)
 account-origin queried [] cs {current = current} actual found =
  case just-injective actual of λ { refl → current , found }
 account-origin queried ((k , bytes) ∷ members) cs actual found with lookup k cs in selected
 ... | nothing = case actual of λ ()
 ... | just c with Model.positive (E.keyHeld c)
 ...   | false = case actual of λ ()
 ...   | true with account-origin queried members
  (put k (E.cell (E.fixedLane c) (E.keyHeld c Int.- + 1) (E.sent c Nat.+ bytes)) cs) actual found
 ...     | old , prior with queried ≟ k
 ...       | yes refl = c , selected
 ...       | no different = old , trans
  (sym (lookup-put-other k queried (E.cell (E.fixedLane c) (E.keyHeld c Int.- + 1) (E.sent c Nat.+ bytes)) cs different)) prior

 -- The per-key conservation law drops exactly one membership when this ready
 -- batch is marked written. A nonmember key's owned count is unchanged.
 release-owned-key : ∀ ident before b queried old →
  lookup ident (E.batches before) ≡ just b → E.phase b ≡ E.ready →
  lookup queried (E.cells before) ≡ just old → KeyOwnership before →
  releasedHeld (lookup queried (E.members b)) (E.keyHeld old) ≡
   + (count (membership queried) (put ident (record b { phase = E.written }) (E.batches before)))
 release-owned-key ident before b queried old found phase oldFound owns with lookup queried (E.members b) in member
 ... | nothing = trans (owns queried old oldFound) (cong +_ (sym unchanged))
  where
  same : membership queried (record b { phase = E.written }) ≡ membership queried b
  same rewrite phase | member = refl
  unchanged = count-put-same (membership queried) ident (record b { phase = E.written })
   (E.batches before) b found same
 ... | just bytes = result
  where
  positiveMember : membership queried b ≡ suc (membership queried (record b { phase = E.written }))
  positiveMember rewrite phase | member = refl
  decrement = count-put-minus (membership queried) ident (record b { phase = E.written })
   (E.batches before) b found positiveMember
  result : releasedHeld (just bytes) (E.keyHeld old) ≡
   + (count (membership queried) (put ident (record b { phase = E.written }) (E.batches before)))
  result rewrite owns queried old oldFound | decrement = refl
 key-write : ∀ ident before {after} → E.step (E.writeAccount ident) before ≡ just after →
  MembersUnique before → KeyOwnership before → KeyOwnership after
 key-write ident before actual unique owns queried current foundCurrent with write ident before actual
 ... | wrote-batch b cs found phase pending held enabled accounted refl with
  account-origin queried (E.members b) (E.cells before) accounted foundCurrent
 ...   | old , oldFound with account-cell queried (E.members b) (E.cells before) old
  (lookup-batch-value BatchMembersUnique ident (E.batches before) b unique found) oldFound accounted
 ...     | accounted-cell next foundNext heldShape sentShape laneSame =
  trans (cong E.keyHeld (just-injective (trans (sym foundCurrent) foundNext)))
   (trans heldShape (release-owned-key ident before b queried old found phase oldFound owns))

 -- Steps that leave every key cell alone and replace one batch row with the
 -- same per-key membership preserve the per-key conservation law.
 key-batch-change : ∀ ident before after old replacement →
  lookup ident (E.batches before) ≡ just old →
  (∀ q → membership q replacement ≡ membership q old) →
  E.batches after ≡ put ident replacement (E.batches before) →
  E.cells after ≡ E.cells before → KeyOwnership before → KeyOwnership after
 key-batch-change ident before after old replacement found same changed cellsSame owns q current foundAfter =
  trans (owns q current (trans (cong (lookup q) (sym cellsSame)) foundAfter))
   (cong +_ (sym (trans (cong (count (membership q)) changed)
    (count-put-same (membership q) ident replacement (E.batches before) old found (same q)))))

 -- One key cell gains one held membership exactly when that key's batch
 -- count grows by one; every other key keeps both its cell and its count.
 key-acquire : ∀ before after k old →
  lookup k (E.cells before) ≡ just old →
  E.cells after ≡ put k (E.cell (E.fixedLane old) (E.keyHeld old Int.+ + 1) (E.sent old)) (E.cells before) →
  count (membership k) (E.batches after) ≡ count (membership k) (E.batches before) Nat.+ 1 →
  (∀ q → q ≢ k → count (membership q) (E.batches after) ≡ count (membership q) (E.batches before)) →
  KeyOwnership before → KeyOwnership after
 key-acquire before after k old oldFound cellsAfter plusK sameOther owns q current found with q ≟ k
 ... | yes refl = trans (cong E.keyHeld (just-injective (trans (sym located)
   (lookup-put k (E.cell (E.fixedLane old) (E.keyHeld old Int.+ + 1) (E.sent old)) (E.cells before)))))
  (trans (cong (λ n → n Int.+ + 1) (owns k old oldFound)) (cong +_ (sym plusK)))
  where
  located = trans (sym (cong (lookup k) cellsAfter)) found
 ... | no different = trans (owns q current (trans (sym (lookup-put-other k q
   (E.cell (E.fixedLane old) (E.keyHeld old Int.+ + 1) (E.sent old)) (E.cells before) different))
   (trans (sym (cong (lookup q) cellsAfter)) found)))
  (cong +_ (sym (sameOther q different)))

 -- Extending a batch with an already-member key rewrites only its byte data.
 key-touch : ∀ before after k old replacement →
  lookup k (E.cells before) ≡ just old → E.keyHeld replacement ≡ E.keyHeld old →
  E.cells after ≡ put k replacement (E.cells before) →
  (∀ q → count (membership q) (E.batches after) ≡ count (membership q) (E.batches before)) →
  KeyOwnership before → KeyOwnership after
 key-touch before after k old replacement oldFound heldSame cellsAfter sameAll owns q current found with q ≟ k
 ... | yes refl = trans (cong E.keyHeld (just-injective (trans (sym located)
   (lookup-put k replacement (E.cells before)))))
  (trans heldSame (trans (owns k old oldFound) (cong +_ (sym (sameAll k)))))
  where
  located = trans (sym (cong (lookup k) cellsAfter)) found
 ... | no different = trans (owns q current (trans (sym (lookup-put-other k q replacement (E.cells before) different))
   (trans (sym (cong (lookup q) cellsAfter)) found)))
  (cong +_ (sym (sameAll q)))

 building-one : ∀ b → E.phase b ≡ E.building → outstanding b ≡ 1
 building-one b phase rewrite phase = refl

 key-create : ∀ w k s {t} → E.step (E.createWanton w k) s ≡ just t → KeyOwnership s → KeyOwnership t
 key-create w k s actual owns with lookup w (E.wantons s) | lookup k (E.cells s)
 ... | nothing | just _ = case just-injective actual of λ { refl → owns }
 ... | nothing | nothing = case actual of λ ()
 ... | just _ | _ = case actual of λ ()
 key-send : ∀ w bytes s {t} → E.step (E.appendPayload w bytes) s ≡ just t → KeyOwnership s → KeyOwnership t
 key-send w bytes s actual owns with lookup w (E.wantons s)
 ... | nothing = case actual of λ ()
 ... | just f with Relation.Nullary.does (E.payload f Nat.<? Model.softLimit)
 ...   | false = case actual of λ ()
 ...   | true with E.payload f
 ...     | suc _ = case just-injective actual of λ { refl → owns }
 ...     | zero with lookup (E.key f) (E.cells s)
 ...       | nothing = case actual of λ ()
 ...       | just c with lookup (E.fixedLane c) (E.queues s)
 ...         | nothing = case actual of λ ()
 ...         | just q with Relation.Nullary.does (Data.List.length q Nat.<? 100)
 ...           | false = case actual of λ ()
 ...           | true = case just-injective actual of λ { refl → owns }

 key-finish : ∀ ident s {t} → E.step (E.finishBatch ident) s ≡ just t → KeyOwnership s → KeyOwnership t
 key-finish ident s {t} actual owns with lookup ident (E.batches s) in found
 ... | nothing = case actual of λ ()
 ... | just b with E.phase b in phase | E.pending b | E.belowCaps b s
 ...   | E.building | nothing | false = case just-injective actual of λ { refl →
  key-batch-change ident s t b (record b { phase = E.ready }) found same refl refl owns }
  where
  same : ∀ q → membership q (record b { phase = E.ready }) ≡ membership q b
  same q rewrite phase = refl
 ...   | E.building | nothing | true = case actual of λ ()
 ...   | E.building | just _ | _ = case actual of λ ()
 ...   | E.ready | _ | _ = case actual of λ ()
 ...   | E.failed | _ | _ = case actual of λ ()
 ...   | E.written | _ | _ = case actual of λ ()
 key-select : ∀ ident s {t} → E.step (E.selectDemand ident) s ≡ just t → KeyOwnership s → KeyOwnership t
 key-select ident s {t} actual owns with lookup ident (E.batches s) in found
 ... | nothing = case actual of λ ()
 ... | just b with E.phase b in phase | E.pending b | E.belowCaps b s
 ...   | E.building | nothing | true with lookup (E.lane b) (E.queues s)
 ...     | nothing = case actual of λ ()
 ...     | just [] = case just-injective actual of λ { refl →
  key-batch-change ident s t b (record b { phase = E.ready }) found same refl refl owns }
  where
  same : ∀ q → membership q (record b { phase = E.ready }) ≡ membership q b
  same q rewrite phase = refl
 ...     | just (w ∷ rest) = case just-injective actual of λ { refl →
  key-batch-change ident s t b (record b { pending = just w }) found (λ q → refl) refl refl owns }
 key-select ident s actual owns | just b | E.building | nothing | false = case actual of λ ()
 key-select ident s actual owns | just b | E.building | just _ | _ = case actual of λ ()
 key-select ident s actual owns | just b | E.ready | _ | _ = case actual of λ ()
 key-select ident s actual owns | just b | E.failed | _ | _ = case actual of λ ()
 key-select ident s actual owns | just b | E.written | _ | _ = case actual of λ ()

 key-failure : ∀ ident before {after} → E.step (E.writeFailed ident) before ≡ just after →
  KeyOwnership before → KeyOwnership after
 key-failure ident before {after} actual owns with failure ident before actual
 ... | failed-batch b found phase refl sameCells sameHeld sameWantons sameQueues =
  key-batch-change ident before after b (record b { phase = E.failed }) found (same phase) refl refl owns
  where
  same : E.phase b ≡ E.building ⊎ E.phase b ≡ E.ready →
   ∀ q → membership q (record b { phase = E.failed }) ≡ membership q b
  same (inj₁ building) q rewrite building = refl
  same (inj₂ ready) q rewrite ready = refl

 -- A fresh batch contributes exactly one membership, for its first key.
 singleton-member : ∀ (k : Key) (n : ℕ) → present (lookup k ((k , n) ∷ [])) ≡ 1
 singleton-member k n = cong present (lookup-head k n [])
 singleton-other : ∀ (q k : Key) (n : ℕ) → q ≢ k → present (lookup q ((k , n) ∷ [])) ≡ 0
 singleton-other q k n different = cong present (apart-lookup q ((k , n) ∷ []) (different ∷ []))
 key-open : ∀ l s {t} → E.step (E.takeFirst l) s ≡ just t → KeyOwnership s → KeyOwnership t
 key-open l s {t} actual owns with E.laneBusy l (E.batches s) | lookup l (E.queues s) |
  lookup (E.nextBatch s) (E.batches s) in fresh
 ... | false | just (w ∷ rest) | nothing with lookup w (E.wantons s)
 ...   | nothing = case actual of λ ()
 ...   | just f with lookup (E.key f) (E.cells s) in cellFound
 ...     | nothing = case actual of λ ()
 ...     | just c = case just-injective actual of λ { refl →
  key-acquire s t (E.key f) c cellFound refl plusK sameOther owns }
  where
  bytes = Model.headerBytes Nat.+ (E.fragmentLimit s Nat.⊓ E.payload f)
  created = E.batch l ((E.key f , bytes) ∷ []) nothing E.building 1
  plusK : count (membership (E.key f)) (put (E.nextBatch s) created (E.batches s)) ≡
   count (membership (E.key f)) (E.batches s) Nat.+ 1
  plusK = trans (count-put-fresh (membership (E.key f)) (E.nextBatch s) created (E.batches s) fresh)
   (cong (λ n → count (membership (E.key f)) (E.batches s) Nat.+ (1 Nat.* n)) (singleton-member (E.key f) bytes))
  sameOther : ∀ q → q ≢ E.key f →
   count (membership q) (put (E.nextBatch s) created (E.batches s)) ≡ count (membership q) (E.batches s)
  sameOther q different = trans (count-put-fresh (membership q) (E.nextBatch s) created (E.batches s) fresh)
   (trans (cong (λ n → count (membership q) (E.batches s) Nat.+ (1 Nat.* n)) (singleton-other q (E.key f) bytes different))
    (NatProperties.+-identityʳ (count (membership q) (E.batches s))))
 key-open l s actual owns | true | _ | _ = case actual of λ ()
 key-open l s actual owns | false | nothing | _ = case actual of λ ()
 key-open l s actual owns | false | just [] | _ = case actual of λ ()
 key-open l s actual owns | false | just (_ ∷ _) | just _ = case actual of λ ()

 -- Extension adds a key membership only on the key's first fragment in this
 -- batch; repeated fragments for the key keep the shared held cell unchanged.
 key-extend : ∀ ident s {t} → E.step (E.takeFragment ident) s ≡ just t → KeyOwnership s → KeyOwnership t
 key-extend ident s {t} actual owns with lookup ident (E.batches s) in found
 ... | nothing = case actual of λ ()
 ... | just b with E.phase b in phase | E.pending b
 ...   | E.building | just w with lookup w (E.wantons s) | lookup (E.lane b) (E.queues s)
 ...     | just f | just q with lookup (E.key f) (E.cells s) in cellFound | lookup (E.key f) (E.members b) in prior
 ...       | just c | nothing with E.canRequeue (E.payload f Nat.∸ (E.fragmentLimit s Nat.⊓ E.payload f)) q
 ...         | false = case actual of λ ()
 ...         | true = case just-injective actual of λ { refl →
  key-acquire s t (E.key f) c cellFound refl plusK sameOther owns }
  where
  total = Model.headerBytes Nat.+ (E.fragmentLimit s Nat.⊓ E.payload f) Nat.+ previousBytes nothing
  replacement = record b { members = put (E.key f) total (E.members b); pending = nothing; sdus = suc (E.sdus b) }
  one = building-one b phase
  plusMember : membership (E.key f) replacement ≡ suc (membership (E.key f) b)
  plusMember = trans (cong (λ m → outstanding b Nat.* present m) (lookup-put (E.key f) total (E.members b)))
   (trans (cong (λ n → n Nat.* 1) one)
    (sym (trans (cong (λ m → suc (outstanding b Nat.* present m)) prior) (cong (λ n → suc (n Nat.* 0)) one))))
  plusK : count (membership (E.key f)) (put ident replacement (E.batches s)) ≡
   count (membership (E.key f)) (E.batches s) Nat.+ 1
  plusK = trans (count-put-plus (membership (E.key f)) ident replacement (E.batches s) b found plusMember)
   (sym (NatProperties.+-comm (count (membership (E.key f)) (E.batches s)) 1))
  sameOther : ∀ r → r ≢ E.key f →
   count (membership r) (put ident replacement (E.batches s)) ≡ count (membership r) (E.batches s)
  sameOther r different = count-put-same (membership r) ident replacement (E.batches s) b found
   (cong (λ m → outstanding b Nat.* present m) (lookup-put-other (E.key f) r total (E.members b) different))
 key-extend ident s {t} actual owns | just b | E.building | just w | just f | just q | just c | just oldBytes with E.canRequeue (E.payload f Nat.∸ (E.fragmentLimit s Nat.⊓ E.payload f)) q
 ...         | false = case actual of λ ()
 ...         | true = case just-injective actual of λ { refl →
  key-touch s t (E.key f) c (E.cell (E.fixedLane c) (E.keyHeld c) (E.sent c)) cellFound refl refl sameAll owns }
  where
  total = Model.headerBytes Nat.+ (E.fragmentLimit s Nat.⊓ E.payload f) Nat.+ previousBytes (just oldBytes)
  replacement = record b { members = put (E.key f) total (E.members b); pending = nothing; sdus = suc (E.sdus b) }
  sameMember : ∀ r → membership r replacement ≡ membership r b
  sameMember r with r ≟ E.key f
  ... | yes refl = trans (cong (λ m → outstanding b Nat.* present m) (lookup-put (E.key f) total (E.members b)))
   (sym (cong (λ m → outstanding b Nat.* present m) prior))
  ... | no different = cong (λ m → outstanding b Nat.* present m)
   (lookup-put-other (E.key f) r total (E.members b) different)
  sameAll : ∀ r → count (membership r) (put ident replacement (E.batches s)) ≡ count (membership r) (E.batches s)
  sameAll r = count-put-same (membership r) ident replacement (E.batches s) b found (sameMember r)
 key-extend ident s actual owns | just b | E.building | just w | just f | just q | nothing | _ = case actual of λ ()
 key-extend ident s actual owns | just b | E.building | just w | nothing | _ = case actual of λ ()
 key-extend ident s actual owns | just b | E.building | just w | just _ | nothing = case actual of λ ()
 key-extend ident s actual owns | just b | E.building | nothing = case actual of λ ()
 key-extend ident s actual owns | just b | E.ready | _ = case actual of λ ()
 key-extend ident s actual owns | just b | E.failed | _ = case actual of λ ()
 key-extend ident s actual owns | just b | E.written | _ = case actual of λ ()

 -- Per-key held-count conservation over every actual kernel action. Only the
 -- write case consumes batch-member uniqueness, carried by members-step.
 key-advance : ∀ ident a s {t} → E.step (E.advance ident a) s ≡ just t → KeyOwnership s → KeyOwnership t
 key-advance ident a s actual owns with advance-shape ident a s actual
 ... | W , L , refl = owns
 key-step : ∀ action s {t} → E.step action s ≡ just t → MembersUnique s → KeyOwnership s → KeyOwnership t
 key-step (E.createWanton w k) s actual unique = key-create w k s actual
 key-step (E.appendPayload w n) s actual unique = key-send w n s actual
 key-step (E.takeFirst lane) s actual unique = key-open lane s actual
 key-step (E.selectDemand ident) s actual unique = key-select ident s actual
 key-step (E.takeFragment ident) s actual unique = key-extend ident s actual
 key-step (E.finishBatch ident) s actual unique = key-finish ident s actual
 key-step (E.writeAccount ident) s actual unique = key-write ident s actual unique
 key-step (E.writeFailed ident) s actual unique = key-failure ident s actual
 key-step (E.advance ident a) s actual unique = key-advance ident a s actual
 key-runs : ∀ {s actions t} → Runs s actions t → MembersUnique s → KeyOwnership s → KeyOwnership t
 key-runs stop unique owns = owns
 key-runs (more {s = s} {a = action} actual path) unique owns =
  key-runs path (members-step action s actual unique) (key-step action s actual unique owns)
 from-initial-keys : ∀ {plan limit bound keys start actions current} →
  E.initial plan limit bound keys ≡ just start → Runs start actions current → KeyOwnership current
 from-initial-keys {plan} {limit} {bound} {keys} initialized path =
  key-runs path (initial-members plan limit bound keys initialized) (initial-key-ownership plan limit bound keys initialized)

 -- Reachable key cells are nonnegative because each counts owned batches.
 from-initial-key-nonnegative : ∀ {plan limit bound keys start actions current} k c →
  E.initial plan limit bound keys ≡ just start → Runs start actions current →
  lookup k (E.cells current) ≡ just c → CellNonnegative c
 from-initial-key-nonnegative {plan} {limit} {bound} {keys} k c initialized path found
  rewrite from-initial-keys {plan} {limit} {bound} {keys} initialized path k c found = +≤+ z≤n

 -- Every batch member names an existing source key cell. Cells are never
 -- created after initialization, and only already-present keys are written.
 MembersConfigured : E.State → Set
 MembersConfigured s = ∀ ident b k n → lookup ident (E.batches s) ≡ just b →
  lookup k (E.members b) ≡ just n → Σ E.Cell (λ c → lookup k (E.cells s) ≡ just c)
 CellsForward : E.State → E.State → Set
 CellsForward before after = ∀ k c → lookup k (E.cells before) ≡ just c →
  Σ E.Cell (λ c′ → lookup k (E.cells after) ≡ just c′)
 MembersBacked : E.State → E.Batch → Set
 MembersBacked s b = ∀ k n → lookup k (E.members b) ≡ just n → Σ E.Cell (λ c → lookup k (E.cells s) ≡ just c)

 lookup-put-cases : ∀ {K V : Set} ⦃ _ : DecEq K ⦄ (i q : K) (r v : V) bs → lookup q (put i r bs) ≡ just v →
  (q ≡ i × v ≡ r) ⊎ lookup q bs ≡ just v
 lookup-put-cases i q r v bs found with q ≟ i
 ... | yes refl = inj₁ (refl , just-injective (trans (sym found) (lookup-put q r bs)))
 ... | no different = inj₂ (trans (sym (lookup-put-other i q r bs different)) found)
 cell-put-forward : ∀ (k k′ : Key) (v : E.Cell) cs c → lookup k cs ≡ just c →
  Σ E.Cell (λ c′ → lookup k (put k′ v cs) ≡ just c′)
 cell-put-forward k k′ v cs c found with k ≟ k′
 ... | yes refl = v , lookup-put k v cs
 ... | no different = c , trans (lookup-put-other k′ k v cs different) found
 cells-same-forward : ∀ before after → E.cells after ≡ E.cells before → CellsForward before after
 cells-same-forward before after same k c found = c , trans (cong (lookup k) same) found

 configured-change : ∀ before after ident replacement → CellsForward before after →
  E.batches after ≡ put ident replacement (E.batches before) → MembersBacked before replacement →
  MembersConfigured before → MembersConfigured after
 configured-change before after ident replacement forward changed fresh configured i b k n found member
  with lookup-put-cases ident i replacement b (E.batches before) (trans (sym (cong (lookup i) changed)) found)
 ... | inj₁ (refl , refl) = forward k (proj₁ (fresh k n member)) (proj₂ (fresh k n member))
 ... | inj₂ old = forward k (proj₁ (configured i b k n old member)) (proj₂ (configured i b k n old member))
 same-members-backed : ∀ s ident old replacement → lookup ident (E.batches s) ≡ just old →
  E.members replacement ≡ E.members old → MembersConfigured s → MembersBacked s replacement
 same-members-backed s ident old replacement found same configured k n member =
  configured ident old k n found (trans (cong (lookup k) (sym same)) member)
 -- A row rewrite keeping cells and members preserves configuration.
 configured-row : ∀ before after ident old replacement → lookup ident (E.batches before) ≡ just old →
  E.members replacement ≡ E.members old → E.batches after ≡ put ident replacement (E.batches before) →
  E.cells after ≡ E.cells before → MembersConfigured before → MembersConfigured after
 configured-row before after ident old replacement found same changed cellsSame configured =
  configured-change before after ident replacement (cells-same-forward before after cellsSame) changed
   (same-members-backed before ident old replacement found same configured) configured

 initial-configured : ∀ plan limit bound keys {s} → E.initial plan limit bound keys ≡ just s → MembersConfigured s
 initial-configured plan limit bound keys actual with E.makeCells plan keys
 ... | nothing = case actual of λ ()
 ... | just cs = case just-injective actual of λ { refl → λ ident b k n found member → case found of λ () }
 configured-create : ∀ w k s {t} → E.step (E.createWanton w k) s ≡ just t → MembersConfigured s → MembersConfigured t
 configured-create w k s actual owns with lookup w (E.wantons s) | lookup k (E.cells s)
 ... | nothing | just _ = case just-injective actual of λ { refl → owns }
 ... | nothing | nothing = case actual of λ ()
 ... | just _ | _ = case actual of λ ()
 configured-send : ∀ w bytes s {t} → E.step (E.appendPayload w bytes) s ≡ just t → MembersConfigured s → MembersConfigured t
 configured-send w bytes s actual owns with lookup w (E.wantons s)
 ... | nothing = case actual of λ ()
 ... | just f with Relation.Nullary.does (E.payload f Nat.<? Model.softLimit)
 ...   | false = case actual of λ ()
 ...   | true with E.payload f
 ...     | suc _ = case just-injective actual of λ { refl → owns }
 ...     | zero with lookup (E.key f) (E.cells s)
 ...       | nothing = case actual of λ ()
 ...       | just c with lookup (E.fixedLane c) (E.queues s)
 ...         | nothing = case actual of λ ()
 ...         | just q with Relation.Nullary.does (Data.List.length q Nat.<? 100)
 ...           | false = case actual of λ ()
 ...           | true = case just-injective actual of λ { refl → owns }
 configured-finish : ∀ ident s {t} → E.step (E.finishBatch ident) s ≡ just t → MembersConfigured s → MembersConfigured t
 configured-finish ident s {t} actual owns with lookup ident (E.batches s) in found
 ... | nothing = case actual of λ ()
 ... | just b with E.phase b | E.pending b | E.belowCaps b s
 ...   | E.building | nothing | false = case just-injective actual of λ { refl →
  configured-row s t ident b (record b { phase = E.ready }) found refl refl refl owns }
 ...   | E.building | nothing | true = case actual of λ ()
 ...   | E.building | just _ | _ = case actual of λ ()
 ...   | E.ready | _ | _ = case actual of λ ()
 ...   | E.failed | _ | _ = case actual of λ ()
 ...   | E.written | _ | _ = case actual of λ ()
 configured-select : ∀ ident s {t} → E.step (E.selectDemand ident) s ≡ just t → MembersConfigured s → MembersConfigured t
 configured-select ident s {t} actual owns with lookup ident (E.batches s) in found
 ... | nothing = case actual of λ ()
 ... | just b with E.phase b | E.pending b | E.belowCaps b s
 ...   | E.building | nothing | true with lookup (E.lane b) (E.queues s)
 ...     | nothing = case actual of λ ()
 ...     | just [] = case just-injective actual of λ { refl →
  configured-row s t ident b (record b { phase = E.ready }) found refl refl refl owns }
 ...     | just (w ∷ rest) = case just-injective actual of λ { refl →
  configured-row s t ident b (record b { pending = just w }) found refl refl refl owns }
 configured-select ident s actual owns | just b | E.building | nothing | false = case actual of λ ()
 configured-select ident s actual owns | just b | E.building | just _ | _ = case actual of λ ()
 configured-select ident s actual owns | just b | E.ready | _ | _ = case actual of λ ()
 configured-select ident s actual owns | just b | E.failed | _ | _ = case actual of λ ()
 configured-select ident s actual owns | just b | E.written | _ | _ = case actual of λ ()
 configured-failure : ∀ ident before {after} → E.step (E.writeFailed ident) before ≡ just after →
  MembersConfigured before → MembersConfigured after
 configured-failure ident before {after} actual owns with failure ident before actual
 ... | failed-batch b found phase refl sameCells sameHeld sameWantons sameQueues =
  configured-row before after ident b (record b { phase = E.failed }) found refl refl refl owns
 configured-write : ∀ ident before {after} → E.step (E.writeAccount ident) before ≡ just after →
  MembersUnique before → MembersConfigured before → MembersConfigured after
 configured-write ident before {after} actual unique owns with write ident before actual
 ... | wrote-batch b cs found phase pending held enabled accounted refl =
  configured-change before after ident (record b { phase = E.written }) forward refl
   (same-members-backed before ident b (record b { phase = E.written }) found refl owns) owns
  where
  forward : CellsForward before after
  forward k c cellFound with account-cell k (E.members b) (E.cells before) c
   (lookup-batch-value BatchMembersUnique ident (E.batches before) b unique found) cellFound accounted
  ... | accounted-cell current foundCurrent heldShape sentShape laneSame = current , foundCurrent

 singleton-key : ∀ (k k′ : Key) (v n : ℕ) → lookup k ((k′ , v) ∷ []) ≡ just n → k ≡ k′
 singleton-key k k′ v n found with k ≟ k′
 ... | yes same = same
 ... | no _ = case found of λ ()
 configured-open : ∀ l s {t} → E.step (E.takeFirst l) s ≡ just t → MembersConfigured s → MembersConfigured t
 configured-open l s {t} actual owns with E.laneBusy l (E.batches s) | lookup l (E.queues s) |
  lookup (E.nextBatch s) (E.batches s)
 ... | false | just (w ∷ rest) | nothing with lookup w (E.wantons s)
 ...   | nothing = case actual of λ ()
 ...   | just f with lookup (E.key f) (E.cells s) in cellFound
 ...     | nothing = case actual of λ ()
 ...     | just c = case just-injective actual of λ { refl →
  configured-change s t (E.nextBatch s) created
   (λ k old found → cell-put-forward k (E.key f) newCell (E.cells s) old found) refl backed owns }
  where
  bytes = Model.headerBytes Nat.+ (E.fragmentLimit s Nat.⊓ E.payload f)
  created = E.batch l ((E.key f , bytes) ∷ []) nothing E.building 1
  newCell = E.cell (E.fixedLane c) (E.keyHeld c Int.+ + 1) (E.sent c)
  backed : MembersBacked s created
  backed k n member = case singleton-key k (E.key f) bytes n member of λ { refl → c , cellFound }
 configured-open l s actual owns | true | _ | _ = case actual of λ ()
 configured-open l s actual owns | false | nothing | _ = case actual of λ ()
 configured-open l s actual owns | false | just [] | _ = case actual of λ ()
 configured-open l s actual owns | false | just (_ ∷ _) | just _ = case actual of λ ()

 configured-extend : ∀ ident s {t} → E.step (E.takeFragment ident) s ≡ just t → MembersConfigured s → MembersConfigured t
 configured-extend ident s {t} actual owns with lookup ident (E.batches s) in found
 ... | nothing = case actual of λ ()
 ... | just b with E.phase b | E.pending b
 ...   | E.building | just w with lookup w (E.wantons s) | lookup (E.lane b) (E.queues s)
 ...     | just f | just q with lookup (E.key f) (E.cells s) in cellFound | lookup (E.key f) (E.members b)
 ...       | just c | nothing with E.canRequeue (E.payload f Nat.∸ (E.fragmentLimit s Nat.⊓ E.payload f)) q
 ...         | false = case actual of λ ()
 ...         | true = case just-injective actual of λ { refl →
  configured-change s t ident replacement
   (λ k old present → cell-put-forward k (E.key f) newCell (E.cells s) old present) refl backed owns }
  where
  total = Model.headerBytes Nat.+ (E.fragmentLimit s Nat.⊓ E.payload f) Nat.+ previousBytes nothing
  replacement = record b { members = put (E.key f) total (E.members b); pending = nothing; sdus = suc (E.sdus b) }
  newCell = E.cell (E.fixedLane c) (E.keyHeld c Int.+ + 1) (E.sent c)
  backed : MembersBacked s replacement
  backed k n member with lookup-put-cases (E.key f) k total n (E.members b) member
  ... | inj₁ (refl , _) = c , cellFound
  ... | inj₂ old = owns ident b k n found old
 configured-extend ident s {t} actual owns | just b | E.building | just w | just f | just q | just c | just oldBytes with E.canRequeue (E.payload f Nat.∸ (E.fragmentLimit s Nat.⊓ E.payload f)) q
 ...         | false = case actual of λ ()
 ...         | true = case just-injective actual of λ { refl →
  configured-change s t ident replacement
   (λ k old present → cell-put-forward k (E.key f) newCell (E.cells s) old present) refl backed owns }
  where
  total = Model.headerBytes Nat.+ (E.fragmentLimit s Nat.⊓ E.payload f) Nat.+ previousBytes (just oldBytes)
  replacement = record b { members = put (E.key f) total (E.members b); pending = nothing; sdus = suc (E.sdus b) }
  newCell = E.cell (E.fixedLane c) (E.keyHeld c) (E.sent c)
  backed : MembersBacked s replacement
  backed k n member with lookup-put-cases (E.key f) k total n (E.members b) member
  ... | inj₁ (refl , _) = c , cellFound
  ... | inj₂ old = owns ident b k n found old
 configured-extend ident s actual owns | just b | E.building | just w | just f | just q | nothing | _ = case actual of λ ()
 configured-extend ident s actual owns | just b | E.building | just w | nothing | _ = case actual of λ ()
 configured-extend ident s actual owns | just b | E.building | just w | just _ | nothing = case actual of λ ()
 configured-extend ident s actual owns | just b | E.building | nothing = case actual of λ ()
 configured-extend ident s actual owns | just b | E.ready | _ = case actual of λ ()
 configured-extend ident s actual owns | just b | E.failed | _ = case actual of λ ()
 configured-extend ident s actual owns | just b | E.written | _ = case actual of λ ()

 configured-advance : ∀ ident a s {t} → E.step (E.advance ident a) s ≡ just t → MembersConfigured s → MembersConfigured t
 configured-advance ident a s actual owns with advance-shape ident a s actual
 ... | W , L , refl = owns
 configured-step : ∀ action s {t} → E.step action s ≡ just t → MembersUnique s → MembersConfigured s → MembersConfigured t
 configured-step (E.createWanton w k) s actual unique = configured-create w k s actual
 configured-step (E.appendPayload w n) s actual unique = configured-send w n s actual
 configured-step (E.takeFirst lane) s actual unique = configured-open lane s actual
 configured-step (E.selectDemand ident) s actual unique = configured-select ident s actual
 configured-step (E.takeFragment ident) s actual unique = configured-extend ident s actual
 configured-step (E.finishBatch ident) s actual unique = configured-finish ident s actual
 configured-step (E.writeAccount ident) s actual unique = configured-write ident s actual unique
 configured-step (E.writeFailed ident) s actual unique = configured-failure ident s actual
 configured-step (E.advance ident a) s actual unique = configured-advance ident a s actual

 -- The four component invariants travel together along actual kernel runs.
 record Reachable (s : E.State) : Set where
  constructor reachable
  field global : GlobalOwnership s
        keys : KeyOwnership s
        unique : MembersUnique s
        configured : MembersConfigured s
 reachable-step : ∀ action s {t} → E.step action s ≡ just t → Reachable s → Reachable t
 reachable-step action s actual (reachable global keys unique configured) = reachable
  (global-step action s actual global) (key-step action s actual unique keys)
  (members-step action s actual unique) (configured-step action s actual unique configured)
 reachable-runs : ∀ {s actions t} → Runs s actions t → Reachable s → Reachable t
 reachable-runs stop valid = valid
 reachable-runs (more {s = s} {a = action} actual path) valid = reachable-runs path (reachable-step action s actual valid)
 from-initial-reachable : ∀ {plan limit bound keys start actions current} →
  E.initial plan limit bound keys ≡ just start → Runs start actions current → Reachable current
 from-initial-reachable {plan} {limit} {bound} {keys} initialized path = reachable-runs path
  (reachable (initial-global plan limit bound keys initialized) (initial-key-ownership plan limit bound keys initialized)
   (initial-members plan limit bound keys initialized) (initial-configured plan limit bound keys initialized))

 -- A found row contributes its own value to a store-wide count.
 count-found : ∀ (f : E.Batch → ℕ) (ident : ℕ) (bs : Store ℕ E.Batch) b → lookup ident bs ≡ just b → Σ ℕ (λ m → count f bs ≡ f b Nat.+ m)
 count-found f ident [] b found = case found of λ ()
 count-found f ident ((q , x) ∷ bs) b found with ident ≟ q
 ... | yes _ = case just-injective found of λ { refl → count f bs , refl }
 ... | no _ with count-found f ident bs b found
 ...   | m , split = f x Nat.+ m , trans (cong (f x Nat.+_) split)
  (trans (sym (NatProperties.+-assoc (f x) (f b) m))
   (trans (cong (Nat._+ m) (NatProperties.+-comm (f x) (f b))) (NatProperties.+-assoc (f b) (f x) m)))

 member-present-cons : ∀ (k : Key) (v : ℕ) (ms ys : Store Key ℕ) →
  All (λ binding → Σ ℕ (λ w → lookup (proj₁ binding) ms ≡ just w)) ys →
  All (λ binding → Σ ℕ (λ w → lookup (proj₁ binding) ((k , v) ∷ ms) ≡ just w)) ys
 member-present-cons k v ms [] [] = []
 member-present-cons k v ms ((q , _) ∷ ys) ((w , found) ∷ rest) = shifted ∷ member-present-cons k v ms ys rest
  where
  shifted : Σ ℕ (λ u → lookup q ((k , v) ∷ ms) ≡ just u)
  shifted with q ≟ k
  ... | yes _ = v , refl
  ... | no _ = w , found
 -- Each listed member key is found by lookup, even with shadowed entries.
 members-present : ∀ (ms : Store Key ℕ) → All (λ binding → Σ ℕ (λ w → lookup (proj₁ binding) ms ≡ just w)) ms
 members-present [] = []
 members-present ((k , v) ∷ ms) = (v , lookup-head k v ms) ∷ member-present-cons k v ms ms (members-present ms)

 AccountReady : Store Key E.Cell → Key → Set
 AccountReady cs k = Σ E.Cell (λ c → lookup k cs ≡ just c × Model.positive (E.keyHeld c) ≡ true)
 ready-shift : ∀ (k : Key) (v : E.Cell) (cs : Store Key E.Cell) (ms : Store Key ℕ) → All (λ binding → k ≢ proj₁ binding) ms →
  All (λ binding → AccountReady cs (proj₁ binding)) ms → All (λ binding → AccountReady (put k v cs) (proj₁ binding)) ms
 ready-shift k v cs [] [] [] = []
 ready-shift k v cs ((q , _) ∷ ms) (apart ∷ aparts) ((c , found , positive) ∷ ready) =
  (c , trans (lookup-put-other k q v cs (λ same → apart (sym same))) found , positive) ∷ ready-shift k v cs ms aparts ready
 -- Distinct members with present, positive cells always complete accounting.
 account-succeeds : ∀ (ms : Store Key ℕ) (cs : Store Key E.Cell) → UniqueKeys ms → All (λ binding → AccountReady cs (proj₁ binding)) ms →
  Σ (Store Key E.Cell) (λ after → E.account ms cs ≡ just after)
 account-succeeds [] cs [] [] = cs , refl
 account-succeeds ((k , bytes) ∷ ms) cs (apart ∷ unique) ((c , found , positive) ∷ ready)
  rewrite found | positive = account-succeeds ms
   (put k (E.cell (E.fixedLane c) (E.keyHeld c Int.- + 1) (E.sent c Nat.+ bytes)) cs) unique
   (ready-shift k (E.cell (E.fixedLane c) (E.keyHeld c Int.- + 1) (E.sent c Nat.+ bytes)) cs ms apart ready)

 positive-suc : ∀ n m → n ≡ suc m → Model.positive (+ n) ≡ true
 positive-suc n m same rewrite same = refl
 member-ready : ∀ ident s b → Reachable s → lookup ident (E.batches s) ≡ just b → E.phase b ≡ E.ready →
  ∀ k → Σ ℕ (λ v → lookup k (E.members b) ≡ just v) → AccountReady (E.cells s) k
 member-ready ident s b (reachable global keys unique configured) found phase k (v , member)
  with configured ident b k v found member
 ... | c , cellFound with count-found (membership k) ident (E.batches s) b found
 ...   | m , split = c , cellFound , trans (cong Model.positive (keys k c cellFound))
  (positive-suc (count (membership k) (E.batches s)) m (trans split one))
  where
  one : membership k b Nat.+ m ≡ suc m
  one rewrite phase | member = refl

 -- Source positivity guards never refuse a reachable ready, unpending batch:
 -- the actual write/account transaction is enabled for it.
 -- M4: the batch's wait stage must also admit the write (always true for a
 -- plain mux's unwaited batch; for a scheduled lane, after the locked write).
 write-enabled : ∀ ident s b → Reachable s → lookup ident (E.batches s) ≡ just b →
  E.phase b ≡ E.ready → E.pending b ≡ nothing →
  Model.writeEnabled (Model.modeOf (E.layout s) (E.lane b)) (lookup ident (E.waits s)) ≡ true →
  Σ E.State (λ t → E.step (E.writeAccount ident) s ≡ just t)
 write-enabled ident s b valid found phase pending enabled
  with account-succeeds (E.members b) (E.cells s)
   (lookup-batch-value BatchMembersUnique ident (E.batches s) b (Reachable.unique valid) found)
   (All.map (λ {binding} → member-ready ident s b valid found phase (proj₁ binding)) (members-present (E.members b)))
 ... | cs , accounted with count-found outstanding ident (E.batches s) b found
 ...   | m , split = result
  where
  heldPositive : Model.positive (E.runHeld s) ≡ true
  heldPositive = trans (cong Model.positive (Reachable.global valid))
   (positive-suc (count outstanding (E.batches s)) m (trans split one))
   where
   one : outstanding b Nat.+ m ≡ suc m
   one rewrite phase = refl
  result : Σ E.State (λ t → E.step (E.writeAccount ident) s ≡ just t)
  result rewrite found | phase | pending | heldPositive | enabled | accounted = _ , refl
 from-initial-write-enabled : ∀ {plan limit bound keys start actions current} ident b →
  E.initial plan limit bound keys ≡ just start → Runs start actions current →
  lookup ident (E.batches current) ≡ just b → E.phase b ≡ E.ready → E.pending b ≡ nothing →
  Model.writeEnabled (Model.modeOf (E.layout current) (E.lane b)) (lookup ident (E.waits current)) ≡ true →
  Σ E.State (λ t → E.step (E.writeAccount ident) current ≡ just t)
 from-initial-write-enabled {plan} {limit} {bound} {keys} {current = current} ident b initialized path =
  write-enabled ident current b (from-initial-reachable {plan} {limit} {bound} {keys} initialized path)

 -- At most one unwritten (building, ready or failed) batch owns each lane.
 -- Failed batches keep their lane busy, matching the source egress loop.
 LaneExclusive : E.State → Set
 LaneExclusive s = ∀ i j bi bj → lookup i (E.batches s) ≡ just bi → lookup j (E.batches s) ≡ just bj →
  E.lane bi ≡ E.lane bj → outstanding bi ≡ 1 → outstanding bj ≡ 1 → i ≡ j
 written-outstanding : ∀ b → E.phase b ≡ E.written → outstanding b ≡ 0
 written-outstanding b phase rewrite phase = refl
 lane-free : ∀ l (bs : Store ℕ E.Batch) i b → E.laneBusy l bs ≡ false → lookup i bs ≡ just b →
  E.lane b ≡ l → outstanding b ≡ 1 → ⊥
 lane-free l [] i b free found same live = case found of λ ()
 lane-free l ((q , x) ∷ bs) i b free found same live with l ≟ E.lane x
 ... | no different with i ≟ q
 ...   | yes _ = case just-injective found of λ { refl → different (sym same) }
 ...   | no _ = lane-free l bs i b free found same live
 lane-free l ((q , x) ∷ bs) i b free found same live | yes sameLane with E.phase x in phase
 ...   | E.written with i ≟ q
 ...     | yes _ = case just-injective found of λ { refl → case trans (sym live) (written-outstanding x phase) of λ () }
 ...     | no _ = lane-free l bs i b free found same live
 lane-free l ((q , x) ∷ bs) i b free found same live | yes sameLane | E.building = case free of λ ()
 lane-free l ((q , x) ∷ bs) i b free found same live | yes sameLane | E.ready = case free of λ ()
 lane-free l ((q , x) ∷ bs) i b free found same live | yes sameLane | E.failed = case free of λ ()

 -- Rewriting one row without moving its lane or reviving it preserves exclusivity.
 lane-row : ∀ before after ident old replacement → lookup ident (E.batches before) ≡ just old →
  E.lane replacement ≡ E.lane old → (outstanding replacement ≡ 1 → outstanding old ≡ 1) →
  E.batches after ≡ put ident replacement (E.batches before) → LaneExclusive before → LaneExclusive after
 lane-row before after ident old replacement found laneSame liveBack changed exclusive i j bi bj fi fj sameLane li lj
  with lookup-put-cases ident i replacement bi (E.batches before) (trans (sym (cong (lookup i) changed)) fi)
     | lookup-put-cases ident j replacement bj (E.batches before) (trans (sym (cong (lookup j) changed)) fj)
 ... | inj₁ (refl , refl) | inj₁ (refl , refl) = refl
 ... | inj₁ (refl , refl) | inj₂ oldJ = exclusive i j old bj found oldJ (trans (sym laneSame) sameLane) (liveBack li) lj
 ... | inj₂ oldI | inj₁ (refl , refl) = exclusive i j bi old oldI found (trans sameLane laneSame) li (liveBack lj)
 ... | inj₂ oldI | inj₂ oldJ = exclusive i j bi bj oldI oldJ sameLane li lj
 -- A fresh row may claim only a lane that no unwritten batch owns.
 lane-fresh : ∀ before after ident created → lookup ident (E.batches before) ≡ nothing →
  E.laneBusy (E.lane created) (E.batches before) ≡ false →
  E.batches after ≡ put ident created (E.batches before) → LaneExclusive before → LaneExclusive after
 lane-fresh before after ident created fresh free changed exclusive i j bi bj fi fj sameLane li lj
  with lookup-put-cases ident i created bi (E.batches before) (trans (sym (cong (lookup i) changed)) fi)
     | lookup-put-cases ident j created bj (E.batches before) (trans (sym (cong (lookup j) changed)) fj)
 ... | inj₁ (refl , refl) | inj₁ (refl , refl) = refl
 ... | inj₁ (refl , refl) | inj₂ oldJ = ⊥-elim (lane-free (E.lane created) (E.batches before) j bj free oldJ (sym sameLane) lj)
 ... | inj₂ oldI | inj₁ (refl , refl) = ⊥-elim (lane-free (E.lane created) (E.batches before) i bi free oldI sameLane li)
 ... | inj₂ oldI | inj₂ oldJ = exclusive i j bi bj oldI oldJ sameLane li lj

 initial-lanes : ∀ plan limit bound keys {s} → E.initial plan limit bound keys ≡ just s → LaneExclusive s
 initial-lanes plan limit bound keys actual with E.makeCells plan keys
 ... | nothing = case actual of λ ()
 ... | just cs = case just-injective actual of λ { refl → λ i j bi bj fi → case fi of λ () }
 lanes-create : ∀ w k s {t} → E.step (E.createWanton w k) s ≡ just t → LaneExclusive s → LaneExclusive t
 lanes-create w k s actual owns with lookup w (E.wantons s) | lookup k (E.cells s)
 ... | nothing | just _ = case just-injective actual of λ { refl → owns }
 ... | nothing | nothing = case actual of λ ()
 ... | just _ | _ = case actual of λ ()
 lanes-send : ∀ w bytes s {t} → E.step (E.appendPayload w bytes) s ≡ just t → LaneExclusive s → LaneExclusive t
 lanes-send w bytes s actual owns with lookup w (E.wantons s)
 ... | nothing = case actual of λ ()
 ... | just f with Relation.Nullary.does (E.payload f Nat.<? Model.softLimit)
 ...   | false = case actual of λ ()
 ...   | true with E.payload f
 ...     | suc _ = case just-injective actual of λ { refl → owns }
 ...     | zero with lookup (E.key f) (E.cells s)
 ...       | nothing = case actual of λ ()
 ...       | just c with lookup (E.fixedLane c) (E.queues s)
 ...         | nothing = case actual of λ ()
 ...         | just q with Relation.Nullary.does (Data.List.length q Nat.<? 100)
 ...           | false = case actual of λ ()
 ...           | true = case just-injective actual of λ { refl → owns }
 lanes-open : ∀ l s {t} → E.step (E.takeFirst l) s ≡ just t → LaneExclusive s → LaneExclusive t
 lanes-open l s {t} actual owns with E.laneBusy l (E.batches s) in free | lookup l (E.queues s) |
  lookup (E.nextBatch s) (E.batches s) in fresh
 ... | false | just (w ∷ rest) | nothing with lookup w (E.wantons s)
 ...   | nothing = case actual of λ ()
 ...   | just f with lookup (E.key f) (E.cells s)
 ...     | nothing = case actual of λ ()
 ...     | just c = case just-injective actual of λ { refl →
  lane-fresh s t (E.nextBatch s) created fresh free refl owns }
  where
  created = E.batch l ((E.key f , Model.headerBytes Nat.+ (E.fragmentLimit s Nat.⊓ E.payload f)) ∷ [])
   nothing E.building 1
 lanes-open l s actual owns | true | _ | _ = case actual of λ ()
 lanes-open l s actual owns | false | nothing | _ = case actual of λ ()
 lanes-open l s actual owns | false | just [] | _ = case actual of λ ()
 lanes-open l s actual owns | false | just (_ ∷ _) | just _ = case actual of λ ()
 lanes-finish : ∀ ident s {t} → E.step (E.finishBatch ident) s ≡ just t → LaneExclusive s → LaneExclusive t
 lanes-finish ident s {t} actual owns with lookup ident (E.batches s) in found
 ... | nothing = case actual of λ ()
 ... | just b with E.phase b in phase | E.pending b | E.belowCaps b s
 ...   | E.building | nothing | false = case just-injective actual of λ { refl →
  lane-row s t ident b (record b { phase = E.ready }) found refl (λ _ → building-one b phase) refl owns }
 ...   | E.building | nothing | true = case actual of λ ()
 ...   | E.building | just _ | _ = case actual of λ ()
 ...   | E.ready | _ | _ = case actual of λ ()
 ...   | E.failed | _ | _ = case actual of λ ()
 ...   | E.written | _ | _ = case actual of λ ()
 lanes-select : ∀ ident s {t} → E.step (E.selectDemand ident) s ≡ just t → LaneExclusive s → LaneExclusive t
 lanes-select ident s {t} actual owns with lookup ident (E.batches s) in found
 ... | nothing = case actual of λ ()
 ... | just b with E.phase b in phase | E.pending b | E.belowCaps b s
 ...   | E.building | nothing | true with lookup (E.lane b) (E.queues s)
 ...     | nothing = case actual of λ ()
 ...     | just [] = case just-injective actual of λ { refl →
  lane-row s t ident b (record b { phase = E.ready }) found refl (λ _ → building-one b phase) refl owns }
 ...     | just (w ∷ rest) = case just-injective actual of λ { refl →
  lane-row s t ident b (record b { pending = just w }) found refl (λ live → live) refl owns }
 lanes-select ident s actual owns | just b | E.building | nothing | false = case actual of λ ()
 lanes-select ident s actual owns | just b | E.building | just _ | _ = case actual of λ ()
 lanes-select ident s actual owns | just b | E.ready | _ | _ = case actual of λ ()
 lanes-select ident s actual owns | just b | E.failed | _ | _ = case actual of λ ()
 lanes-select ident s actual owns | just b | E.written | _ | _ = case actual of λ ()
 lanes-extend : ∀ ident s {t} → E.step (E.takeFragment ident) s ≡ just t → LaneExclusive s → LaneExclusive t
 lanes-extend ident s {t} actual owns with lookup ident (E.batches s) in found
 ... | nothing = case actual of λ ()
 ... | just b with E.phase b | E.pending b
 ...   | E.building | just w with lookup w (E.wantons s) | lookup (E.lane b) (E.queues s)
 ...     | just f | just q with lookup (E.key f) (E.cells s) | lookup (E.key f) (E.members b)
 ...       | just c | previous with E.canRequeue (E.payload f Nat.∸ (E.fragmentLimit s Nat.⊓ E.payload f)) q
 ...         | false = case actual of λ ()
 ...         | true = case just-injective actual of λ { refl →
  lane-row s t ident b _ found refl (λ live → live) refl owns }
 lanes-extend ident s actual owns | just b | E.building | just w | just f | just q | nothing | _ = case actual of λ ()
 lanes-extend ident s actual owns | just b | E.building | just w | nothing | _ = case actual of λ ()
 lanes-extend ident s actual owns | just b | E.building | just w | just _ | nothing = case actual of λ ()
 lanes-extend ident s actual owns | just b | E.building | nothing = case actual of λ ()
 lanes-extend ident s actual owns | just b | E.ready | _ = case actual of λ ()
 lanes-extend ident s actual owns | just b | E.failed | _ = case actual of λ ()
 lanes-extend ident s actual owns | just b | E.written | _ = case actual of λ ()
 lanes-write : ∀ ident before {after} → E.step (E.writeAccount ident) before ≡ just after →
  LaneExclusive before → LaneExclusive after
 lanes-write ident before {after} actual owns with write ident before actual
 ... | wrote-batch b cs found phase pending held enabled accounted refl =
  lane-row before after ident b (record b { phase = E.written }) found refl (λ ()) refl owns
 lanes-failure : ∀ ident before {after} → E.step (E.writeFailed ident) before ≡ just after →
  LaneExclusive before → LaneExclusive after
 lanes-failure ident before {after} actual owns with failure ident before actual
 ... | failed-batch b found phase refl sameCells sameHeld sameWantons sameQueues =
  lane-row before after ident b (record b { phase = E.failed }) found refl (live phase) refl owns
  where
  live : E.phase b ≡ E.building ⊎ E.phase b ≡ E.ready → outstanding (record b { phase = E.failed }) ≡ 1 → outstanding b ≡ 1
  live (inj₁ building) _ = building-one b building
  live (inj₂ ready) _ rewrite ready = refl
 lanes-advance : ∀ ident a s {t} → E.step (E.advance ident a) s ≡ just t → LaneExclusive s → LaneExclusive t
 lanes-advance ident a s actual valid with advance-shape ident a s actual
 ... | W , L , refl = valid
 lanes-step : ∀ action s {t} → E.step action s ≡ just t → LaneExclusive s → LaneExclusive t
 lanes-step (E.createWanton w k) = lanes-create w k
 lanes-step (E.appendPayload w n) = lanes-send w n
 lanes-step (E.takeFirst lane) = lanes-open lane
 lanes-step (E.selectDemand ident) = lanes-select ident
 lanes-step (E.takeFragment ident) = lanes-extend ident
 lanes-step (E.finishBatch ident) = lanes-finish ident
 lanes-step (E.writeAccount ident) = lanes-write ident
 lanes-step (E.writeFailed ident) = lanes-failure ident
 lanes-step (E.advance ident a) = lanes-advance ident a
 lanes-runs : ∀ {s actions t} → Runs s actions t → LaneExclusive s → LaneExclusive t
 lanes-runs stop valid = valid
 lanes-runs (more {s = s} {a = action} actual path) valid = lanes-runs path (lanes-step action s actual valid)
 from-initial-lanes : ∀ {plan limit bound keys start actions current} →
  E.initial plan limit bound keys ≡ just start → Runs start actions current → LaneExclusive current
 from-initial-lanes {plan} {limit} {bound} {keys} initialized path =
  lanes-runs path (initial-lanes plan limit bound keys initialized)

 -- Each existing key cell survives every step with its fixed lane unchanged.
 CellKept : E.State → E.State → Set
 CellKept before after = ∀ k c → lookup k (E.cells before) ≡ just c →
  Σ E.Cell (λ c′ → lookup k (E.cells after) ≡ just c′ × E.fixedLane c′ ≡ E.fixedLane c)
 kept-same : ∀ before after → E.cells after ≡ E.cells before → CellKept before after
 kept-same before after same k c found = c , trans (cong (lookup k) same) found , refl
 kept-put : ∀ before after (k′ : Key) old v → lookup k′ (E.cells before) ≡ just old →
  E.cells after ≡ put k′ v (E.cells before) → E.fixedLane v ≡ E.fixedLane old → CellKept before after
 kept-put before after k′ old v oldFound changed laneSame k c found with k ≟ k′
 ... | yes refl = v , trans (cong (lookup k) changed) (lookup-put k v (E.cells before)) ,
   trans laneSame (cong E.fixedLane (just-injective (trans (sym oldFound) found)))
 ... | no different = c , trans (cong (lookup k) changed) (trans (lookup-put-other k′ k v (E.cells before) different) found) , refl
 kept-trans : ∀ s t u → CellKept s t → CellKept t u → CellKept s u
 kept-trans s t u st tu k c found with st k c found
 ... | c′ , found′ , lane′ with tu k c′ found′
 ...   | c″ , found″ , lane″ = c″ , found″ , trans lane″ lane′

 -- Wanton identities are never removed and never change their source key.
 WantonKept : E.State → E.State → Set
 WantonKept before after = ∀ w f → lookup w (E.wantons before) ≡ just f →
  Σ E.Wanton (λ f′ → lookup w (E.wantons after) ≡ just f′ × E.key f′ ≡ E.key f)
 wanton-same : ∀ before after → E.wantons after ≡ E.wantons before → WantonKept before after
 wanton-same before after same x f found = f , trans (cong (lookup x) same) found , refl
 wanton-fresh : ∀ before after w v → lookup w (E.wantons before) ≡ nothing →
  E.wantons after ≡ put w v (E.wantons before) → WantonKept before after
 wanton-fresh before after w v absent changed x f found with x ≟ w
 ... | yes refl = case trans (sym absent) found of λ ()
 ... | no different = f , trans (cong (lookup x) changed) (trans (lookup-put-other w x v (E.wantons before) different) found) , refl
 wanton-put : ∀ before after w old v → lookup w (E.wantons before) ≡ just old →
  E.wantons after ≡ put w v (E.wantons before) → E.key v ≡ E.key old → WantonKept before after
 wanton-put before after w old v oldFound changed keySame x f found with x ≟ w
 ... | yes refl = v , trans (cong (lookup x) changed) (lookup-put x v (E.wantons before)) ,
   trans keySame (cong E.key (just-injective (trans (sym oldFound) found)))
 ... | no different = f , trans (cong (lookup x) changed) (trans (lookup-put-other w x v (E.wantons before) different) found) , refl

 -- Queue and pending demand names an existing wanton whose key cell is fixed
 -- to that queue's (or batch's) lane.
 Routed : E.State → Model.Lane → ℕ → Set
 Routed s l w = Σ E.Wanton (λ f → lookup w (E.wantons s) ≡ just f ×
  Σ E.Cell (λ c → lookup (E.key f) (E.cells s) ≡ just c × E.fixedLane c ≡ l))
 routed-mono : ∀ s t l w → WantonKept s t → CellKept s t → Routed s l w → Routed t l w
 routed-mono s t l w wk ck (f , wf , c , cf , lane) with wk w f wf
 ... | f′ , wf′ , keySame with ck (E.key f) c cf
 ...   | c′ , cf′ , laneSame = f′ , wf′ , c′ , trans (cong (λ k → lookup k (E.cells t)) keySame) cf′ , trans laneSame lane
 all-routed-mono : ∀ s t l (q : List ℕ) → WantonKept s t → CellKept s t → All (Routed s l) q → All (Routed t l) q
 all-routed-mono s t l q wk ck = All.map (λ {w} → routed-mono s t l w wk ck)
 record Routing (s : E.State) : Set where
  constructor routing
  field queues-routed : ∀ l q → lookup l (E.queues s) ≡ just q → All (Routed s l) q
        pending-routed : ∀ ident b w → lookup ident (E.batches s) ≡ just b → E.pending b ≡ just w → Routed s (E.lane b) w

 QueuesFrom PendingFrom : E.State → E.State → Set
 QueuesFrom before after = ∀ l q → lookup l (E.queues after) ≡ just q → All (Routed before l) q
 PendingFrom before after = ∀ ident b w → lookup ident (E.batches after) ≡ just b → E.pending b ≡ just w →
  Routed before (E.lane b) w
 kept-routing : ∀ before after → WantonKept before after → CellKept before after →
  QueuesFrom before after → PendingFrom before after → CellKept before after × Routing after
 kept-routing before after wk ck qf pf = ck , routing
  (λ l q found → all-routed-mono before after l q wk ck (qf l q found))
  (λ ident b w found pend → routed-mono before after (E.lane b) w wk ck (pf ident b w found pend))
 queues-from-same : ∀ before after → E.queues after ≡ E.queues before → Routing before → QueuesFrom before after
 queues-from-same before after same valid l q found = Routing.queues-routed valid l q (trans (cong (lookup l) (sym same)) found)
 queues-from-put : ∀ before after l′ q′ → E.queues after ≡ put l′ q′ (E.queues before) → All (Routed before l′) q′ →
  Routing before → QueuesFrom before after
 queues-from-put before after l′ q′ changed fresh valid l q found
  with lookup-put-cases l′ l q′ q (E.queues before) (trans (sym (cong (lookup l) changed)) found)
 ... | inj₁ (refl , refl) = fresh
 ... | inj₂ old = Routing.queues-routed valid l q old
 pending-from-same : ∀ before after → E.batches after ≡ E.batches before → Routing before → PendingFrom before after
 pending-from-same before after same valid ident b w found = Routing.pending-routed valid ident b w (trans (cong (lookup ident) (sym same)) found)
 pending-from-row : ∀ before after ident replacement → E.batches after ≡ put ident replacement (E.batches before) →
  (∀ w → E.pending replacement ≡ just w → Routed before (E.lane replacement) w) → Routing before → PendingFrom before after
 pending-from-row before after ident replacement changed fresh valid i b w found pend
  with lookup-put-cases ident i replacement b (E.batches before) (trans (sym (cong (lookup i) changed)) found)
 ... | inj₁ (refl , refl) = fresh w pend
 ... | inj₂ old = Routing.pending-routed valid i b w old pend
 pending-kept : ∀ before ident old → lookup ident (E.batches before) ≡ just old → Routing before →
  ∀ w → E.pending old ≡ just w → Routed before (E.lane old) w
 pending-kept before ident old found valid w pend = Routing.pending-routed valid ident old w found pend
 remainder-all : ∀ {P : ℕ → Set} w n rest → All P rest → P w → All P (E.remainderQueue w n rest)
 remainder-all w zero rest all pw = all
 remainder-all w (suc n) rest all pw = AllProperties.++⁺ all (pw ∷ [])

 empty-queues-empty : ∀ ls l q → lookup l (E.emptyQueues ls) ≡ just q → q ≡ []
 empty-queues-empty [] l q found = case found of λ ()
 empty-queues-empty (l′ ∷ ls) l q found with l ≟ l′
 ... | yes _ = sym (just-injective found)
 ... | no _ = empty-queues-empty ls l q found
 initial-routing : ∀ plan limit bound keys {s} → E.initial plan limit bound keys ≡ just s → Routing s
 initial-routing plan limit bound keys actual with E.makeCells plan keys
 ... | nothing = case actual of λ ()
 ... | just cs = case just-injective actual of λ { refl → routing
  (λ l q found → case empty-queues-empty (Model.lanes plan) l q found of λ { refl → [] })
  (λ ident b w found → case found of λ ()) }

 routing-create : ∀ w k s {t} → E.step (E.createWanton w k) s ≡ just t → Routing s → CellKept s t × Routing t
 routing-create w k s {t} actual valid with lookup w (E.wantons s) in absent | lookup k (E.cells s)
 ... | nothing | just _ = case just-injective actual of λ { refl → kept-routing s t
  (wanton-fresh s t w (E.wanton k 0) absent refl) (kept-same s t refl)
  (queues-from-same s t refl valid) (pending-from-same s t refl valid) }
 ... | nothing | nothing = case actual of λ ()
 ... | just _ | _ = case actual of λ ()
 routing-send : ∀ w bytes s {t} → E.step (E.appendPayload w bytes) s ≡ just t → Routing s → CellKept s t × Routing t
 routing-send w bytes s {t} actual valid with lookup w (E.wantons s) in found
 ... | nothing = case actual of λ ()
 ... | just f with Relation.Nullary.does (E.payload f Nat.<? Model.softLimit)
 ...   | false = case actual of λ ()
 ...   | true with E.payload f
 ...     | suc n = case just-injective actual of λ { refl → kept-routing s t
  (wanton-put s t w f _ found refl refl) (kept-same s t refl)
  (queues-from-same s t refl valid) (pending-from-same s t refl valid) }
 ...     | zero with lookup (E.key f) (E.cells s) in cellFound
 ...       | nothing = case actual of λ ()
 ...       | just c with lookup (E.fixedLane c) (E.queues s) in queue
 ...         | nothing = case actual of λ ()
 ...         | just q with Relation.Nullary.does (Data.List.length q Nat.<? 100)
 ...           | false = case actual of λ ()
 ...           | true = case just-injective actual of λ { refl → kept-routing s t
  (wanton-put s t w f _ found refl refl) (kept-same s t refl)
  (queues-from-put s t (E.fixedLane c) _ refl
   (AllProperties.++⁺ (Routing.queues-routed valid (E.fixedLane c) q queue) ((f , found , c , cellFound , refl) ∷ [])) valid)
  (pending-from-same s t refl valid) }
 routing-open : ∀ l s {t} → E.step (E.takeFirst l) s ≡ just t → Routing s → CellKept s t × Routing t
 routing-open l s {t} actual valid with E.laneBusy l (E.batches s) | lookup l (E.queues s) in queue |
  lookup (E.nextBatch s) (E.batches s)
 ... | false | just (w ∷ rest) | nothing with lookup w (E.wantons s) in wantonFound
 ...   | nothing = case actual of λ ()
 ...   | just f with lookup (E.key f) (E.cells s) in cellFound
 ...     | nothing = case actual of λ ()
 ...     | just c = case just-injective actual of λ { refl → kept-routing s t
  (wanton-put s t w f _ wantonFound refl refl) (kept-put s t (E.key f) c _ cellFound refl refl)
  (queues-from-put s t l _ refl
   (remainder-all w (E.payload f Nat.∸ (E.fragmentLimit s Nat.⊓ E.payload f)) rest (All.tail routedAll) (All.head routedAll)) valid)
  (pending-from-row s t (E.nextBatch s) _ refl (λ x ()) valid) }
  where
  routedAll = Routing.queues-routed valid l (w ∷ rest) queue
 routing-open l s actual valid | true | _ | _ = case actual of λ ()
 routing-open l s actual valid | false | nothing | _ = case actual of λ ()
 routing-open l s actual valid | false | just [] | _ = case actual of λ ()
 routing-open l s actual valid | false | just (_ ∷ _) | just _ = case actual of λ ()
 routing-finish : ∀ ident s {t} → E.step (E.finishBatch ident) s ≡ just t → Routing s → CellKept s t × Routing t
 routing-finish ident s {t} actual valid with lookup ident (E.batches s) in found
 ... | nothing = case actual of λ ()
 ... | just b with E.phase b | E.pending b | E.belowCaps b s
 ...   | E.building | nothing | false = case just-injective actual of λ { refl → kept-routing s t
  (wanton-same s t refl) (kept-same s t refl) (queues-from-same s t refl valid)
  (pending-from-row s t ident (record b { phase = E.ready }) refl (pending-kept s ident b found valid) valid) }
 ...   | E.building | nothing | true = case actual of λ ()
 ...   | E.building | just _ | _ = case actual of λ ()
 ...   | E.ready | _ | _ = case actual of λ ()
 ...   | E.failed | _ | _ = case actual of λ ()
 ...   | E.written | _ | _ = case actual of λ ()
 routing-select : ∀ ident s {t} → E.step (E.selectDemand ident) s ≡ just t → Routing s → CellKept s t × Routing t
 routing-select ident s {t} actual valid with lookup ident (E.batches s) in found
 ... | nothing = case actual of λ ()
 ... | just b with E.phase b | E.pending b | E.belowCaps b s
 ...   | E.building | nothing | true with lookup (E.lane b) (E.queues s) in queue
 ...     | nothing = case actual of λ ()
 ...     | just [] = case just-injective actual of λ { refl → kept-routing s t
  (wanton-same s t refl) (kept-same s t refl) (queues-from-same s t refl valid)
  (pending-from-row s t ident (record b { phase = E.ready }) refl (pending-kept s ident b found valid) valid) }
 ...     | just (w ∷ rest) = case just-injective actual of λ { refl → kept-routing s t
  (wanton-same s t refl) (kept-same s t refl)
  (queues-from-put s t (E.lane b) rest refl (All.tail routedAll) valid)
  (pending-from-row s t ident (record b { pending = just w }) refl
   (λ x selected → case just-injective selected of λ { refl → All.head routedAll }) valid) }
  where
  routedAll = Routing.queues-routed valid (E.lane b) (w ∷ rest) queue
 routing-select ident s actual valid | just b | E.building | nothing | false = case actual of λ ()
 routing-select ident s actual valid | just b | E.building | just _ | _ = case actual of λ ()
 routing-select ident s actual valid | just b | E.ready | _ | _ = case actual of λ ()
 routing-select ident s actual valid | just b | E.failed | _ | _ = case actual of λ ()
 routing-select ident s actual valid | just b | E.written | _ | _ = case actual of λ ()
 routing-extend : ∀ ident s {t} → E.step (E.takeFragment ident) s ≡ just t → Routing s → CellKept s t × Routing t
 routing-extend ident s {t} actual valid with lookup ident (E.batches s) in found
 ... | nothing = case actual of λ ()
 ... | just b with E.phase b | E.pending b in pend
 ...   | E.building | just w with lookup w (E.wantons s) in wantonFound | lookup (E.lane b) (E.queues s) in queue
 ...     | just f | just q with lookup (E.key f) (E.cells s) in cellFound | lookup (E.key f) (E.members b)
 ...       | just c | previous with E.canRequeue (E.payload f Nat.∸ (E.fragmentLimit s Nat.⊓ E.payload f)) q
 ...         | false = case actual of λ ()
 ...         | true = case just-injective actual of λ { refl → kept-routing s t
  (wanton-put s t w f _ wantonFound refl refl) (kept-put s t (E.key f) c _ cellFound refl refl)
  (queues-from-put s t (E.lane b) _ refl
   (remainder-all w (E.payload f Nat.∸ (E.fragmentLimit s Nat.⊓ E.payload f)) q
    (Routing.queues-routed valid (E.lane b) q queue) (Routing.pending-routed valid ident b w found pend)) valid)
  (pending-from-row s t ident _ refl (λ x ()) valid) }
 routing-extend ident s actual valid | just b | E.building | just w | just f | just q | nothing | _ = case actual of λ ()
 routing-extend ident s actual valid | just b | E.building | just w | nothing | _ = case actual of λ ()
 routing-extend ident s actual valid | just b | E.building | just w | just _ | nothing = case actual of λ ()
 routing-extend ident s actual valid | just b | E.building | nothing = case actual of λ ()
 routing-extend ident s actual valid | just b | E.ready | _ = case actual of λ ()
 routing-extend ident s actual valid | just b | E.failed | _ = case actual of λ ()
 routing-extend ident s actual valid | just b | E.written | _ = case actual of λ ()
 routing-failure : ∀ ident before {after} → E.step (E.writeFailed ident) before ≡ just after →
  Routing before → CellKept before after × Routing after
 routing-failure ident before {after} actual valid with failure ident before actual
 ... | failed-batch b found phase refl sameCells sameHeld sameWantons sameQueues = kept-routing before after
  (wanton-same before after refl) (kept-same before after refl) (queues-from-same before after refl valid)
  (pending-from-row before after ident (record b { phase = E.failed }) refl (pending-kept before ident b found valid) valid)
 routing-write : ∀ ident before {after} → E.step (E.writeAccount ident) before ≡ just after →
  MembersUnique before → Routing before → CellKept before after × Routing after
 routing-write ident before {after} actual unique valid with write ident before actual
 ... | wrote-batch b cs found phase pending held enabled accounted refl = kept-routing before after
  (wanton-same before after refl) ck (queues-from-same before after refl valid)
  (pending-from-row before after ident (record b { phase = E.written }) refl (pending-kept before ident b found valid) valid)
  where
  ck : CellKept before after
  ck k c cellFound with account-cell k (E.members b) (E.cells before) c
   (lookup-batch-value BatchMembersUnique ident (E.batches before) b unique found) cellFound accounted
  ... | accounted-cell current foundCurrent heldShape sentShape laneSame = current , foundCurrent , laneSame

 routing-advance : ∀ ident a s {t} → E.step (E.advance ident a) s ≡ just t → Routing s → CellKept s t × Routing t
 routing-advance ident a s actual valid with advance-shape ident a s actual
 ... | W , L , refl = (λ k c found → c , found , refl) , routing (Routing.queues-routed valid) (Routing.pending-routed valid)
 routing-step : ∀ action s {t} → E.step action s ≡ just t → MembersUnique s → Routing s → CellKept s t × Routing t
 routing-step (E.createWanton w k) s actual unique = routing-create w k s actual
 routing-step (E.appendPayload w n) s actual unique = routing-send w n s actual
 routing-step (E.takeFirst lane) s actual unique = routing-open lane s actual
 routing-step (E.selectDemand ident) s actual unique = routing-select ident s actual
 routing-step (E.takeFragment ident) s actual unique = routing-extend ident s actual
 routing-step (E.finishBatch ident) s actual unique = routing-finish ident s actual
 routing-step (E.writeAccount ident) s actual unique = routing-write ident s actual unique
 routing-step (E.writeFailed ident) s actual unique = routing-failure ident s actual
 routing-step (E.advance ident a) s actual unique = routing-advance ident a s actual
 routing-runs : ∀ {s actions t} → Runs s actions t → MembersUnique s → Routing s → CellKept s t × Routing t
 routing-runs {s} stop unique valid = (λ k c found → c , found , refl) , valid
 routing-runs (more {s = s} {t = next} {u = last} {a = action} actual path) unique valid with routing-step action s actual unique valid
 ... | kept , valid′ with routing-runs path (members-step action s actual unique) valid′
 ...   | kept′ , final = kept-trans s next last kept kept′ , final
 -- Reachable demand routing, and immutable key-to-lane assignment from the
 -- initialized cells, along every finite run of actual kernel actions.
 from-initial-routing : ∀ {plan limit bound keys start actions current} →
  E.initial plan limit bound keys ≡ just start → Runs start actions current → CellKept start current × Routing current
 from-initial-routing {plan} {limit} {bound} {keys} initialized path = routing-runs path
  (initial-members plan limit bound keys initialized) (initial-routing plan limit bound keys initialized)
