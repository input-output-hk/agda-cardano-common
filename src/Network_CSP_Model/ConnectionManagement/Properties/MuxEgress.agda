{-# OPTIONS --guardedness #-}

-- Local observations of the M1 batch accounting kernel. These certify actual
-- model steps; grant ledgers, bearer execution and Haskell refinement are not
-- conclusions of the component lemmas.
module ConnectionManagement.Properties.MuxEgress where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥-elim)
open import Data.Integer using (ℤ; +_; -[1+_]; _≤_; +≤+)
import Data.Integer as Int
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; zero; suc; z≤n)
import Data.Nat as Nat
import Data.Nat.Properties as NatProperties
open import Data.Product using (Σ; _×_; _,_; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)
open import Class.DecEq using (DecEq; _≟_)
open import Class.DecEq.Instances using (DecEq-ℕ)
open import ConnectionManagement.Store using (Store; lookup; put)
open import ConnectionManagement.Properties.Entries using (lookup-put)
open import ConnectionManagement.Properties.Stores using (put-values; put-unique; UniqueKeys; lookup-put-other; apart-lookup)
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
        after-shape : after ≡ record before
          { batches = put ident (record captured { phase = E.failed }) (E.batches before) }
        cells-same : E.cells after ≡ E.cells before
        held-same : E.runHeld after ≡ E.runHeld before
        wantons-same : E.wantons after ≡ E.wantons before
        queues-same : E.queues after ≡ E.queues before
 failure : ∀ ident before {after} → E.step (E.writeFailed ident) before ≡ just after → Failure ident before after
 failure ident before actual with lookup ident (E.batches before) in found
 ... | nothing = case actual of λ ()
 ... | just b with E.phase b in phase
 ...   | E.building = case just-injective actual of λ { refl → failed-batch b found (inj₁ phase) refl refl refl refl refl }
 ...   | E.ready = case just-injective actual of λ { refl → failed-batch b found (inj₂ phase) refl refl refl refl refl }
 ...   | E.failed = case actual of λ ()
 ...   | E.written = case actual of λ ()

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
        actual-account : E.account (E.members captured) (E.cells before) ≡ just cellsAfter
        after-shape : after ≡ record before
          { cells = cellsAfter; runHeld = E.runHeld before Int.- + 1
          ; batches = put ident (record captured { phase = E.written }) (E.batches before) }
 write : ∀ ident before {after} → E.step (E.writeAccount ident) before ≡ just after → Write ident before after
 write ident before actual with lookup ident (E.batches before) in found
 ... | nothing = case actual of λ ()
 ... | just b with E.phase b in phase | E.pending b in pending | Model.positive (E.runHeld before) in held
 ...   | E.ready | nothing | true with E.account (E.members b) (E.cells before) in accounted
 ...     | nothing = case actual of λ ()
 ...     | just cs = case just-injective actual of λ { refl → wrote-batch b cs found phase pending held accounted refl }
 write ident before actual | just b | E.building | _ | _ = case actual of λ ()
 write ident before actual | just b | E.ready | just _ | _ = case actual of λ ()
 write ident before actual | just b | E.ready | nothing | false = case actual of λ ()
 write ident before actual | just b | E.failed | _ | _ = case actual of λ ()
 write ident before actual | just b | E.written | _ | _ = case actual of λ ()

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
 ... | wrote-batch b cs found phase pending held accounted refl =
  written-refused ident (record before
   { cells = cs; runHeld = E.runHeld before Int.- + 1
   ; batches = put ident (record b { phase = E.written }) (E.batches before) })
   (record b { phase = E.written })
   (lookup-put ident (record b { phase = E.written }) (E.batches before)) refl
 failure-not-write : ∀ ident before {after} → E.step (E.writeFailed ident) before ≡ just after →
  E.step (E.writeAccount ident) after ≡ nothing
 failure-not-write ident before actual with failure ident before actual
 ... | failed-batch b found phase refl sameCells sameHeld sameWantons sameQueues =
  failed-refused ident (record before
   { batches = put ident (record b { phase = E.failed }) (E.batches before) })
   (record b { phase = E.failed })
   (lookup-put ident (record b { phase = E.failed }) (E.batches before)) refl

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
 ... | wrote-batch b cs found phase pending held accounted refl with positive-predecessor (E.runHeld before) held
 ...   | n , same rewrite same = +≤+ z≤n

 initial-global : ∀ plan limit bound keys {s} → E.initial plan limit bound keys ≡ just s → GlobalOwnership s
 initial-global plan limit bound keys actual with E.makeCells plan keys
 ... | nothing = case actual of λ ()
 ... | just cs = case just-injective actual of λ { refl → refl }

 global-write : ∀ ident before {after} → E.step (E.writeAccount ident) before ≡ just after →
  GlobalOwnership before → GlobalOwnership after
 global-write ident before actual owns with write ident before actual
 ... | wrote-batch b cs found phase pending held accounted refl = result
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
   ; batches = put ident (record b { phase = E.written }) (E.batches before) })
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

 global-step : ∀ action s {t} → E.step action s ≡ just t → GlobalOwnership s → GlobalOwnership t
 global-step (E.createWanton w k) = global-create w k
 global-step (E.appendPayload w n) = global-send w n
 global-step (E.takeFirst lane) = global-open lane
 global-step (E.selectDemand ident) = global-select ident
 global-step (E.takeFragment ident) = global-extend ident
 global-step (E.finishBatch ident) = global-finish ident
 global-step (E.writeAccount ident) = global-write ident
 global-step (E.writeFailed ident) = global-failure ident
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
 ... | wrote-batch b cs found phase pending held accounted refl = account-nonnegative (E.members b) (E.cells before) accounted valid

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
 ... | wrote-batch b cs found phase pending held accounted refl =
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
 members-step : ∀ action s {t} → E.step action s ≡ just t → MembersUnique s → MembersUnique t
 members-step (E.createWanton w k) = members-create w k
 members-step (E.appendPayload w n) = members-send w n
 members-step (E.takeFirst lane) = members-open lane
 members-step (E.selectDemand ident) = members-select ident
 members-step (E.takeFragment ident) = members-extend ident
 members-step (E.finishBatch ident) = members-finish ident
 members-step (E.writeAccount ident) = members-write ident
 members-step (E.writeFailed ident) = members-failure ident
 members-runs : ∀ {s actions t} → Runs s actions t → MembersUnique s → MembersUnique t
 members-runs stop valid = valid
 members-runs (more {s = s} {a = action} actual path) valid = members-runs path (members-step action s actual valid)
 from-initial-members : ∀ {plan limit bound keys start actions current} →
  E.initial plan limit bound keys ≡ just start → Runs start actions current → MembersUnique current
 from-initial-members {plan} {limit} {bound} {keys} initialized path =
  members-runs path (initial-members plan limit bound keys initialized)
