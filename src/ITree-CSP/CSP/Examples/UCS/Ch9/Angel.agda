{-# OPTIONS --guardedness #-}

-- UCS chapter 9 §9.4: ANGELIC CHOICE AS A CSP-LIKE OPERATOR.  A port of
--
--   fdr-examples/ucs/chapter09/angel.csp   (A.W. Roscoe, July 2010)
--
-- WHY THIS FILE.  `bangelic(P,Q)` is NOT a primitive: §9.4's whole point is that a
-- CSP-LIKE operator outside the core language can be BUILT from the core.  So the
-- model below is a genuine composition of the operators this development already has
-- — two renamings (`CSP.Rename`), interleaving, interface parallel, throw, hiding and
-- sequential composition — exactly as the script writes it:
--
--   ER(i,P) = P[[x <- ev.x.i.V, x <- ev.x.i.H | x <- Sigma]]
--   CR(P)   = P[[ev.x.i.V <- x, ev.x.i.H <- tau | x <- Sigma, i <- Lane]]
--             [[tick1 <- tau, tick2 <- tau, tick <- tau]]
--   bangelic(P,Q) = CR(((ER(1,(P;tick1 -> STOP)) ||| ER(2,(Q;tick2 -> STOP)))
--                       [|{|ev,tick1,tick2|}|] BReg)
--                       [|{tick}|> SKIP) \ {tau}
--
-- Two lanes run P and Q side by side; the regulator BReg keeps them on the SAME
-- visible trace (whichever lane runs an event VISIBLY, the other must catch up on it
-- HIDDEN), and the throw on `tick` is what lets the winner's √ escape.  This is the
-- second real customer for the throw operator `_⟦_▷_` (the first is
-- CSP.Examples.UCS.Ch7.Throw).
--
-- ═══════════════════════════════════════════════════════════════════════════════════
-- WHAT IS AND IS NOT PROVED  (read this before citing anything from here)
-- ═══════════════════════════════════════════════════════════════════════════════════
-- The script carries three asserts:
--
--   (1) assert bangelic(bangelic(A,B),C) :[deterministic]      (angel.csp:99)
--   (2) assert bangelic(bangelic(C,B),A) :[deterministic]      (angel.csp:100)
--   (3) assert ABC [FD= bangelic(bangelic(A,B),C)              (angel.csp:106)
--
-- Re-derived from `Semantics.Determinism` and `Semantics.FailuresDivergences`, all
-- three are expected TRUE (see §B.0 for the derivation).  NONE OF THE THREE IS PROVED
-- HERE.  What §B contains is TRANSITION SANITY for the construction — see §B.0 for the
-- precise blocker and what discharging the asserts would take.  Nothing in this file
-- may be read as a proof of an assert.  This is the MODEL-ONLY posture of
-- CSP.Examples.UCS.Ch7.Counter, applied to a file that DOES carry asserts.
--
-- CLASSICAL FOOTPRINT: none.  No `postulate`, no LEM/`dne` seam, no FSim bridge — the
-- same side as CSP.Examples.UCS.Ch6.FailDiv and CSP.Examples.UCS.Ch8.Lazic, not the
-- sanctioned `Hide-fsim`/`αpar-fsim-df` seams CSP.Examples.UCS.Ch5.NCopyL rides.  No
-- NON_TERMINATING/TERMINATING pragma, no sized types, no old-style `mutual` block
-- (forward declarations only), no holes.
--
-- GUARDEDNESS: the recursions here (the `BReg`/`Reg` families) are DIRECT, not through
-- a CSP operator, so the inlined-`react`-copattern idiom of
-- CSP.Examples.UCS.Ch3.SyncIdentity's REPEAT applies and the wall documented in
-- Ch7/Throw and Ch5/MergeSort is not hit: no constructed-solution-plus-bisimulation
-- workaround was needed.  `bangelic` itself is not recursive at all.

module CSP.Examples.UCS.Ch9.Angel where

open import Level using (Lift; lift) renaming (zero to lzero; suc to lsuc)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic renaming (⊤ to ⊤poly) using ()
open import Data.Empty using (⊥)
open import Data.Bool using (Bool; true; false; T)
open import Data.Nat using (ℕ; zero; suc; _<ᵇ_; _∸_)
open import Data.List using (List; []; _∷_; _∷ʳ_; length)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (T?)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq; Irrelevant⇒DecEq)

open import Process_Trees
open PTree

------------------------------------------------------------------------------------
-- §A. The model.
------------------------------------------------------------------------------------

-- Sigma = {a,b,c}: the three basic events.  They are modelled as the three VALUES of
-- one channel `sig` rather than as three nullary channels, so that the `x` of the
-- script's `ev.x.i.s` is literally this same object; event-wise the two encodings are
-- the same three events.  Read `σa`/`σb`/`σc` as the script's `a`/`b`/`c`.
data Sig : Set where σa σb σc : Sig

-- Lane = {1,2}: which of the two angelic alternatives an event belongs to
data Lane : Set where ln1 ln2 : Lane

-- datatype Status = V | H: a visible (V) or a hidden (H) copy of a basic event
data Status : Set where V H : Status

-- The alphabet.  NOTE the naming hazard: `tauCh` is the script's ORDINARY VISIBLE
-- channel `tau` (line 16, `channel tau`), later hidden by `\{tau}`.  It is NOT the
-- LTS's silent τ of `Semantics.LTS`; the two are unrelated and the spelling here is
-- deliberately different so they can never be confused.
data AEv : Set → Set where
  sig              : AEv Sig                       -- a, b, c
  ev               : AEv (Sig × Lane × Status)     -- channel ev:Sigma.Lane.Status
  tick tick1 tick2 : AEv ⊤                         -- termination-regulating events
  tauCh            : AEv ⊤                         -- the VISIBLE channel `tau`

-- decidable equality on the event indices, as every CSP operator module needs
AEv-≟ : (x y : AnyTypes AEv) → Dec (x ≡ y)
AEv-≟ (_ , sig)          (_ , sig)    = yes refl
AEv-≟ (_ , sig)          (_ , ev)     = no (λ ())
AEv-≟ (_ , sig)          (_ , tick)   = no (λ ())
AEv-≟ (_ , sig)          (_ , tick1)  = no (λ ())
AEv-≟ (_ , sig)          (_ , tick2)  = no (λ ())
AEv-≟ (_ , sig)          (_ , tauCh)  = no (λ ())
AEv-≟ (_ , ev)           (_ , sig)    = no (λ ())
AEv-≟ (_ , ev)           (_ , ev)     = yes refl
AEv-≟ (_ , ev)           (_ , tick)   = no (λ ())
AEv-≟ (_ , ev)           (_ , tick1)  = no (λ ())
AEv-≟ (_ , ev)           (_ , tick2)  = no (λ ())
AEv-≟ (_ , ev)           (_ , tauCh)  = no (λ ())
AEv-≟ (_ , tick)         (_ , sig)    = no (λ ())
AEv-≟ (_ , tick)         (_ , ev)     = no (λ ())
AEv-≟ (_ , tick)         (_ , tick)   = yes refl
AEv-≟ (_ , tick)         (_ , tick1)  = no (λ ())
AEv-≟ (_ , tick)         (_ , tick2)  = no (λ ())
AEv-≟ (_ , tick)         (_ , tauCh)  = no (λ ())
AEv-≟ (_ , tick1)        (_ , sig)    = no (λ ())
AEv-≟ (_ , tick1)        (_ , ev)     = no (λ ())
AEv-≟ (_ , tick1)        (_ , tick)   = no (λ ())
AEv-≟ (_ , tick1)        (_ , tick1)  = yes refl
AEv-≟ (_ , tick1)        (_ , tick2)  = no (λ ())
AEv-≟ (_ , tick1)        (_ , tauCh)  = no (λ ())
AEv-≟ (_ , tick2)        (_ , sig)    = no (λ ())
AEv-≟ (_ , tick2)        (_ , ev)     = no (λ ())
AEv-≟ (_ , tick2)        (_ , tick)   = no (λ ())
AEv-≟ (_ , tick2)        (_ , tick1)  = no (λ ())
AEv-≟ (_ , tick2)        (_ , tick2)  = yes refl
AEv-≟ (_ , tick2)        (_ , tauCh)  = no (λ ())
AEv-≟ (_ , tauCh)        (_ , sig)    = no (λ ())
AEv-≟ (_ , tauCh)        (_ , ev)     = no (λ ())
AEv-≟ (_ , tauCh)        (_ , tick)   = no (λ ())
AEv-≟ (_ , tauCh)        (_ , tick1)  = no (λ ())
AEv-≟ (_ , tauCh)        (_ , tick2)  = no (λ ())
AEv-≟ (_ , tauCh)        (_ , tauCh)  = yes refl

-- decidable equality on Sigma (needed for `c!v` outputs and for the regulator's
-- `ev!y!i!H` offer, which compares the head of its pending queue with the event)
_Sig≟_ : (x y : Sig) → Dec (x ≡ y)
σa Sig≟ σa = yes refl
σa Sig≟ σb = no (λ ())
σa Sig≟ σc = no (λ ())
σb Sig≟ σa = no (λ ())
σb Sig≟ σb = yes refl
σb Sig≟ σc = no (λ ())
σc Sig≟ σa = no (λ ())
σc Sig≟ σb = no (λ ())
σc Sig≟ σc = yes refl

open import CSP.Operators AEv-≟

instance
  -- `_□_` asks for a DecEq on the return type; `⊤poly {lzero}` is irrelevant
  DecEq-⊤poly : DecEq (⊤poly {lzero})
  DecEq-⊤poly = Irrelevant⇒DecEq (λ { (lift _) (lift _) → refl })

  -- `c ! v ⟶ P` pins one carried value, so it asks for a DecEq on the carrier
  DecEq-Sig : DecEq Sig
  DecEq-Sig = record { _≟_ = _Sig≟_ }

open import Semantics.LTS {E = AEv} {I = ExtI AEv}

-- every process in this file lives over one alphabet and returns ⊤ (CSP's √)
AProc : Set₁
AProc = PTree AEv (ExtI AEv) (⊤poly {lzero})

------------------------------------------------------------------------------------
-- §A.1  The two renamings, over the SINGLE alphabet AEv (E₁ = E₂ = AEv, ι = id).
------------------------------------------------------------------------------------

-- the identity event injection: this file renames WITHIN one alphabet
idι : ∀ {A} → AEv A → AEv A
idι e = e

-- its (total) inverse
idι⁻¹ : ∀ {A} → AEv A → Maybe (AEv A)
idι⁻¹ e = just e

-- …which is a left inverse on the nose, so `ExtI` index re-tagging is the identity
idι-linv : ∀ {A} (e : AEv A) → idι⁻¹ (idι e) ≡ just e
idι-linv _ = refl

open import CSP.Rename {E₁ = AEv} {E₂ = AEv} idι idι⁻¹ idι-linv

-- concrete-event constructors (an event index paired with its carried value)
sigC : Sig → ConcEvent₁
sigC x = ((Sig , sig) , x)

-- the four nullary concrete events
tickC tick1C tick2C tauC : ConcEvent₁
tickC  = ((⊤ , tick)  , tt)
tick1C = ((⊤ , tick1) , tt)
tick2C = ((⊤ , tick2) , tt)
tauC   = ((⊤ , tauCh) , tt)

-- ER's inverse map:  ER(i,P) = P[[x <- ev.x.i.V, x <- ev.x.i.H | x <- Sigma]].
-- Forward this FANS OUT (each basic event x gets both an ev.x.i.V and an ev.x.i.H
-- image), so BACKWARDS it is a function — one source per target — which is exactly
-- what `renameInv` consumes.  The `ev` channel is left FIXED by the CSPM renaming
-- (only Sigma is in its domain), but the operand of ER is always `R ; tick_i -> STOP`
-- for an R over Sigma alone, so that identity component is vacuous and is dropped:
-- ev.x.i.s's only live source is the basic event x.
erInv : Lane → (bt : AnyTypes AEv) → proj₁ bt → Maybe ConcEvent₁
erInv ln1 (_ , ev) (x , ln1 , _) = just (sigC x)
erInv ln1 (_ , ev) (_ , ln2 , _) = nothing
erInv ln2 (_ , ev) (_ , ln1 , _) = nothing
erInv ln2 (_ , ev) (x , ln2 , _) = just (sigC x)
erInv _   (_ , sig)   _ = nothing               -- basic events are renamed AWAY
erInv _   (_ , tick)  _ = just tickC            -- everything else is left fixed
erInv _   (_ , tick1) _ = just tick1C
erInv _   (_ , tick2) _ = just tick2C
erInv _   (_ , tauCh) _ = just tauC

-- CR's first renaming, forwards: [[ev.x.i.V <- x, ev.x.i.H <- tau | x<-Sigma, i<-Lane]].
-- It is a FUNCTION forwards (many-to-one: every hidden copy collapses onto `tau`, and
-- the two lanes' visible copies collapse onto the same basic event), so backwards it
-- FANS IN and `renameInv` does not apply — the general relational operator does.
cr1F : ConcEvent₁ → ConcEvent₁
cr1F ((_ , ev)    , (x , _ , V)) = sigC x
cr1F ((_ , ev)    , (_ , _ , H)) = tauC
cr1F ((_ , sig)   , x)           = sigC x
cr1F ((_ , tick)  , _)           = tickC
cr1F ((_ , tick1) , _)           = tick1C
cr1F ((_ , tick2) , _)           = tick2C
cr1F ((_ , tauCh) , _)           = tauC

-- …as a renaming RELATION (the shape `_⟦_¿_⟧` takes)
cr1R : ConcEvent₁ → ConcEvent₂ → Set₁
cr1R e f = cr1F e ≡ f

-- …and its per-target preimage enumerator: two lanes fan in onto each basic event,
-- and all six hidden copies (plus `tau` itself) fan in onto `tau`.
cr1Pre : (bt : AnyTypes AEv) (b : proj₁ bt)
       → List (Σ[ at ∈ AnyTypes AEv ] Σ[ a ∈ proj₁ at ] cr1R (at , a) (bt , b))
cr1Pre (_ , sig) x  = ((_ , ev) , (x , ln1 , V) , refl)
                    ∷ ((_ , ev) , (x , ln2 , V) , refl)
                    ∷ ((_ , sig) , x , refl)
                    ∷ []
cr1Pre (_ , ev)    _  = []                       -- ev.* is entirely renamed away
cr1Pre (_ , tick)  tt = ((_ , tick)  , tt , refl) ∷ []
cr1Pre (_ , tick1) tt = ((_ , tick1) , tt , refl) ∷ []
cr1Pre (_ , tick2) tt = ((_ , tick2) , tt , refl) ∷ []
cr1Pre (_ , tauCh) tt = ((_ , ev) , (σa , ln1 , H) , refl)
                      ∷ ((_ , ev) , (σa , ln2 , H) , refl)
                      ∷ ((_ , ev) , (σb , ln1 , H) , refl)
                      ∷ ((_ , ev) , (σb , ln2 , H) , refl)
                      ∷ ((_ , ev) , (σc , ln1 , H) , refl)
                      ∷ ((_ , ev) , (σc , ln2 , H) , refl)
                      ∷ ((_ , tauCh) , tt , refl)
                      ∷ []

-- CR's second renaming, forwards: [[tick1 <- tau, tick2 <- tau, tick <- tau]].
-- Again functional forwards, fan-in backwards.
cr2F : ConcEvent₁ → ConcEvent₁
cr2F ((_ , tick)  , _) = tauC
cr2F ((_ , tick1) , _) = tauC
cr2F ((_ , tick2) , _) = tauC
cr2F ((_ , sig)   , x) = sigC x
cr2F ((_ , ev)    , w) = (((Sig × Lane × Status) , ev) , w)
cr2F ((_ , tauCh) , _) = tauC

-- …as a renaming relation
cr2R : ConcEvent₁ → ConcEvent₂ → Set₁
cr2R e f = cr2F e ≡ f

-- …and its per-target preimage enumerator: the three tick events (and `tau` itself)
-- fan in onto `tau`; nothing else moves.
cr2Pre : (bt : AnyTypes AEv) (b : proj₁ bt)
       → List (Σ[ at ∈ AnyTypes AEv ] Σ[ a ∈ proj₁ at ] cr2R (at , a) (bt , b))
cr2Pre (_ , sig) x  = ((_ , sig) , x , refl) ∷ []
cr2Pre (_ , ev)  w  = ((_ , ev) , w , refl) ∷ []
cr2Pre (_ , tick)  tt = []
cr2Pre (_ , tick1) tt = []
cr2Pre (_ , tick2) tt = []
cr2Pre (_ , tauCh) tt = ((_ , tick)  , tt , refl)
                      ∷ ((_ , tick1) , tt , refl)
                      ∷ ((_ , tick2) , tt , refl)
                      ∷ ((_ , tauCh) , tt , refl)
                      ∷ []

-- ER(i,P): every basic event of P acquires a visible and a hidden lane-i copy
ER : Lane → AProc → AProc
ER i P = renameInv P (erInv i)

-- CR(P): the two renamings of the script's `CR`, applied in the same order
CR : AProc → AProc
CR P = (P ⟦ cr1R ¿ cr1Pre ⟧) ⟦ cr2R ¿ cr2Pre ⟧

------------------------------------------------------------------------------------
-- §A.2  The event sets used by the parallel, the throw and the hiding.
------------------------------------------------------------------------------------

-- a channel-level event set from a Boolean channel test
chanES : (AnyTypes AEv → Bool) → EventSet
chanES f = chanSet (λ at → T (f at)) (λ at → T? (f at))

-- {| ev, tick1, tick2 |} — what the lanes and the regulator synchronise on
evTick12B : AnyTypes AEv → Bool
evTick12B (_ , ev)    = true
evTick12B (_ , tick1) = true
evTick12B (_ , tick2) = true
evTick12B _           = false

evTick12 : EventSet
evTick12 = chanES evTick12B

-- {tick} — the throw's trigger set
tickB : AnyTypes AEv → Bool
tickB (_ , tick) = true
tickB _          = false

tickES : EventSet
tickES = chanES tickB

-- {tau} — the hidden channel (the script's visible `tau`, NOT the LTS's τ)
tauB : AnyTypes AEv → Bool
tauB (_ , tauCh) = true
tauB _           = false

tauES : EventSet
tauES = chanES tauB

------------------------------------------------------------------------------------
-- §A.3  The regulator.  BOUNDED version (`Bd = 5`) — the one the three asserts use.
--
-- The regulator keeps the two lanes on the SAME visible trace: whichever lane runs an
-- event visibly (ev.x.i.V), the other must catch up on it hidden (ev.x.(3-i).H), in
-- order.  `BReg1 y s` is the book's `BReg1(<y>^s)`: lane 1 is ahead by the non-empty
-- queue <y>^s.  `#s < Bd-1` bounds that queue, which is what makes the state space
-- finite.  Each node is written as an inlined `react` copattern (the offer maps are
-- forward-declared helpers in the same recursive clique) because a corecursive call
-- underneath `□`/`⟶` is not syntactically guarded.
------------------------------------------------------------------------------------

-- Bd = 5
Bd : ℕ
Bd = 5

-- `tick -> STOP`, the regulator's terminal handshake with the throw
tickStop : AProc
tickStop = tick ⟶₀ Stop

BReg    : AProc
BReg1   : Sig → List Sig → AProc
BReg1'  : AProc
BReg2   : Sig → List Sig → AProc
BReg2'  : AProc

bRegV   : (at : AnyTypes AEv) → ContinueType at (Maybe AProc)
bReg1V  : Sig → List Sig → (at : AnyTypes AEv) → ContinueType at (Maybe AProc)
bReg1'V : (at : AnyTypes AEv) → ContinueType at (Maybe AProc)
bReg2V  : Sig → List Sig → (at : AnyTypes AEv) → ContinueType at (Maybe AProc)
bReg2'V : (at : AnyTypes AEv) → ContinueType at (Maybe AProc)

-- BReg: neither lane is ahead; either may take the lead, or either may finish
force BReg = react bRegV ∅t
bRegV (_ , ev) (x , ln1 , V) = just (BReg1 x [])
bRegV (_ , ev) (x , ln2 , V) = just (BReg2 x [])
bRegV (_ , ev) (_ , _   , H) = nothing
bRegV (_ , tick1) _ = just tickStop
bRegV (_ , tick2) _ = just tickStop
bRegV (_ , sig)   _ = nothing
bRegV (_ , tick)  _ = nothing
bRegV (_ , tauCh) _ = nothing

-- BReg1(<y>^s): lane 1 is ahead by <y>^s
force (BReg1 y s) = react (bReg1V y s) ∅t
bReg1V y s (_ , ev) (x , ln1 , V) with length s <ᵇ Bd ∸ 1   -- #s < Bd-1 & …
... | true  = just (BReg1 y (s ∷ʳ x))
... | false = nothing
bReg1V y s (_ , ev) (x , ln2 , H) with x Sig≟ y | s          -- ev!y!2!H -> …
... | yes _ | []     = just BReg
... | yes _ | z ∷ s' = just (BReg1 z s')
... | no  _ | _      = nothing
bReg1V y s (_ , ev) (_ , ln1 , H) = nothing
bReg1V y s (_ , ev) (_ , ln2 , V) = nothing
bReg1V y s (_ , tick1) _ = just tickStop
bReg1V y s (_ , tick2) _ = just BReg1'
bReg1V y s (_ , sig)   _ = nothing
bReg1V y s (_ , tick)  _ = nothing
bReg1V y s (_ , tauCh) _ = nothing

-- BReg1': lane 2 has bowed out; lane 1 runs free until it finishes
force BReg1' = react bReg1'V ∅t
bReg1'V (_ , ev) (_ , ln1 , V) = just BReg1'
bReg1'V (_ , ev) (_ , ln1 , H) = nothing
bReg1'V (_ , ev) (_ , ln2 , _) = nothing
bReg1'V (_ , tick1) _ = just tickStop
bReg1'V (_ , sig)   _ = nothing
bReg1'V (_ , tick)  _ = nothing
bReg1'V (_ , tick2) _ = nothing
bReg1'V (_ , tauCh) _ = nothing

-- BReg2(<y>^s): lane 2 is ahead by <y>^s (the mirror image of BReg1)
force (BReg2 y s) = react (bReg2V y s) ∅t
bReg2V y s (_ , ev) (x , ln2 , V) with length s <ᵇ Bd ∸ 1
... | true  = just (BReg2 y (s ∷ʳ x))
... | false = nothing
bReg2V y s (_ , ev) (x , ln1 , H) with x Sig≟ y | s
... | yes _ | []     = just BReg
... | yes _ | z ∷ s' = just (BReg2 z s')
... | no  _ | _      = nothing
bReg2V y s (_ , ev) (_ , ln2 , H) = nothing
bReg2V y s (_ , ev) (_ , ln1 , V) = nothing
bReg2V y s (_ , tick2) _ = just tickStop
bReg2V y s (_ , tick1) _ = just BReg2'
bReg2V y s (_ , sig)   _ = nothing
bReg2V y s (_ , tick)  _ = nothing
bReg2V y s (_ , tauCh) _ = nothing

-- BReg2': lane 1 has bowed out; lane 2 runs free.  NOTE — the script (line 85) writes
-- `BReg2' = ev?x!2!V -> BReg2' [] tick1 -> tick -> STOP`, i.e. it waits for `tick1`,
-- not `tick2`; the same asymmetry is in the unbounded `Reg2'` (line 46).  That looks
-- like a slip (lane 1 has ALREADY performed tick1 to get here, and is at STOP), but it
-- is what the file says and it is what is ported: the port is of angel.csp, not of a
-- repaired angel.csp.  It costs nothing either way — on the three subjects of the
-- asserts NEITHER `BReg1'` NOR `BReg2'` is reachable at all (no run has one lane
-- finishing while the other is strictly ahead), so reading `tick2` here instead
-- changes none of the state counts or verdicts in §B.0.
force BReg2' = react bReg2'V ∅t
bReg2'V (_ , ev) (_ , ln2 , V) = just BReg2'
bReg2'V (_ , ev) (_ , ln2 , H) = nothing
bReg2'V (_ , ev) (_ , ln1 , _) = nothing
bReg2'V (_ , tick1) _ = just tickStop
bReg2'V (_ , sig)   _ = nothing
bReg2'V (_ , tick)  _ = nothing
bReg2'V (_ , tick2) _ = nothing
bReg2'V (_ , tauCh) _ = nothing

------------------------------------------------------------------------------------
-- §A.4  The UNBOUNDED regulator (script lines 26-46).  MODEL-ONLY: the script
-- presents `Reg` first and then abandons it ("the problem with this is that Reg is
-- infinite state because of the unbounded sequences it has"), so no assert is attached
-- to it and none is attempted here — the same MODEL-ONLY posture as
-- CSP.Examples.UCS.Ch7.Counter.  It is `BReg` with the `#s < Bd-1` guard removed.
------------------------------------------------------------------------------------

Reg    : AProc
Reg1   : Sig → List Sig → AProc
Reg1'  : AProc
Reg2   : Sig → List Sig → AProc
Reg2'  : AProc

regV   : (at : AnyTypes AEv) → ContinueType at (Maybe AProc)
reg1V  : Sig → List Sig → (at : AnyTypes AEv) → ContinueType at (Maybe AProc)
reg1'V : (at : AnyTypes AEv) → ContinueType at (Maybe AProc)
reg2V  : Sig → List Sig → (at : AnyTypes AEv) → ContinueType at (Maybe AProc)
reg2'V : (at : AnyTypes AEv) → ContinueType at (Maybe AProc)

-- Reg: the unbounded regulator's idle state
force Reg = react regV ∅t
regV (_ , ev) (x , ln1 , V) = just (Reg1 x [])
regV (_ , ev) (x , ln2 , V) = just (Reg2 x [])
regV (_ , ev) (_ , _   , H) = nothing
regV (_ , tick1) _ = just tickStop
regV (_ , tick2) _ = just tickStop
regV (_ , sig)   _ = nothing
regV (_ , tick)  _ = nothing
regV (_ , tauCh) _ = nothing

-- Reg1(<y>^s): lane 1 ahead, queue UNBOUNDED
force (Reg1 y s) = react (reg1V y s) ∅t
reg1V y s (_ , ev) (x , ln1 , V) = just (Reg1 y (s ∷ʳ x))
reg1V y s (_ , ev) (x , ln2 , H) with x Sig≟ y | s
... | yes _ | []     = just Reg
... | yes _ | z ∷ s' = just (Reg1 z s')
... | no  _ | _      = nothing
reg1V y s (_ , ev) (_ , ln1 , H) = nothing
reg1V y s (_ , ev) (_ , ln2 , V) = nothing
reg1V y s (_ , tick1) _ = just tickStop
reg1V y s (_ , tick2) _ = just Reg1'
reg1V y s (_ , sig)   _ = nothing
reg1V y s (_ , tick)  _ = nothing
reg1V y s (_ , tauCh) _ = nothing

-- Reg1': lane 2 out, lane 1 free
force Reg1' = react reg1'V ∅t
reg1'V (_ , ev) (_ , ln1 , V) = just Reg1'
reg1'V (_ , ev) (_ , ln1 , H) = nothing
reg1'V (_ , ev) (_ , ln2 , _) = nothing
reg1'V (_ , tick1) _ = just tickStop
reg1'V (_ , sig)   _ = nothing
reg1'V (_ , tick)  _ = nothing
reg1'V (_ , tick2) _ = nothing
reg1'V (_ , tauCh) _ = nothing

-- Reg2(<y>^s): lane 2 ahead, queue unbounded
force (Reg2 y s) = react (reg2V y s) ∅t
reg2V y s (_ , ev) (x , ln2 , V) = just (Reg2 y (s ∷ʳ x))
reg2V y s (_ , ev) (x , ln1 , H) with x Sig≟ y | s
... | yes _ | []     = just Reg
... | yes _ | z ∷ s' = just (Reg2 z s')
... | no  _ | _      = nothing
reg2V y s (_ , ev) (_ , ln2 , H) = nothing
reg2V y s (_ , ev) (_ , ln1 , V) = nothing
reg2V y s (_ , tick2) _ = just tickStop
reg2V y s (_ , tick1) _ = just Reg2'
reg2V y s (_ , sig)   _ = nothing
reg2V y s (_ , tick)  _ = nothing
reg2V y s (_ , tauCh) _ = nothing

-- Reg2': lane 1 out, lane 2 free (with the script's `tick1`, as in BReg2')
force Reg2' = react reg2'V ∅t
reg2'V (_ , ev) (_ , ln2 , V) = just Reg2'
reg2'V (_ , ev) (_ , ln2 , H) = nothing
reg2'V (_ , ev) (_ , ln1 , _) = nothing
reg2'V (_ , tick1) _ = just tickStop
reg2'V (_ , sig)   _ = nothing
reg2'V (_ , tick)  _ = nothing
reg2'V (_ , tick2) _ = nothing
reg2'V (_ , tauCh) _ = nothing

------------------------------------------------------------------------------------
-- §A.5  Angelic choice itself — a CONSTRUCTION out of the operators this development
-- already has: two renamings, interleaving, interface parallel, throw, hiding and
-- sequential composition.  Nothing here is primitive.
------------------------------------------------------------------------------------

-- the two lanes, each running its operand and then announcing termination
lane : Lane → AProc → AProc
lane ln1 P = ER ln1 (P >> (tick1 ⟶₀ Stop))
lane ln2 Q = ER ln2 (Q >> (tick2 ⟶₀ Stop))

-- bangelic(P,Q) — the bounded, throw-terminated angelic choice (script lines 88-91)
bangelic : AProc → AProc → AProc
bangelic P Q =
  CR ((((lane ln1 P) ⦀ (lane ln2 Q)) ∥⇘ evTick12 ⇙ BReg) ⟦ tickES ▷ Skip) ∖ tauES

-- angelic(P,Q) — the unbounded version of script lines 53-55.  MODEL-ONLY (see §A.4);
-- note it carries NO throw: the script only added `[|{tick}|> SKIP` in `bangelic`.
angelic : AProc → AProc → AProc
angelic P Q =
  CR (((lane ln1 P) ⦀ (lane ln2 Q)) ∥⇘ evTick12 ⇙ Reg) ∖ tauES

------------------------------------------------------------------------------------
-- §A.6  The subject processes and the specification (script lines 95-104).
------------------------------------------------------------------------------------

-- A = a -> a -> b -> SKIP   (the only operand that TERMINATES)
A : AProc
A = sig ! σa ⟶ (sig ! σa ⟶ (sig ! σb ⟶ Skip))

-- B = a -> a -> a -> STOP
B : AProc
B = sig ! σa ⟶ (sig ! σa ⟶ (sig ! σa ⟶ Stop))

-- C = a -> a -> a -> c -> STOP
C : AProc
C = sig ! σa ⟶ (sig ! σa ⟶ (sig ! σa ⟶ (sig ! σc ⟶ Stop)))

-- ABC = a -> a -> (a -> c -> STOP [] b -> SKIP)  — how angelic choice SHOULD behave
ABC : AProc
ABC = sig ! σa ⟶ (sig ! σa ⟶ ((sig ! σa ⟶ (sig ! σc ⟶ Stop)) □ (sig ! σb ⟶ Skip)))

------------------------------------------------------------------------------------
-- §B.0  THE THREE ASSERTS: expected truth values, and why none is discharged here.
--
-- Hand-evaluating the construction on the three subjects:
--   bangelic(A,B)             ≈  a -> a -> (b -> SKIP [] a -> STOP)
--   bangelic(bangelic(A,B),C) ≈  a -> a -> (b -> SKIP [] a -> c -> STOP)  =  ABC
--   bangelic(C,B)             ≈  a -> a -> a -> c -> STOP  (B adds nothing C lacks)
--   bangelic(bangelic(C,B),A) ≈  ABC  as well
-- ABC is deterministic and divergence-free, so all three asserts are expected TRUE,
-- agreeing with the book (Roscoe presents all three as demonstrations).  That
-- expectation is NOT a proof and is not used as one anywhere below.
--
-- The expectation was additionally cross-checked by enumerating the SAME operational
-- semantics outside Agda (scratch code, not part of this repository, therefore NOT
-- evidence in the sense this development uses the word — only a guard against stating
-- a wrong verdict here).  That enumeration reports: both doubly-nested terms have
-- exactly ABC's seven trace-nodes with exactly ABC's offer sets at each, are
-- divergence-free, and are deterministic; so (1), (2) and (3) all hold, and in fact
-- both nested terms are FD-EQUIVALENT to ABC, not merely refined by it.  It also
-- reports the reachable-state counts quoted below.
--
-- WHY THEY ARE NOT PROVED.  Each assert is about a DOUBLY-NESTED bangelic, i.e. two
-- full copies of the rename/interleave/parallel/throw/hide stack, the inner one
-- sitting in the outer's lane 1.  Both a `⊑FD` proof and a determinism proof need the
-- reachable-state family of the whole term, closed under both visible and τ steps,
-- with a refusal argument at every stable member (the `SimR` shape of
-- CSP.Examples.UCS.Ch8.Lazic, or the `split-det`/`L1-det` shape of Ch5/Renaming and
-- Ch7/Resettable).  Measured, not guessed: bangelic(A,B) alone has 20 reachable
-- states; bangelic(bangelic(A,B),C) has 86 and bangelic(bangelic(C,B),A) has 80 —
-- Lazić's harness, at 1478 lines, needed 26.  The state COUNT is only half the cost;
-- the other half is TERM DEPTH.  Lazić's composite is three operator layers deep
-- (Par/Par/Hide); here every step inversion must be pushed through fourteen —
-- hide, rename, rename, throw, par, par, rename for the outer stack, and the same
-- seven again inside lane 1, because the inner stack's τ-structure (hidden catch-up
-- events and renaming fan-ins) is RE-EXPOSED to the outer stack rather than absorbed
-- by it.  The §B.1 error terms are the size that produces.  That is a scale problem,
-- not a missing lemma: no new operator law, postulate or classical seam is needed,
-- only the enumeration and its inversions.  Discharging (3) would come first — it is
-- the one where a one-way weak simulation with refusal transfer suffices; (1) and (2)
-- then need the two-sided argument on top.  A single-nesting warm-up
-- (`a -> a -> (b -> SKIP [] a -> STOP) ⊑FD bangelic(A,B)`, 20 states, seven layers) is
-- the natural first target, but it is NOT one of the script's asserts and is not
-- attempted here either.
--
-- What IS below is transition sanity: the construction is shown to RUN, in both of its
-- angelic branches, and to carry a √ all the way out.  A model that typechecks but
-- cannot step is no evidence of anything; this much is evidence that the composition
-- is the right one, and no more than that.
------------------------------------------------------------------------------------

------------------------------------------------------------------------------------
-- §B.1  Transition sanity.
------------------------------------------------------------------------------------

open import Semantics.Failures {E = AEv} {I = ExtI AEv}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; traces)

-- the visible label `a` (= sig.σa)
evA : Event√ (⊤poly {lzero})
evA = evl (evLabel Sig sig σa)

-- bangelic(A,B) offers `a`
bangAB-a : Σ[ P ∈ AProc ] (bangelic A B ─[ ev evA ]─► P)
bangAB-a = _ , sVis refl refl

-- the τ that resolves the renaming's fan-in (pick lane 1)
bangAB-aa : traces (bangelic A B) (evA ∷ evA ∷ [])
bangAB-aa = _ , ⟹-ev (sVis refl refl)
                (⟹-τ (sTau {i = (_ , pair (fin {n = 2}) (fin {n = 2}))}
                           {a = (lift fzero , lift fzero)} refl refl)
                (⟹-ev (sVis refl refl) ⟹-refl))

-- the visible labels `b` and `c`, and the termination label √
evB : Event√ (⊤poly {lzero})
evB = evl (evLabel Sig sig σb)

evC : Event√ (⊤poly {lzero})
evC = evl (evLabel Sig sig σc)

√A : Event√ (⊤poly {lzero})
√A = √ (lift tt)

-- the full A-side run: bangelic(A,B) can perform <a,a,b,√>.  Lane 1 (running A) leads
-- throughout; lane 2 (running B) is left behind, and A's √ travels through the `;`,
-- the regulator's tick1/tick handshake, the throw and the hiding to become the
-- composite's own √.  The τ shapes are the two the construction generates: a hide of a
-- newly-`tau`-renamed event (`pair fin (base tauCh)`, tag 1) and a resolution of a
-- renaming fan-in (`pair fin fin`, tag 0).
bangAB-aab√ : traces (bangelic A B) (evA ∷ evA ∷ evB ∷ √A ∷ [])
bangAB-aab√ =
  _ , ⟹-ev (sVis refl refl)                                     -- a  (either lane may lead)
      (⟹-τ (sTau {i = (_ , pair (fin {n = 2}) (fin {n = 2}))}
                 {a = (lift fzero , lift fzero)} refl refl)      -- …resolved to lane 1
      (⟹-ev (sVis refl refl)                                     -- a
      (⟹-ev (sVis refl refl)                                     -- b
      (⟹-τ (sTau {i = (_ , pair (fin {n = 2}) (base tauCh))}
                 {a = (lift (fsuc fzero) , tt)} refl refl)        -- a hidden event…
      (⟹-τ (sTau {i = (_ , pair (fin {n = 2}) (fin {n = 2}))}
                 {a = (lift fzero , lift fzero)} refl refl)       -- …namely tick1
      (⟹-τ (sTau {i = (_ , pair (fin {n = 2}) (base tauCh))}
                 {a = (lift (fsuc fzero) , tt)} refl refl)        -- tick: the throw fires
      (⟹-ev (sRet refl) ⟹-refl)))))))

-- the B-side run: the SAME bangelic(A,B) can instead perform <a,a,a>, by resolving
-- the very first fan-in the other way (lane 2, running B, leads).  Together with
-- `bangAB-aab√` this is the angelic content of the construction: both operands'
-- behaviours survive, and the choice between them is not committed by the first event.
bangAB-aaa : traces (bangelic A B) (evA ∷ evA ∷ evA ∷ [])
bangAB-aaa =
  _ , ⟹-ev (sVis refl refl)                                     -- a
      (⟹-τ (sTau {i = (_ , pair (fin {n = 2}) (fin {n = 2}))}
                 {a = (lift fzero , lift (fsuc fzero))} refl refl)  -- …resolved to lane 2
      (⟹-ev (sVis refl refl)                                     -- a
      (⟹-ev (sVis refl refl) ⟹-refl)))                           -- a

-- the doubly-nested term of the three asserts steps too
bang2-a : Σ[ P ∈ AProc ] (bangelic (bangelic A B) C ─[ ev evA ]─► P)
bang2-a = _ , sVis refl refl

-- …and it reaches C's `c`, two levels of nesting deep: lane 2 of the OUTER stack (the
-- one running C) leads the whole way, so C's fourth event survives being wrapped in a
-- second rename/parallel/throw/hide layer.  This is the check that the NESTING works,
-- not just one bangelic.
bang2-aaac : traces (bangelic (bangelic A B) C) (evA ∷ evA ∷ evA ∷ evC ∷ [])
bang2-aaac =
  _ , ⟹-ev (sVis refl refl)                                     -- a
      (⟹-τ (sTau {i = (_ , pair (fin {n = 2}) (fin {n = 2}))}
                 {a = (lift fzero , lift (fsuc fzero))} refl refl)  -- …resolved to lane 2 (C)
      (⟹-ev (sVis refl refl)                                     -- a
      (⟹-ev (sVis refl refl)                                     -- a
      (⟹-ev (sVis refl refl) ⟹-refl))))                          -- c
