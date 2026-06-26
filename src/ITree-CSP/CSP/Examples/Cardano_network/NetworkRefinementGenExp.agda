{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Task 5, Steps 2–3 of the Cardano single-channel refinement, GENERALISED
-- in the forwarded payload `Data`.
--
-- This module HOSTS the heavier Step-2/3 content (VisWit + theVisWit and the
-- expA/expB/expG expansion builders) that could not be appended to
-- `NetworkRefinementGen` because that monolith already sits at the memory
-- ceiling.  It imports the Gen module to re-use every Step-0/1 definition and
-- only adds the new theory on top.
------------------------------------------------------------------------

open import Level using (0ℓ; lift)
open import Data.Unit using (⊤; tt)
import Data.Unit.Polymorphic as Poly
open import Data.Nat using (ℕ)
open import Data.Fin using (zero) renaming (suc to fs)
open import Data.Fin using () renaming (zero to fz)
open import Data.Maybe using (Maybe; just; nothing; is-just)
open import Data.Bool using (true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_,_; proj₁; proj₂; Σ; Σ-syntax; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; ≡-≟-identity; sym; trans; cong; cong₂; subst; _≢_)
open import Data.Maybe.Properties using (just-injective)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees
open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Base using
  ( IDs; N2N_KeepAlive
  ; N2N_ChainSync; N2N_BlockFetch; N2N_TxSubmission
  ; N2N_LeiosNotify; N2N_LeiosFetch )
open import CSP.Examples.Cardano_network.NetModel
  using ( CS; mkCS; cs0
        ; inp; tr; ra; out; rc; sa
        ; IP; I0; I1; I2; Ig
        ; TP; T0; T1; Tg
        ; RP; R0; R1; Rg
        ; OP; O0; O1; O2; Og
        ; CP; Rc0; Rc1; Rcg
        ; SP; Sa0; Sa1; Sag
        ; _⇒ᵢ_; _⇒ᵥ_
        ; gI; gT; gR; gO; gRc; gSa )
import CSP.Examples.Cardano_network.NetModel as NM

module CSP.Examples.Cardano_network.NetworkRefinementGenExp
  (Data : Set) ⦃ _ : DecEq Data ⦄ where

open PTree
open ExtI

------------------------------------------------------------------------
-- Bring in EVERY Step-0/1 definition of the Gen module FIRST, so that the
-- SAME `p1` instance (re-exported by Gen) is used to instantiate every
-- downstream module open below.  (Defining a fresh local `p1` would make a
-- distinct extended lambda for `numConns` and so a type-incompatible `Net p1`.)
------------------------------------------------------------------------
open import CSP.Examples.Cardano_network.NetworkRefinementGen Data

open import CSP.Examples.Cardano_network.Net p1
  using (Net; Conn; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack)
open import CSP.Examples.Cardano_network.Network p1 Data

open import Semantics.LTS {E = Net Data} {I = ExtI (Net Data)}
open import Semantics.WeakBisim {E = Net Data} {I = ExtI (Net Data)}
  using (_─[τ*]─►_; τ*-refl; τ*-step; _═[_]═►_; wτ; wev; WSimF; Wbisim)
open import Semantics.DRBisim {E = Net Data} {I = ExtI (Net Data)}
  using (Diverges; _≈DR_; deadlock-converges; drbisim→wbisim; drbisim-sym)
open import Semantics.Expansion {E = Net Data} {I = ExtI (Net Data)}
  using (Expand; ExpBwdF; _⪰_; ⪯→≈DR)
open import Semantics.Failures {E = Net Data} {I = ExtI (Net Data)}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; _⊑T_; traces; traces-respects-≈)
open import Semantics.FailuresDivergences {E = Net Data} {I = ExtI (Net Data)}
  using (_⊑D_; divergences; IsDivergence; _⊑F⊥_; _⊑FD_; _≈FD_)
open import Semantics.DRImpliesFD {E = Net Data} {I = ExtI (Net Data)}
  using (drbisim→≈FD)

open import CSP.Examples.Cardano_network.Net p1 using (Net-≟)

open import CSP.Operators {E = Net Data} (Net-≟ {Data})
  using (Par⊤; _∥⇘_⇙_; _⦀_; _∖_; chanSet; EventSet; Skip; Par; ∅ES; viewV)
open EventSet

open import Data.List using (List; map; _∷_; [])
import CSP.Operators {E = Net Data} (Net-≟ {Data}) as Op

open import CSP.Laws.FD.HideDivergence (Net-≟ {Data})
  using (MAcc; macc; Hide-noDiv-from-MAcc)
open import CSP.Laws.Bisim.DRCongruence (Net-≟ {Data})
  using (ModAStep; maτ; maE)
open import CSP.Laws.Traces.TraceLawsParallelElim (Net-≟ {Data})
  using (Par-τ-elim; ParτR; τL; τR
        ; Par-ev-elim; ParevR; evSync; evL; evR; evBoth; ev√
        ; Par-force-ret-inv)
open import CSP.Laws.Traces.TraceLawsParallel (Net-≟ {Data})
  using (Par-soloL; Par-soloR; Par-sync; Par-τ-L; Par-τ-R)
open import CSP.Laws.Traces.TraceLawsHide (Net-≟ {Data})
  using (Hide-τ-elim; HideτR; hτP; hτH
        ; Hide-ev-elim; HideevR; heV; he√
        ; Hide-τ; Hide-keep; Hide-hidden
        ; fHide-ret-inv)
open import CSP.Laws.Traces.TraceLawsParallelTrace (Net-≟ {Data})
  using (deadlock-no-τ; deadlock-no-ev)

------------------------------------------------------------------------
-- STEP 2.  Fresh-input leaf characterisations, decode non-termination,
-- visible reflections, and the VisWit witness record.
------------------------------------------------------------------------

nTR-input-q : ∀ t r dR a
            → viewV (PTree.force (decT t dR ⦀ decR r dR))
                    (Data , input N2N_KeepAlive c0) a ≡ nothing
nTR-input-q T0 R0 dR a = refl
nTR-input-q T0 R1 dR a = refl
nTR-input-q T0 Rg dR a rewrite ≟-diag dR = refl
nTR-input-q T1 R0 dR a rewrite ≟-diag dR = refl
nTR-input-q T1 R1 dR a rewrite ≟-diag dR = refl
nTR-input-q T1 Rg dR a rewrite ≟-diag dR = refl
nTR-input-q Tg R0 dR a rewrite ≟-diag dR = refl
nTR-input-q Tg R1 dR a rewrite ≟-diag dR = refl
nTR-input-q Tg Rg dR a rewrite ≟-diag dR = refl

nRx-input-q : ∀ o c s dR a
            → viewV (PTree.force (decRx o c s dR))
                    (Data , input N2N_KeepAlive c0) a ≡ nothing
nRx-input-q O0 Rc0 Sa0 dR a = refl
nRx-input-q O0 Rc0 Sa1 dR a = refl
nRx-input-q O0 Rc0 Sag dR a = refl
nRx-input-q O0 Rc1 Sa0 dR a rewrite ≟-diag dR = refl
nRx-input-q O0 Rc1 Sa1 dR a rewrite ≟-diag dR = refl
nRx-input-q O0 Rc1 Sag dR a rewrite ≟-diag dR = refl
nRx-input-q O0 Rcg Sa0 dR a rewrite ≟-diag dR = refl
nRx-input-q O0 Rcg Sa1 dR a rewrite ≟-diag dR = refl
nRx-input-q O0 Rcg Sag dR a rewrite ≟-diag dR = refl
nRx-input-q O1 Rc0 Sa0 dR a rewrite ≟-diag dR = refl
nRx-input-q O1 Rc0 Sa1 dR a rewrite ≟-diag dR = refl
nRx-input-q O1 Rc0 Sag dR a rewrite ≟-diag dR = refl
nRx-input-q O1 Rc1 Sa0 dR a rewrite ≟-diag dR = refl
nRx-input-q O1 Rc1 Sa1 dR a rewrite ≟-diag dR = refl
nRx-input-q O1 Rc1 Sag dR a rewrite ≟-diag dR = refl
nRx-input-q O1 Rcg Sa0 dR a rewrite ≟-diag dR = refl
nRx-input-q O1 Rcg Sa1 dR a rewrite ≟-diag dR = refl
nRx-input-q O1 Rcg Sag dR a rewrite ≟-diag dR = refl
nRx-input-q O2 Rc0 Sa0 dR a rewrite ≟-diag dR = refl
nRx-input-q O2 Rc0 Sa1 dR a rewrite ≟-diag dR = refl
nRx-input-q O2 Rc0 Sag dR a rewrite ≟-diag dR = refl
nRx-input-q O2 Rc1 Sa0 dR a rewrite ≟-diag dR = refl
nRx-input-q O2 Rc1 Sa1 dR a rewrite ≟-diag dR = refl
nRx-input-q O2 Rc1 Sag dR a rewrite ≟-diag dR = refl
nRx-input-q O2 Rcg Sa0 dR a rewrite ≟-diag dR = refl
nRx-input-q O2 Rcg Sa1 dR a rewrite ≟-diag dR = refl
nRx-input-q O2 Rcg Sag dR a rewrite ≟-diag dR = refl
nRx-input-q Og Rc0 Sa0 dR a rewrite ≟-diag dR = refl
nRx-input-q Og Rc0 Sa1 dR a rewrite ≟-diag dR = refl
nRx-input-q Og Rc0 Sag dR a rewrite ≟-diag dR = refl
nRx-input-q Og Rc1 Sa0 dR a rewrite ≟-diag dR = refl
nRx-input-q Og Rc1 Sa1 dR a rewrite ≟-diag dR = refl
nRx-input-q Og Rc1 Sag dR a rewrite ≟-diag dR = refl
nRx-input-q Og Rcg Sa0 dR a rewrite ≟-diag dR = refl
nRx-input-q Og Rcg Sa1 dR a rewrite ≟-diag dR = refl
nRx-input-q Og Rcg Sag dR a rewrite ≟-diag dR = refl

-- A FRESH `input` firing a NEW payload `a` while partners keep the old `d`.
-- Lands on the MIXED post-state `⟦cs′⟧ᵢ a d ∖ csTA'`.
fresh-input : ∀ {t r o c s} a d
            → ⟦ mkCS I0 t r o c s ⟧N d
              ─[ ev (inputLbl a) ]─►
              (⟦ mkCS I1 t r o c s ⟧ᵢ a d ∖ csTA')
fresh-input {t} {r} {o} {c} {s} a d =
  Hide-keep csTA' _ (λ ())
   (Par-soloL csTA' ⊤merge (decTx I0 t r d) (decRx o c s d) (λ ())
     (Hide-keep csSR' _ (λ ())
       (Par-soloL csSR' ⊤merge (decI I0 d) (decT t d ⦀ decR r d) (λ ())
         (sVis refl refl)
         (nTR-input-q t r d a)))
     (nRx-input-q o c s d a))

-- The decoded leaves never terminate (decI is always a `react` menu).
decI-noret : ∀ i d {x} → PTree.force (decI i d) ≡ ret x → ⊥
decI-noret I0 d ()
decI-noret I1 d ()
decI-noret I2 d eqf with ev-inv (emit-I2-rcvack {d})
... | _ , _ , freq , _ with trans (sym freq) eqf
... | ()
decI-noret Ig d eqf with τ-inv (guard-Ig-τ {d})
... | inj₁ feq                          with trans (sym feq) eqf
...   | ()
decI-noret Ig d eqf | inj₂ (_ , _ , _ , _ , freq , _) with trans (sym freq) eqf
... | ()

decTx-noret : ∀ i t r d {x} → PTree.force (decTx i t r d) ≡ ret x → ⊥
decTx-noret i t r d eqf
  with Par-force-ret-inv csSR' ⊤merge {P = decI i d} {Q = decT t d ⦀ decR r d}
         (fHide-ret-inv csSR' ((decI i d) ∥⇘ csSR' ⇙ (decT t d ⦀ decR r d)) eqf)
... | r₁ , _ , decIret , _ , _ = decI-noret i d decIret

⟦⟧-noret : ∀ cs d {x} → PTree.force (⟦ cs ⟧ d) ≡ ret x → ⊥
⟦⟧-noret (mkCS i t r o c s) d eqf
  with Par-force-ret-inv csTA' ⊤merge {P = decTx i t r d} {Q = decRx o c s d} eqf
... | r₁ , _ , decTxret , _ , _ = decTx-noret i t r d decTxret

-- Label-resolved, state-resolved visible inversion of the un-hidden ⟦cs⟧ d.
data uVisRG (cs : CS) (l : Event√ NetR) (d : Data) (W′ : NetProc) : Set₁ where
  uInG  : ∀ {t r o c s} a → cs ≡ mkCS I0 t r o c s
        → l ≡ inputLbl a → W′ ≡ ⟦ mkCS I1 t r o c s ⟧ᵢ a d
        → uVisRG cs l d W′
  uOutG : ∀ {i t r c s} → cs ≡ mkCS i t r O1 c s
        → l ≡ outputLbl d → W′ ≡ ⟦ mkCS i t r O2 c s ⟧ d
        → uVisRG cs l d W′

sim-uVis-lbl : ∀ cs {d B} {e : Net Data B} {a} {W′}
             → ¬ csTA' .mem (B , e) a
             → ⟦ cs ⟧ d ─[ ev (evl (evLabel B e a)) ]─► W′
             → uVisRG cs (evl (evLabel B e a)) d W′
sim-uVis-lbl (mkCS i t r o c s) {d} ¬cs st
  with Par-ev-elim csTA' ⊤merge (decTx i t r d) (decRx o c s d) st
... | evL _ Txev with sim-Tx-ev {i} {t} {r} {d} Txev
...   | inj₁ (a′ , refl , Lin , Weq) =
        uInG a′ refl Lin (cong (λ z → (z ∥⇘ csTA' ⇙ (decRx o c s d))) Weq)
...   | inj₂ (inj₁ (_ , Ltx  , _)) = ⊥-elim (¬cs (txLbl→mem Ltx))
...   | inj₂ (inj₂ (_ , Lack , _)) = ⊥-elim (¬cs (ackLbl→mem Lack))
sim-uVis-lbl (mkCS i t r o c s) {d} ¬cs st
  | evR _ Rxev with sim-Rx-ev {o} {c} {s} {d} Rxev
...   | inj₁ (refl , Lout , Weq) =
        uOutG refl Lout (cong (λ z → ((decTx i t r d) ∥⇘ csTA' ⇙ z)) Weq)
...   | inj₂ (inj₁ (_ , _ , Ltx  , _)) = ⊥-elim (¬cs (txLbl→mem Ltx))
...   | inj₂ (inj₂ (_ , Lack , _)) = ⊥-elim (¬cs (ackLbl→mem Lack))
sim-uVis-lbl (mkCS i t r o c s) ¬cs st | evSync mem _ _ = ⊥-elim (¬cs mem)
sim-uVis-lbl (mkCS i t r o c s) {d} ¬cs st
  | evBoth _ Txev Rxev with sim-Tx-ev {i} {t} {r} {d} Txev | sim-Rx-ev {o} {c} {s} {d} Rxev
...   | inj₁ (_ , _ , Lin , _)    | inj₁ (_ , Lout , _) =
          ⊥-elim (inputLbl≢outputLbl (trans (sym Lin) Lout))
...   | inj₁ (_ , _ , Lin , _)    | inj₂ (inj₁ (_ , _ , Ltx , _)) =
          ⊥-elim (inputLbl≢txLbl (trans (sym Lin) Ltx))
...   | inj₁ (_ , _ , Lin , _)    | inj₂ (inj₂ (_ , Lack , _)) =
          ⊥-elim (inputLbl≢ackLbl (trans (sym Lin) Lack))
...   | inj₂ (inj₁ (_ , Ltx , _)) | _ = ⊥-elim (¬cs (txLbl→mem Ltx))
...   | inj₂ (inj₂ (_ , Lack , _)) | _ = ⊥-elim (¬cs (ackLbl→mem Lack))

-- Reflect a NETWORK strong visible step into label/state resolved form.
data netVisRG (cs : CS) (l : Event√ NetR) (d : Data) (t₂′ : NetProc) : Set₁ where
  nInG  : ∀ {t r o c s} a → cs ≡ mkCS I0 t r o c s
        → l ≡ inputLbl a → t₂′ ≡ (⟦ mkCS I1 t r o c s ⟧ᵢ a d ∖ csTA')
        → netVisRG cs l d t₂′
  nOutG : ∀ {i t r c s} → cs ≡ mkCS i t r O1 c s
        → l ≡ outputLbl d → t₂′ ≡ ⟦ mkCS i t r O2 c s ⟧N d → netVisRG cs l d t₂′

reflectV : ∀ cs {d} {l : Event√ NetR} {t₂′}
         → ⟦ cs ⟧N d ─[ ev l ]─► t₂′
         → netVisRG cs l d t₂′
reflectV cs {d} step with Hide-ev-elim csTA' (⟦ cs ⟧ d) step
... | heV T′ ¬cs Tev with sim-uVis-lbl cs ¬cs Tev
...   | uInG a refl Lin Weq = nInG a refl Lin (cong (_∖ csTA') Weq)
...   | uOutG refl Lout Weq = nOutG refl Lout (cong (_∖ csTA') Weq)
reflectV cs {d} step | he√ eqf = ⊥-elim (⟦⟧-noret cs d eqf)

-- A phase-A network state offers no `output` (out=O1 ⇒ phaseN ≥ 1 ≠ 0).
phaseA-out≢O1 : ∀ {cs} → Reach cs pA → out cs ≢ O1
phaseA-out≢O1 {mkCS i t rr O1 c s} rA oeq = phaseN-O1 i t c (reach-phaseA rA)
phaseA-out≢O1 {mkCS i t rr O0 c s} rA ()
phaseA-out≢O1 {mkCS i t rr O2 c s} rA ()
phaseA-out≢O1 {mkCS i t rr Og c s} rA ()

-- The output-target (out=O2) satisfies inp≠I0 ∧ out≠O1 trivially on out.
out-step-tgt : ∀ {i t r c s} → out (mkCS i t r O2 c s) ≢ O1
out-step-tgt ()

-- `Cg d` is a `react` menu, never a `ret`.  `≟-diag d` unblocks the stuck
-- `d ≟ d` redex inside `force (Cg d)` at this single tiny leaf goal.
Cg-noret : ∀ {d x} → PTree.force (Cg d) ≡ ret x → ⊥
Cg-noret {d} eqf rewrite ≟-diag d with eqf
... | ()

-- A phase-B state never has inp ≡ I0.
pB-inp≢I0 : ∀ {cs} → Reach cs pB → inp cs ≢ I0
pB-inp≢I0 {cs} r i≡ =
  o≢0 (sym (trans (sym (Inv-I0-phase0 {cs} i≡ (reach-Inv r))) (reach-phaseB r)))

------------------------------------------------------------------------
-- The VisWit record (d-threaded).
------------------------------------------------------------------------

record VisWit : Set₁ where
  field
    fwd-in  : ∀ {cs d} (a : Data) → Reach cs pA
            → Σ[ cs′ ∈ CS ] ((⟦ cs ⟧N d ═[ ev (inputLbl a) ]═► ⟦ cs′ ⟧N a) × Reach cs′ pB)
    fwd-out : ∀ {cs d} → Reach cs pB
            → Σ[ cs′ ∈ CS ]
                ((⟦ cs ⟧N d ═[ ev (outputLbl d) ]═► ⟦ cs′ ⟧N d)
                 × Reach cs′ pA × (inp cs′ ≢ I0) × (out cs′ ≢ O1))
    bwd-in  : ∀ {cs d} {l : Event√ NetR} {t₂′} → Reach cs pA
            → ⟦ cs ⟧N d ─[ ev l ]─► t₂′
            → Σ[ a ∈ Data ] (Σ[ eq ∈ l ≡ inputLbl a ]
                (Σ[ cs′ ∈ CS ] ((t₂′ ≡ ⟦ cs′ ⟧N a) × Reach cs′ pB)))
    bwd-out : ∀ {cs d} {l : Event√ NetR} {t₂′} → Reach cs pB
            → ⟦ cs ⟧N d ─[ ev l ]─► t₂′
            → Σ[ eq ∈ l ≡ outputLbl d ]
                (Σ[ cs′ ∈ CS ]
                  ((t₂′ ≡ ⟦ cs′ ⟧N d) × Reach cs′ pA × (inp cs′ ≢ I0) × (out cs′ ≢ O1)))
    noev-AO : ∀ {cs d} {l : Event√ NetR} {t₂′}
            → inp cs ≢ I0 → out cs ≢ O1 → ⟦ cs ⟧N d ─[ ev l ]─► t₂′ → ⊥

theVisWit : VisWit
theVisWit = record
  { fwd-in  = λ {cs} {d} a r →
      let (cs-d , path , i≡) = drainA cs r
          rA               = reach-i* r path
      in fwd-in-build cs r a cs-d path i≡ rA
  ; fwd-out = λ {cs} {d} r →
      let (cs-d , path , o≡) = drainB cs r
          rB               = reach-i* r path
      in fwd-out-build cs r cs-d path o≡ rB
  ; bwd-in  = λ {cs} {d} {l} {t₂′} r step → bwd-in-build cs r step
  ; bwd-out = λ {cs} {d} {l} {t₂′} r step → bwd-out-build cs r step
  ; noev-AO = λ {cs} {d} {l} {t₂′} i≢ o≢ step → noev-build cs i≢ o≢ step
  }
  where
  -- fwd-in : drain to inp=I0, fire a FRESH input `a`, mix-convert to ⟦⟧N a.
  fwd-in-build :
    ∀ cs {d} (r : Reach cs pA) (a : Data) cs-d → cs ⇒ᵢ* cs-d → inp cs-d ≡ I0
    → Reach cs-d pA
    → Σ[ cs′ ∈ CS ] ((⟦ cs ⟧N d ═[ ev (inputLbl a) ]═► ⟦ cs′ ⟧N a) × Reach cs′ pB)
  fwd-in-build cs {d} r a (mkCS I0 t rr o c s) path refl rA =
    mkCS I1 t rr o c s ,
    wev (real-⇒ᵢ*-Net path)
        (subst (λ W → ⟦ mkCS I0 t rr o c s ⟧N d ─[ ev (inputLbl a) ]─► W)
               (cong (_∖ csTA') (mix≡uni {t} {rr} {o} {c} {s} hT hO hC))
               (fresh-input {t} {rr} {o} {c} {s} a d))
        τ*-refl ,
    reach-vA rA NM.input
    where
    pin = pinA {t} {rr} {o} {c} {s} (reach-Inv rA) (reach-phaseA rA)
    hT = proj₁ pin
    hO = proj₁ (proj₂ pin)
    hC = proj₂ (proj₂ pin)

  -- fwd-out : drain to out=O1, fire output at current d (no mix).
  fwd-out-build :
    ∀ cs {d} (r : Reach cs pB) cs-d → cs ⇒ᵢ* cs-d → out cs-d ≡ O1 → Reach cs-d pB
    → Σ[ cs′ ∈ CS ]
        ((⟦ cs ⟧N d ═[ ev (outputLbl d) ]═► ⟦ cs′ ⟧N d)
         × Reach cs′ pA × (inp cs′ ≢ I0) × (out cs′ ≢ O1))
  fwd-out-build cs {d} r (mkCS i t rr O1 c s) path refl rB =
    mkCS i t rr O2 c s ,
    wev (real-⇒ᵢ*-Net path)
        (out-step d) τ*-refl ,
    reach-vB rB NM.output ,
    (λ i≡ → pB-inp≢I0 rB i≡) ,
    out-step-tgt {i} {t} {rr} {c} {s}
    where
    out-step : ∀ d → ⟦ mkCS i t rr O1 c s ⟧N d ─[ ev (outputLbl d) ]─►
                     ⟦ mkCS i t rr O2 c s ⟧N d
    out-step d = proj₂ (proj₂ (real-⇒ᵥ-Net {d = d} (NM.output {i} {t} {rr} {c} {s})))

  -- bwd-in : invert the network ev; at phase A it must be input.
  bwd-in-build :
    ∀ cs {d} {l : Event√ NetR} {t₂′} → Reach cs pA → ⟦ cs ⟧N d ─[ ev l ]─► t₂′
    → Σ[ a ∈ Data ] (Σ[ eq ∈ l ≡ inputLbl a ]
        (Σ[ cs′ ∈ CS ] ((t₂′ ≡ ⟦ cs′ ⟧N a) × Reach cs′ pB)))
  bwd-in-build cs {d} r step with reflectV cs step
  ... | nInG {t} {rr} {o} {c} {s} a refl Lin Weq =
        let (hT , hO , hC) = pinA {t} {rr} {o} {c} {s} (reach-Inv r) (reach-phaseA r)
        in a , Lin , mkCS I1 t rr o c s ,
           trans Weq (cong (_∖ csTA') (mix≡uni {t} {rr} {o} {c} {s} {a} {d} hT hO hC)) ,
           reach-vA r NM.input
  ... | nOutG refl Lout Weq = ⊥-elim (phaseA-out≢O1 r refl)

  -- bwd-out : invert the network ev; at phase B it must be output.
  bwd-out-build :
    ∀ cs {d} {l : Event√ NetR} {t₂′} → Reach cs pB → ⟦ cs ⟧N d ─[ ev l ]─► t₂′
    → Σ[ eq ∈ l ≡ outputLbl d ]
        (Σ[ cs′ ∈ CS ]
          ((t₂′ ≡ ⟦ cs′ ⟧N d) × Reach cs′ pA × (inp cs′ ≢ I0) × (out cs′ ≢ O1)))
  bwd-out-build cs r step with reflectV cs step
  ... | nOutG {i} {t} {rr} {c} {s} refl Lout Weq =
        Lout , mkCS i t rr O2 c s , Weq , reach-vB r NM.output ,
        (λ i≡ → pB-inp≢I0 r i≡) , out-step-tgt {i} {t} {rr} {c} {s}
  ... | nInG a refl Lin Weq = ⊥-elim (pB-inp≢I0 r refl)

  -- noev-AO : an inp≠I0 ∧ out≠O1 state offers no strong visible event.
  noev-build :
    ∀ cs {d} {l : Event√ NetR} {t₂′} → inp cs ≢ I0 → out cs ≢ O1
    → ⟦ cs ⟧N d ─[ ev l ]─► t₂′ → ⊥
  noev-build cs i≢ o≢ step with reflectV cs step
  ... | nInG a refl Lin Weq = i≢ refl
  ... | nOutG refl Lout Weq = o≢ refl

------------------------------------------------------------------------
-- Payload-preserving modulo-csTA inversion.  Identical to Gen's `sim-modA`
-- but with the conclusion's payload PINNED to the incoming `d` (every
-- internal step preserves the in-flight payload), so the τ-reflection below
-- can recurse the spec side `C0`/`C1 d` at a FIXED `d`.
------------------------------------------------------------------------
sim-modA-d : ∀ cs {d W′} → ModAStep csTA' (⟦ cs ⟧ d) W′
           → Σ[ cs′ ∈ CS ] ((cs ⇒ᵢ cs′) × (W′ ≡ ⟦ cs′ ⟧ d))
sim-modA-d (mkCS i t r o c s) {d} (maτ parτ)
  with Par-τ-elim csTA' ⊤merge (decTx i t r d) (decRx o c s d) parτ
... | τL P′ Txτ refl with sim-Tx-τ {i} {t} {r} {d} Txτ
...   | inj₁ (refl , refl , Weq) =
        mkCS I2 T1 r o c s , NM.sndmsg ,
        cong (λ z → (z ∥⇘ csTA' ⇙ (decRx o c s d))) Weq
...   | inj₂ (inj₁ (refl , refl , Weq)) =
        mkCS Ig t Rg o c s , NM.rcvack ,
        cong (λ z → (z ∥⇘ csTA' ⇙ (decRx o c s d))) Weq
...   | inj₂ (inj₂ (inj₁ (refl , Weq))) =
        mkCS I0 t r o c s , gI ,
        cong (λ z → (z ∥⇘ csTA' ⇙ (decRx o c s d))) Weq
...   | inj₂ (inj₂ (inj₂ (inj₁ (refl , Weq)))) =
        mkCS i T0 r o c s , gT ,
        cong (λ z → (z ∥⇘ csTA' ⇙ (decRx o c s d))) Weq
...   | inj₂ (inj₂ (inj₂ (inj₂ (refl , Weq)))) =
        mkCS i t R0 o c s , gR ,
        cong (λ z → (z ∥⇘ csTA' ⇙ (decRx o c s d))) Weq
sim-modA-d (mkCS i t r o c s) {d} (maτ parτ)
  | τR Q′ Rxτ refl with sim-Rx-τ {o} {c} {s} {d} Rxτ
...   | inj₁ (refl , refl , Weq) =
        mkCS i t r O1 Rcg s , NM.rcvmsg ,
        cong (λ z → ((decTx i t r d) ∥⇘ csTA' ⇙ z)) Weq
...   | inj₂ (inj₁ (refl , refl , Weq)) =
        mkCS i t r Og c Sa1 , NM.sndack ,
        cong (λ z → ((decTx i t r d) ∥⇘ csTA' ⇙ z)) Weq
...   | inj₂ (inj₂ (inj₁ (refl , Weq))) =
        mkCS i t r O0 c s , gO ,
        cong (λ z → ((decTx i t r d) ∥⇘ csTA' ⇙ z)) Weq
...   | inj₂ (inj₂ (inj₂ (inj₁ (refl , Weq)))) =
        mkCS i t r o Rc0 s , gRc ,
        cong (λ z → ((decTx i t r d) ∥⇘ csTA' ⇙ z)) Weq
...   | inj₂ (inj₂ (inj₂ (inj₂ (refl , Weq)))) =
        mkCS i t r o c Sa0 , gSa ,
        cong (λ z → ((decTx i t r d) ∥⇘ csTA' ⇙ z)) Weq
sim-modA-d (mkCS i t r o c s) {d} (maE mem parev)
  with Par-ev-elim csTA' ⊤merge (decTx i t r d) (decRx o c s d) parev
... | evL  ¬cs _   = ⊥-elim (¬cs mem)
... | evR  ¬cs _   = ⊥-elim (¬cs mem)
... | evBoth ¬cs _ _ = ⊥-elim (¬cs mem)
... | evSync _ Txev Rxev with sim-Tx-ev {i} {t} {r} {d} Txev | sim-Rx-ev {o} {c} {s} {d} Rxev
...   | inj₁ (_ , _ , Lin , _) | inj₁ (_ , Lout , _) =
          ⊥-elim (inputLbl≢outputLbl (trans (sym Lin) Lout))
...   | inj₁ (_ , _ , Lin , _) | inj₂ (inj₁ (_ , _ , Ltx , _)) =
          ⊥-elim (inputLbl≢txLbl (trans (sym Lin) Ltx))
...   | inj₁ (_ , _ , Lin , _) | inj₂ (inj₂ (_ , Lack , _)) =
          ⊥-elim (inputLbl≢ackLbl (trans (sym Lin) Lack))
...   | inj₂ (inj₁ (refl , Ltx , refl)) | inj₁ (_ , Lout , _) =
          ⊥-elim (outputLbl≢txLbl (trans (sym Lout) Ltx))
...   | inj₂ (inj₁ (refl , Ltx , refl)) | inj₂ (inj₁ (a′ , refl , Ltx′ , WeqRx)) =
          mkCS i Tg r o Rc1 s , NM.tx ,
          cong (Par⊤ csTA' (decTx i Tg r d))
            (trans WeqRx (cong (λ z → decRxᵢ o Rc1 s z d) (txLbl-inj (trans (sym Ltx′) Ltx))))
...   | inj₂ (inj₁ (refl , Ltx , refl)) | inj₂ (inj₂ (_ , Lack , _)) =
          ⊥-elim (txLbl≢ackLbl (trans (sym Ltx) Lack))
...   | inj₂ (inj₂ (refl , Lack , refl)) | inj₁ (_ , Lout , _) =
          ⊥-elim (outputLbl≢ackLbl (trans (sym Lout) Lack))
...   | inj₂ (inj₂ (refl , Lack , refl)) | inj₂ (inj₁ (_ , _ , Ltx , _)) =
          ⊥-elim (txLbl≢ackLbl (trans (sym Ltx) Lack))
...   | inj₂ (inj₂ (refl , _ , refl)) | inj₂ (inj₂ (refl , _ , refl)) =
          mkCS i t R1 o c Sag , NM.ack , refl

------------------------------------------------------------------------
-- STEP 3.  The generic expansion builder (parametrised by `VisWit`).
--
--   expA : C0   ⪰ ⟦cs⟧N d   for a phase-A state cs
--   expB : C1 d ⪰ ⟦cs⟧N d   for a phase-B state cs
--   expG : Cg d ⪰ ⟦cs⟧N d   for an output-target phase-A state
------------------------------------------------------------------------

module _ (w : VisWit) where
  open VisWit w

  expA : ∀ cs d → Reach cs pA → C0 ⪰ ⟦ cs ⟧N d
  expB : ∀ cs d → Reach cs pB → C1 d ⪰ ⟦ cs ⟧N d
  expG : ∀ cs d → inp cs ≢ I0 → out cs ≢ O1 → Reach cs pA → Cg d ⪰ ⟦ cs ⟧N d

  -- shared: reflect a network τ to an internal `⇒ᵢ` step (phase AND payload
  -- preserved — internal steps keep the in-flight `d`).
  reflectτ : ∀ cs {d} {t₂′} → ⟦ cs ⟧N d ─[ τ ]─► t₂′
           → Σ[ cs′ ∈ CS ] ((cs NM.⇒ᵢ cs′) × (t₂′ ≡ ⟦ cs′ ⟧N d))
  reflectτ cs step with Hide-τ-elim csTA' (⟦ cs ⟧ _) step
  ... | hτP T′ Tτ refl      = let (cs′ , red , Weq) = sim-modA-d cs (maτ Tτ)
                              in cs′ , red , cong (_∖ csTA') Weq
  ... | hτH T′ mem Tev refl = let (cs′ , red , Weq) = sim-modA-d cs (maE mem Tev)
                              in cs′ , red , cong (_∖ csTA') Weq

  -- ===========================  expA  (C0)  ===========================
  expA cs d r .Expand.fwd .WSimF.on-ev (sRet ())
  expA cs d r .Expand.fwd .WSimF.on-ev (sVis eqf breq) with C0-evL (sVis eqf breq)
  ... | a , refl , refl with fwd-in a r
  ...   | cs′ , wstep , r′ = ⟦ cs′ ⟧N a , wstep , expB cs′ a r′
  expA cs d r .Expand.fwd .WSimF.on-tau step = ⊥-elim (C0-noτ step)
  expA cs d r .Expand.bwd .ExpBwdF.bon-tau step with reflectτ cs step
  ... | cs′ , red , refl = inj₂ (expA cs′ d (reach-i r red))
  expA cs d r .Expand.bwd .ExpBwdF.bon-ev step with bwd-in r step
  ... | a , refl , cs′ , refl , r′ = C1 a , C0─input─►C1 , expB cs′ a r′
  expA cs d r .Expand.div→ dv = ⊥-elim (¬Div-C0 dv)
  expA cs d r .Expand.div← dv = ⊥-elim (¬Div-⟦⟧N cs d dv)

  -- ===========================  expB  (C1)  ===========================
  expB cs d r .Expand.fwd .WSimF.on-ev (sRet ())
  expB cs d r .Expand.fwd .WSimF.on-ev (sVis eqf breq) with C1-evL (sVis eqf breq)
  ... | refl , refl with fwd-out r
  ...   | cs′ , wstep , r′ , i≢ , o≢ = ⟦ cs′ ⟧N d , wstep , expG cs′ d i≢ o≢ r′
  expB cs d r .Expand.fwd .WSimF.on-tau step = ⊥-elim (C1-noτ step)
  expB cs d r .Expand.bwd .ExpBwdF.bon-tau step with reflectτ cs step
  ... | cs′ , red , refl = inj₂ (expB cs′ d (reach-i r red))
  expB cs d r .Expand.bwd .ExpBwdF.bon-ev step with bwd-out r step
  ... | refl , cs′ , refl , r′ , i≢ , o≢ = Cg d , C1─output─►Cg , expG cs′ d i≢ o≢ r′
  expB cs d r .Expand.div→ dv = ⊥-elim (¬Div-C1 dv)
  expB cs d r .Expand.div← dv = ⊥-elim (¬Div-⟦⟧N cs d dv)

  -- ===========================  expG  (Cg)  ===========================
  expG cs d i≢ o≢ r .Expand.fwd .WSimF.on-ev (sRet eqf) = ⊥-elim (Cg-noret eqf)
  expG cs d i≢ o≢ r .Expand.fwd .WSimF.on-ev (sVis eqf breq) = ⊥-elim (Cg-noev (sVis eqf breq))
  expG cs d i≢ o≢ r .Expand.fwd .WSimF.on-tau step with Cg-τ step
  ... | refl = ⟦ cs ⟧N d , wτ τ*-refl , expA cs d r
  expG cs d i≢ o≢ r .Expand.bwd .ExpBwdF.bon-tau step with reflectτ cs step
  ... | cs′ , red , refl = inj₁ (C0 , Cg─τ─►C0 , expA cs′ d (reach-i r red))
  expG cs d i≢ o≢ r .Expand.bwd .ExpBwdF.bon-ev step = ⊥-elim (noev-AO {cs = cs} i≢ o≢ step)
  expG cs d i≢ o≢ r .Expand.div→ dv = ⊥-elim (¬Div-Cg dv)
  expG cs d i≢ o≢ r .Expand.div← dv = ⊥-elim (¬Div-⟦⟧N cs d dv)

------------------------------------------------------------------------
-- FINAL ASSEMBLY (Task 6).  MASTER KEY & COROLLARIES, generalised in `Data`.
--
--   Network ≈DR CopySpec        (master key: divergence-respecting weak
--                                bisimulation, built by the expansion at
--                                `theVisWit`/`cs0`)
--     ⇒ Network ≈FD CopySpec     (failures-divergences equivalence — FDR's
--                                `[FD=` BOTH ways; via drbisim→≈FD, which
--                                internally relies on the certified postulate
--                                `¬-divergent→normal` from Semantics.DRImpliesFD)
--       ⇒ failures-half both ways  (Network ⊑F⊥ CopySpec, CopySpec ⊑F⊥ Network)
--     ⇒ Network ⟺T CopySpec      (trace equivalence; derived from the weak-bisim
--                                shadow drbisim→wbisim WITHOUT the postulate).
--
-- Defeq used in step 1:  `C0 = CopySpec` (definitional, see C0's def in Gen)
-- and `⟦ cs0 ⟧N d ≡ Network` (`dec-cs0 = refl`, definitional and d-INDEPENDENT),
-- so the builder's result type `C0 ⪰ ⟦ cs0 ⟧N d` is `CopySpec ⪰ Network` on the
-- nose — no `subst` is needed.
--
-- Payload bookkeeping for `cs0`/`d`:  `⟦ cs0 ⟧N d` is d-INDEPENDENT (reduces to
-- `Network` for ANY `d`), but `expA cs0 d reach-cs0` still requires a `d : Data`
-- argument to NAME the result.  We therefore phrase every headline result as a
-- function of an ARBITRARY `(d : Data)`.  This is honest: if `Data` is empty
-- there is no behaviour to witness and the equivalence is vacuous; for every
-- inhabitant `d` the SAME `Network ≈DR CopySpec` is produced (the result does
-- not actually depend on `d`).  We do NOT postulate an inhabitant of `Data`.
------------------------------------------------------------------------

-- 1.  The expansion at the start state, type reduced via the two definitional
--     equalities (C0 = CopySpec, ⟦ cs0 ⟧N d = Network for ANY d).
net-exp : Data → CopySpec ⪰ Network
net-exp d = expA theVisWit cs0 d reach-cs0

-- 2.  Master key:  Network ≈DR CopySpec
--     (⪯→≈DR : t₁ ⪰ t₂ → t₂ ≈DR t₁, with t₁ = CopySpec, t₂ = Network).
net≈DR : Data → Network ≈DR CopySpec
net≈DR d = ⪯→≈DR (net-exp d)

-- 3.  Failures-divergences equivalence (FDR `[FD=` both ways).
net≈FD : Data → Network ≈FD CopySpec
net≈FD d = drbisim→≈FD (net≈DR d)

-- 4.  The headline FAILURES results (both directions of ≈FD).
net⊑FD : Data → Network ⊑FD CopySpec
net⊑FD d = proj₁ (net≈FD d)

spec⊑FD : Data → CopySpec ⊑FD Network
spec⊑FD d = proj₂ (net≈FD d)

--   The failures-half both ways.  `CopySpec ⊑F⊥ Network` is the standard
--   refinement statement "the Network refines the CopySpec".
net⊑F⊥ : Data → Network ⊑F⊥ CopySpec
net⊑F⊥ d = proj₁ (net⊑FD d)

spec⊑F⊥ : Data → CopySpec ⊑F⊥ Network
spec⊑F⊥ d = proj₁ (spec⊑FD d)

-- 5.  TRACE equivalence (derivable from ≈DR via its weak-bisim shadow,
--     WITHOUT the ¬-divergent→normal postulate).
net≈W : Data → Wbisim NetR Network CopySpec
net≈W d = drbisim→wbisim (net≈DR d)

--   `P ⊑T Q = ∀ s → traces Q s → traces P s`, and
--   `traces-respects-≈ : Wbisim R P Q → (traces P s → traces Q s)
--                                      × (traces Q s → traces P s)`.
net⊑T : Data → Network ⊑T CopySpec
net⊑T d s = proj₂ (traces-respects-≈ (net≈W d))

spec⊑T : Data → CopySpec ⊑T Network
spec⊑T d s = proj₁ (traces-respects-≈ (net≈W d))
