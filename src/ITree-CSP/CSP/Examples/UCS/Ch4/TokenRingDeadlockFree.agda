{-# OPTIONS --guardedness #-}

-- UCS chapter 4 §4.2: the token ring is DEADLOCK-FREE.
--
-- Machine-readable companion file:
--
--   fdr-examples/ucs/chapter04/tokring.csp   (UCS ch. 4, the token ring)
--
-- FDR reports two assertions on the token ring:
--
--   assert Ring  :[deadlock free]      -- HOLDS  (proved here, for the UNHIDDEN Ring)
--   assert RingH :[divergence free]    -- FAILS  (the sibling `TokenRing` proves the livelock)
--
-- This module proves `Ring :[deadlock free]` for the single circulating token at
-- the minimal instance N = 2.  The node states, per-node alphabets, and the ring
-- composition are IMPORTED verbatim from `CSP.Examples.UCS.Ch4.TokenRing`; nothing
-- is redefined.  In particular the OFFERS ARE PINNED (NodeR's `send` is restricted
-- to `dst ≠ n`, NodeF forwards the SPECIFIC held packet), because DeadlockFree is a
-- UNIVERSAL claim — a value-generalised offer would be unsound.
--
-- PROOF APPROACH (the `RoutingRingNonBlocking` data-tag technique).  Every node is
-- react-headed and STABLE (τ-map ≡ ∅t), so the composite's only moves are VISIBLE (a
-- solo send/receive of one node, or a ring hand-off synchronised between the two
-- adjacent nodes).  We track each node by its reachable POSITION CLASS (NodeE / NodeR
-- / NodeF pkt, the pinned packet EXISTENTIAL in the class) and carry a joint
-- reachability predicate `RSys` whose FOUR constructors are exactly the reachable
-- single-token occupancies: the token (empty or full) sits at node 0 or at node 1,
-- the other node being empty.  The forbidden two-token / zero-token configurations
-- are ABSENT by construction: a ring hand-off moves the one token across the link,
-- never creating or destroying it.  `RSys` is closed under stepping (`sys-inv`) and
-- every `RSys` state can move (`enabled`) — the token holder always has an enabled
-- action (send / pass empty / deliver / forward full); `Progress` and `DeadlockFree`
-- follow via `progress⇒deadlockFree`.
--
-- The step inversions are given as PER-POSITION result types (`FromE0`/`FromR0`/…),
-- each carrying only the transitions reachable from that concrete node state and
-- indexed by the TARGET.  Splitting such a result (at a variable target) never asks
-- Agda to distinguish two non-injective defined node terms — sidestepping the
-- `UnificationStuck` wall that a single source-indexed relation would hit once the
-- config is concretised.

module CSP.Examples.UCS.Ch4.TokenRingDeadlockFree where

open import Level using () renaming (zero to lzero)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
import Data.Fin as Fin
open import Data.Unit.Polymorphic renaming (⊤ to ⊤poly) using ()
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_)
open import Function.Base using (case_of_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import Process_Trees
open PTree

open import CSP.Examples.UCS.Ch4.TokenRing
  using ( TkEv; TkEv-≟; Node; sucm; Token; A; NodeE; NodeR; NodeF; Init; Ring
        ; send; receive; ring; Empty; Full )
open import CSP.Operators TkEv-≟
open EventSet

open import Semantics.LTS       {E = TkEv} {I = ExtI TkEv}
open import Semantics.Failures  {E = TkEv} {I = ExtI TkEv}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev)
open import Semantics.Deadlock  {E = TkEv} {I = ExtI TkEv}
  using (DeadlockFree; _⟹∖√⟨_⟩_; embed∖√)
open import Semantics.DeadlockDR {E = TkEv} {I = ExtI TkEv}
  using (Progress; progress⇒deadlockFree)
open import CSP.Laws.AlphaParallel TkEv-≟
  using ( αVisR; vSync; vSoloL; vSoloR; v√
        ; αpar-vis-step-inv; αpar-τ-step-inv; αpar-√-step-inv )

-------------------------------------------------------------------------------------
-- §0. Nodes, the local ring plumbing, and the composite state.
-------------------------------------------------------------------------------------

n0 n1 : Node
n0 = fzero
n1 = fsuc fzero

TProc : Set₁
TProc = PTree TkEv (ExtI TkEv) (⊤poly {lzero})

node : Node → Comp TkEv (⊤poly {lzero})
node i = comp (A i) (Init i)

RetR : Set
RetR = RetOf⁺ (node n0) (node n1 ∷ [])

-- The union alphabet of the (singleton) folded tail, and the binary composite.
B1 : EventSet
B1 = unionα (node n1 ∷ [])

Sys : TProc → TProc → PTree TkEv (ExtI TkEv) RetR
Sys t0 t1 = t0 ⟦ A n0 ∥ B1 ⟧ t1

-- The imported ring is the initial composite (node 0 holds the empty token).
ring≡ : Ring ≡ Sys (NodeR n0) (NodeE n1)
ring≡ = refl

-------------------------------------------------------------------------------------
-- §1. Per-node reachable POSITION CLASSES (existential in the pinned packet).
-------------------------------------------------------------------------------------

data Pos0 : TProc → Set where
  pE0 :         Pos0 (NodeE n0)
  pR0 :         Pos0 (NodeR n0)
  pF0 : ∀ p → Pos0 (NodeF n0 p)

data Pos1 : TProc → Set where
  pE1 :         Pos1 (NodeE n1)
  pR1 :         Pos1 (NodeR n1)
  pF1 : ∀ p → Pos1 (NodeF n1 p)

pos0-noret : ∀ {t x} → Pos0 t → t .force ≡ ret x → ⊥
pos0-noret pE0     ()
pos0-noret pR0     ()
pos0-noret (pF0 _) ()

n0-noτ : ∀ {t t′} → Pos0 t → t ─[ τ ]─► t′ → ⊥
n0-noτ pE0     (sSil eq)      = case eq of λ ()
n0-noτ pE0     (sTau refl br) = case br of λ ()
n0-noτ pR0     (sSil eq)      = case eq of λ ()
n0-noτ pR0     (sTau refl br) = case br of λ ()
n0-noτ (pF0 _) (sSil eq)      = case eq of λ ()
n0-noτ (pF0 _) (sTau refl br) = case br of λ ()

n1-noτ : ∀ {t t′} → Pos1 t → t ─[ τ ]─► t′ → ⊥
n1-noτ pE1     (sSil eq)      = case eq of λ ()
n1-noτ pE1     (sTau refl br) = case br of λ ()
n1-noτ pR1     (sSil eq)      = case eq of λ ()
n1-noτ pR1     (sTau refl br) = case br of λ ()
n1-noτ (pF1 _) (sSil eq)      = case eq of λ ()
n1-noτ (pF1 _) (sTau refl br) = case br of λ ()

-------------------------------------------------------------------------------------
-- §2. Per-position visible-step inversions.  Each result type lists ONLY the
-- transitions of that concrete node state, indexed by the TARGET (and, for NodeF, the
-- held packet) so that a later split never confronts two defined node terms.  Ring
-- events pin the token constructor (Empty / Full q); the sync correlation in
-- `vis-route` then prunes the incompatible pairings by event unification.
-------------------------------------------------------------------------------------

-- ── node 0 ──────────────────────────────────────────────────────────────────────
data FromE0 : TProc → Event → Set₁ where
  fe0-inE :       FromE0 (NodeR n0)   (evLabel (Node × Token) ring (n0 , Empty))
  fe0-inF : ∀ q → FromE0 (NodeF n0 q) (evLabel (Node × Token) ring (n0 , Full q))

fromE0-inv : ∀ {t′ e} → NodeE n0 ─[ ev (evl e) ]─► t′ → FromE0 t′ e
fromE0-inv (sVis {at = _ , send}    refl br) = case br of λ ()
fromE0-inv (sVis {at = _ , receive} refl br) = case br of λ ()
fromE0-inv (sVis {at = _ , ring} {a = fzero , Empty}       refl br) = subst (λ z → FromE0 z _) (just-injective br) fe0-inE
fromE0-inv (sVis {at = _ , ring} {a = fsuc fzero , Empty}  refl br) = case br of λ ()
fromE0-inv (sVis {at = _ , ring} {a = fzero , Full q}      refl br) = subst (λ z → FromE0 z _) (just-injective br) (fe0-inF q)
fromE0-inv (sVis {at = _ , ring} {a = fsuc fzero , Full q} refl br) = case br of λ ()

data FromR0 : TProc → Event → Set₁ where
  fr0-send : ∀ dst → FromR0 (NodeF n0 (n0 , dst)) (evLabel (Node × Node)  send (n0 , dst))
  fr0-pass :         FromR0 (NodeE n0)             (evLabel (Node × Token) ring (n1 , Empty))

fromR0-inv : ∀ {t′ e} → NodeR n0 ─[ ev (evl e) ]─► t′ → FromR0 t′ e
fromR0-inv (sVis {at = _ , send} {a = fzero , fzero}      refl br) = case br of λ ()
fromR0-inv (sVis {at = _ , send} {a = fzero , fsuc fzero} refl br) = subst (λ z → FromR0 z _) (just-injective br) (fr0-send (fsuc fzero))
fromR0-inv (sVis {at = _ , send} {a = fsuc fzero , dst}   refl br) = case br of λ ()
fromR0-inv (sVis {at = _ , receive}                       refl br) = case br of λ ()
fromR0-inv (sVis {at = _ , ring} {a = fzero , Empty}      refl br) = case br of λ ()
fromR0-inv (sVis {at = _ , ring} {a = fsuc fzero , Empty} refl br) = subst (λ z → FromR0 z _) (just-injective br) fr0-pass
fromR0-inv (sVis {at = _ , ring} {a = j , Full x}         refl br) = case br of λ ()

data FromF0 : (Node × Node) → TProc → Event → Set₁ where
  ff0-recv : ∀ s src → FromF0 (s , n0) (NodeR n0) (evLabel (Node × Node)  receive (n0 , src))
  ff0-fwd  : ∀ s q   → FromF0 (s , n1) (NodeE n0) (evLabel (Node × Token) ring    (n1 , Full q))

fromF0-inv : ∀ {t′ e} (p : Node × Node) → NodeF n0 p ─[ ev (evl e) ]─► t′ → FromF0 p t′ e
fromF0-inv (s , fzero) (sVis {at = _ , send} refl br) = case br of λ ()
fromF0-inv (s , fzero) (sVis {at = _ , receive} {a = fzero , src}      refl br) with src Fin.≟ s
... | yes _ = subst (λ z → FromF0 _ z _) (just-injective br) (ff0-recv s src)
... | no  _ = case br of λ ()
fromF0-inv (s , fzero) (sVis {at = _ , receive} {a = fsuc fzero , src} refl br) = case br of λ ()
fromF0-inv (s , fzero) (sVis {at = _ , ring} {a = j , Empty}  refl br) = case br of λ ()
fromF0-inv (s , fzero) (sVis {at = _ , ring} {a = j , Full x} refl br) = case br of λ ()
fromF0-inv (s , fsuc fzero) (sVis {at = _ , send}    refl br) = case br of λ ()
fromF0-inv (s , fsuc fzero) (sVis {at = _ , receive} refl br) = case br of λ ()
fromF0-inv (s , fsuc fzero) (sVis {at = _ , ring} {a = fzero , Full x}                       refl br) = case br of λ ()
fromF0-inv (s , fsuc fzero) (sVis {at = _ , ring} {a = fsuc fzero , Full (s′ , fzero)}       refl br) with s′ Fin.≟ s
... | yes _ = case br of λ ()
... | no  _ = case br of λ ()
fromF0-inv (s , fsuc fzero) (sVis {at = _ , ring} {a = fsuc fzero , Full (s′ , fsuc fzero)}  refl br) with s′ Fin.≟ s
... | yes _ = subst (λ z → FromF0 _ z _) (just-injective br) (ff0-fwd s (s′ , fsuc fzero))
... | no  _ = case br of λ ()
fromF0-inv (s , fsuc fzero) (sVis {at = _ , ring} {a = j , Empty} refl br) = case br of λ ()

-- ── node 1 (index n1; forward index sucm n1 = n0) ─────────────────────────────────
data FromE1 : TProc → Event → Set₁ where
  fe1-inE :       FromE1 (NodeR n1)   (evLabel (Node × Token) ring (n1 , Empty))
  fe1-inF : ∀ q → FromE1 (NodeF n1 q) (evLabel (Node × Token) ring (n1 , Full q))

fromE1-inv : ∀ {t′ e} → NodeE n1 ─[ ev (evl e) ]─► t′ → FromE1 t′ e
fromE1-inv (sVis {at = _ , send}    refl br) = case br of λ ()
fromE1-inv (sVis {at = _ , receive} refl br) = case br of λ ()
fromE1-inv (sVis {at = _ , ring} {a = fsuc fzero , Empty}  refl br) = subst (λ z → FromE1 z _) (just-injective br) fe1-inE
fromE1-inv (sVis {at = _ , ring} {a = fzero , Empty}       refl br) = case br of λ ()
fromE1-inv (sVis {at = _ , ring} {a = fsuc fzero , Full q} refl br) = subst (λ z → FromE1 z _) (just-injective br) (fe1-inF q)
fromE1-inv (sVis {at = _ , ring} {a = fzero , Full q}      refl br) = case br of λ ()

data FromR1 : TProc → Event → Set₁ where
  fr1-send : ∀ dst → FromR1 (NodeF n1 (n1 , dst)) (evLabel (Node × Node)  send (n1 , dst))
  fr1-pass :         FromR1 (NodeE n1)             (evLabel (Node × Token) ring (n0 , Empty))

fromR1-inv : ∀ {t′ e} → NodeR n1 ─[ ev (evl e) ]─► t′ → FromR1 t′ e
fromR1-inv (sVis {at = _ , send} {a = fsuc fzero , fsuc fzero} refl br) = case br of λ ()
fromR1-inv (sVis {at = _ , send} {a = fsuc fzero , fzero}      refl br) = subst (λ z → FromR1 z _) (just-injective br) (fr1-send fzero)
fromR1-inv (sVis {at = _ , send} {a = fzero , dst}            refl br) = case br of λ ()
fromR1-inv (sVis {at = _ , receive}                           refl br) = case br of λ ()
fromR1-inv (sVis {at = _ , ring} {a = fzero , Empty}          refl br) = subst (λ z → FromR1 z _) (just-injective br) fr1-pass
fromR1-inv (sVis {at = _ , ring} {a = fsuc fzero , Empty}     refl br) = case br of λ ()
fromR1-inv (sVis {at = _ , ring} {a = j , Full x}             refl br) = case br of λ ()

data FromF1 : (Node × Node) → TProc → Event → Set₁ where
  ff1-recv : ∀ s src → FromF1 (s , n1) (NodeR n1) (evLabel (Node × Node)  receive (n1 , src))
  ff1-fwd  : ∀ s q   → FromF1 (s , n0) (NodeE n1) (evLabel (Node × Token) ring    (n0 , Full q))

fromF1-inv : ∀ {t′ e} (p : Node × Node) → NodeF n1 p ─[ ev (evl e) ]─► t′ → FromF1 p t′ e
fromF1-inv (s , fsuc fzero) (sVis {at = _ , send}    refl br) = case br of λ ()
fromF1-inv (s , fsuc fzero) (sVis {at = _ , receive} {a = fsuc fzero , src} refl br) with src Fin.≟ s
... | yes _ = subst (λ z → FromF1 _ z _) (just-injective br) (ff1-recv s src)
... | no  _ = case br of λ ()
fromF1-inv (s , fsuc fzero) (sVis {at = _ , receive} {a = fzero , src} refl br) = case br of λ ()
fromF1-inv (s , fsuc fzero) (sVis {at = _ , ring} {a = j , Empty}  refl br) = case br of λ ()
fromF1-inv (s , fsuc fzero) (sVis {at = _ , ring} {a = j , Full x} refl br) = case br of λ ()
fromF1-inv (s , fzero) (sVis {at = _ , send}    refl br) = case br of λ ()
fromF1-inv (s , fzero) (sVis {at = _ , receive} refl br) = case br of λ ()
fromF1-inv (s , fzero) (sVis {at = _ , ring} {a = j , Empty}                        refl br) = case br of λ ()
fromF1-inv (s , fzero) (sVis {at = _ , ring} {a = fsuc fzero , Full x}              refl br) = case br of λ ()
fromF1-inv (s , fzero) (sVis {at = _ , ring} {a = fzero , Full (s′ , fsuc fzero)}   refl br) with s′ Fin.≟ s
... | yes _ = case br of λ ()
... | no  _ = case br of λ ()
fromF1-inv (s , fzero) (sVis {at = _ , ring} {a = fzero , Full (s′ , fzero)}        refl br) with s′ Fin.≟ s
... | yes _ = subst (λ z → FromF1 _ z _) (just-injective br) (ff1-fwd s (s′ , fzero))
... | no  _ = case br of λ ()

-------------------------------------------------------------------------------------
-- §3. The joint reachability predicate: the single token sits at exactly one node.
-------------------------------------------------------------------------------------

data RSys : TProc → TProc → Set₁ where
  r-R0 :       RSys (NodeR n0)   (NodeE n1)      -- empty token at node 0
  r-F0 : ∀ p → RSys (NodeF n0 p) (NodeE n1)      -- full  token at node 0
  r-R1 :       RSys (NodeE n0)   (NodeR n1)      -- empty token at node 1
  r-F1 : ∀ p → RSys (NodeE n0)   (NodeF n1 p)    -- full  token at node 1

rsys-init : RSys (NodeR n0) (NodeE n1)
rsys-init = r-R0

rsys-pos0 : ∀ {t0 t1} → RSys t0 t1 → Pos0 t0
rsys-pos0 r-R0     = pR0
rsys-pos0 (r-F0 p) = pF0 p
rsys-pos0 r-R1     = pE0
rsys-pos0 (r-F1 p) = pE0

rsys-pos1 : ∀ {t0 t1} → RSys t0 t1 → Pos1 t1
rsys-pos1 r-R0     = pE1
rsys-pos1 (r-F0 p) = pE1
rsys-pos1 r-R1     = pR1
rsys-pos1 (r-F1 p) = pF1 p

-------------------------------------------------------------------------------------
-- §4. Single-step closure of RSys.  τ / √ are impossible (react-headed, stable
-- nodes); each visible step routes sync / solo-L / solo-R and lands back in RSys.
-------------------------------------------------------------------------------------

sys-no√ : ∀ {t0 t1 x} → RSys t0 t1 → Sys t0 t1 .force ≡ ret x → ⊥
sys-no√ rs feq with αpar-√-step-inv feq
... | v√ p0 _ = pos0-noret (rsys-pos0 rs) p0

sys-noτ : ∀ {t0 t1 t′} → RSys t0 t1 → Sys t0 t1 ─[ τ ]─► t′ → ⊥
sys-noτ rs st with αpar-τ-step-inv st
... | inj₁ (_ , pτ , _) = n0-noτ (rsys-pos0 rs) pτ
... | inj₂ (_ , qτ , _) = n1-noτ (rsys-pos1 rs) qτ

-- Route a visible step out of a reachable config.  Matching `rs` first (at variable
-- indices) pins the concrete config; the per-position inversions then land back in
-- RSys.  Incompatible sync pairings are pruned by event unification.
vis-route : ∀ {t0 t1 t′ e} → RSys t0 t1 → αVisR (A n0) B1 t0 t1 t′ (evl e)
          → Σ[ u0 ∈ TProc ] Σ[ u1 ∈ TProc ] (t′ ≡ Sys u0 u1 × RSys u0 u1)
-- config r-R0 : (NodeR n0 , NodeE n1)
vis-route r-R0 (vSync _ _ p0 q1) with fromR0-inv p0 | fromE1-inv q1
... | fr0-pass | fe1-inE = _ , _ , refl , r-R1
vis-route r-R0 (vSoloL _ ¬pB p0) with fromR0-inv p0
... | fr0-send dst = _ , _ , refl , r-F0 (n0 , dst)
... | fr0-pass     = ⊥-elim (¬pB (inj₁ (inj₁ refl)))
vis-route r-R0 (vSoloR ¬pA _ q1) with fromE1-inv q1
... | fe1-inE   = ⊥-elim (¬pA (inj₂ refl))
... | fe1-inF q = ⊥-elim (¬pA (inj₂ refl))
-- config r-F0 p : (NodeF n0 p , NodeE n1)
vis-route (r-F0 p) (vSync _ _ p0 q1) with fromF0-inv p p0 | fromE1-inv q1
... | ff0-fwd s _ | fe1-inF q = _ , _ , refl , r-F1 q
vis-route (r-F0 p) (vSoloL _ ¬pB p0) with fromF0-inv p p0
... | ff0-recv s src = _ , _ , refl , r-R0
... | ff0-fwd s q    = ⊥-elim (¬pB (inj₁ (inj₁ refl)))
vis-route (r-F0 p) (vSoloR ¬pA _ q1) with fromE1-inv q1
... | fe1-inE   = ⊥-elim (¬pA (inj₂ refl))
... | fe1-inF q = ⊥-elim (¬pA (inj₂ refl))
-- config r-R1 : (NodeE n0 , NodeR n1)
vis-route r-R1 (vSync _ _ p0 q1) with fromE0-inv p0 | fromR1-inv q1
... | fe0-inE | fr1-pass = _ , _ , refl , r-R0
vis-route r-R1 (vSoloL _ ¬pB p0) with fromE0-inv p0
... | fe0-inE   = ⊥-elim (¬pB (inj₁ (inj₂ refl)))
... | fe0-inF q = ⊥-elim (¬pB (inj₁ (inj₂ refl)))
vis-route r-R1 (vSoloR ¬pA _ q1) with fromR1-inv q1
... | fr1-send dst = _ , _ , refl , r-F1 (n1 , dst)
... | fr1-pass     = ⊥-elim (¬pA (inj₁ refl))
-- config r-F1 p : (NodeE n0 , NodeF n1 p)
vis-route (r-F1 p) (vSync _ _ p0 q1) with fromE0-inv p0 | fromF1-inv p q1
... | fe0-inF q | ff1-fwd s _ = _ , _ , refl , r-F0 q
vis-route (r-F1 p) (vSoloL _ ¬pB p0) with fromE0-inv p0
... | fe0-inE   = ⊥-elim (¬pB (inj₁ (inj₂ refl)))
... | fe0-inF q = ⊥-elim (¬pB (inj₁ (inj₂ refl)))
vis-route (r-F1 p) (vSoloR ¬pA _ q1) with fromF1-inv p q1
... | ff1-recv s src = _ , _ , refl , r-R1
... | ff1-fwd s q    = ⊥-elim (¬pA (inj₁ refl))

sys-inv : ∀ {t0 t1 l t′} → RSys t0 t1 → Sys t0 t1 ─[ l ]─► t′
        → Σ[ u0 ∈ TProc ] Σ[ u1 ∈ TProc ] (t′ ≡ Sys u0 u1 × RSys u0 u1)
sys-inv rs (sRet feq)    = ⊥-elim (sys-no√ rs feq)
sys-inv rs (sSil feq)    = ⊥-elim (sys-noτ rs (sSil feq))
sys-inv rs (sTau feq br) = ⊥-elim (sys-noτ rs (sTau feq br))
sys-inv rs (sVis feq br) = vis-route rs (αpar-vis-step-inv feq br)

-------------------------------------------------------------------------------------
-- §5. Reachability closure: every ⟹-reachable ring state is a reachable RSys config.
-------------------------------------------------------------------------------------

reach-cons : ∀ {s t′} → Ring ⟹⟨ s ⟩ t′
           → Σ[ t0 ∈ TProc ] Σ[ t1 ∈ TProc ] (t′ ≡ Sys t0 t1 × RSys t0 t1)
reach-cons = go rsys-init refl
  where
    go : ∀ {t0 t1 t s t′} → RSys t0 t1 → t ≡ Sys t0 t1 → t ⟹⟨ s ⟩ t′
       → Σ[ u0 ∈ TProc ] Σ[ u1 ∈ TProc ] (t′ ≡ Sys u0 u1 × RSys u0 u1)
    go rs refl ⟹-refl         = _ , _ , refl , rs
    go rs refl (⟹-τ  st rest) = let (_ , _ , eq , rs′) = sys-inv rs st in go rs′ eq rest
    go rs refl (⟹-ev st rest) = let (_ , _ , eq , rs′) = sys-inv rs st in go rs′ eq rest

-------------------------------------------------------------------------------------
-- §6. Every reachable configuration can MOVE.  Node step lemmas: NodeF deliveries /
-- ring forwards of the pinned held packet.  The packet's source `s` is abstract, so
-- it is split fzero / fsuc fzero for the offer-map `_Fin.≟_` guards to reduce (Node =
-- Fin 2), whereupon the offer equation is `refl`.
-------------------------------------------------------------------------------------

step-recv0 : ∀ s → NodeF n0 (s , n0) ─[ ev (evl (evLabel (Node × Node) receive (n0 , s))) ]─► NodeR n0
step-recv0 fzero        = sVis refl refl
step-recv0 (fsuc fzero) = sVis refl refl

step-fwd0 : ∀ s → NodeF n0 (s , n1) ─[ ev (evl (evLabel (Node × Token) ring (n1 , Full (s , n1)))) ]─► NodeE n0
step-fwd0 fzero        = sVis refl refl
step-fwd0 (fsuc fzero) = sVis refl refl

step-recv1 : ∀ s → NodeF n1 (s , n1) ─[ ev (evl (evLabel (Node × Node) receive (n1 , s))) ]─► NodeR n1
step-recv1 fzero        = sVis refl refl
step-recv1 (fsuc fzero) = sVis refl refl

step-fwd1 : ∀ s → NodeF n1 (s , n0) ─[ ev (evl (evLabel (Node × Token) ring (n0 , Full (s , n0)))) ]─► NodeE n1
step-fwd1 fzero        = sVis refl refl
step-fwd1 (fsuc fzero) = sVis refl refl

enabled : ∀ {t0 t1} → RSys t0 t1
        → Σ[ l ∈ Label RetR ] Σ[ t″ ∈ PTree TkEv (ExtI TkEv) RetR ] (Sys t0 t1 ─[ l ]─► t″)
-- node 0 holds empty token: inject a fresh packet (send.n0.n1, solo).
enabled r-R0 = _ , _ ,
  αpar-soloL-step {at = _ , send} {a = n0 , n1} refl (λ { (inj₁ ()) ; (inj₂ ()) }) refl refl refl
-- node 0 holds full token, is destination (r = n0): deliver (receive.n0.s, solo).
enabled (r-F0 (s , fzero)) =
  let (_ , _ , eqP , bP) = ev-inv (step-recv0 s)
  in _ , _ , αpar-soloL-step {at = _ , receive} {a = n0 , s} refl (λ { (inj₁ ()) ; (inj₂ ()) }) eqP bP refl
-- node 0 holds full token, not destination (r = n1): forward (ring.n1.Full, sync).
enabled (r-F0 (s , fsuc fzero)) =
  let (_ , _ , eqP , bP) = ev-inv (step-fwd0 s)
  in _ , _ , αpar-sync-step {at = _ , ring} {a = n1 , Full (s , n1)} (inj₂ refl) (inj₁ (inj₁ refl)) eqP bP refl refl
-- node 1 holds empty token: inject a fresh packet (send.n1.n0, solo).
enabled r-R1 = _ , _ ,
  αpar-soloR-step {at = _ , send} {a = n1 , n0} (λ ()) (inj₁ refl) refl refl refl
-- node 1 holds full token, is destination (r = n1): deliver (receive.n1.s, solo).
enabled (r-F1 (s , fsuc fzero)) =
  let (_ , _ , eqQ , bQ) = ev-inv (step-recv1 s)
  in _ , _ , αpar-soloR-step {at = _ , receive} {a = n1 , s} (λ ()) (inj₁ refl) refl eqQ bQ
-- node 1 holds full token, not destination (r = n0): forward (ring.n0.Full, sync).
enabled (r-F1 (s , fzero)) =
  let (_ , _ , eqQ , bQ) = ev-inv (step-fwd1 s)
  in _ , _ , αpar-sync-step {at = _ , ring} {a = n0 , Full (s , n0)} (inj₁ refl) (inj₁ (inj₂ refl)) refl refl eqQ bQ

-------------------------------------------------------------------------------------
-- §7. THE THEOREM: the token ring (N = 2, single circulating token) is DEADLOCK-FREE.
-------------------------------------------------------------------------------------

tokenRing-deadlockFree : DeadlockFree Ring
tokenRing-deadlockFree = progress⇒deadlockFree tr-progress
  where
    tr-progress : Progress Ring
    tr-progress bs with reach-cons (embed∖√ bs)
    ... | (_ , _ , refl , rs) = enabled rs
