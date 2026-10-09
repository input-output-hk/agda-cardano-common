{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- LeiosNotify terminating does not affect the other mini-protocols — at the level of the
-- node's PEER BUNDLE `PeersP.nodeBundleP l cl sv`.  ∀ `Params`, ∀ link, ∀ configuration.
--
-- THE COMPOSITION (read off `PeersP`, `Parametric.Node`, `ApiAlphabet`).  A bundle is
-- `⦀⋆ (map slot (linkConfig l))`: every configured `(d , id)` instance contributes ONE
-- renamed peer, and the peers are INTERLEAVED (`⦀`, empty sync set).  A node is
-- `linkBundlesWith mk n ∥⇘ apiES ⇙ logic` (bundles of all incident links interleaved, then
-- synchronised with the node logic on every api channel and on `done`), and the system puts
-- all nodes against the medium on `ioES`.  So inside the bundle the peers share NOTHING:
-- an LN peer can neither block nor enable a step of another peer.
--
-- THE RESULTS.
--   (A) `bundle-elim` / `bundle-intro`: a √-free run of an interleaved bundle `⦀⋆ Ps` is
--       exactly one run per component, merged by an `ILv` (csp-ptree's n-ary interleaving
--       witness), the reached state τ-resolving to the bundle of the component ends.  The
--       right-nested `⦀⋆` counterpart of `InterleaveNest.Nest-reach-elim/intro`.
--   (B) `⦀⋆-drop∼`: a component that has RETURNED (√ is its only move) can be deleted from
--       the bundle up to STRONG bisimulation — `Skip` is the unit of `⦀` and `∼` is a
--       congruence for `Par`.
--   (C) `drop-terminated` (the main theorem, generic): along ANY √-free run of `⦀⋆ Ps`, once
--       component i has terminated, (1) the reached state is `∼` (hence `≈DR`,
--       `drop-terminated-DR`) to a state V of the bundle WITHOUT component i, and (2) V is
--       reached by `⦀⋆ (del i Ps)` itself along `s′`, where the run's trace `s` is exactly
--       component i's own trace interleaved with `s′`.  So the other peers' history is a
--       genuine run of the other peers alone, and their future is unchanged.
--   (D) `lnGone`: (C) at `nodeBundleP`, for the slot of any configured LeiosNotify instance
--       (`slot-client` / `slot-server` identify it as `LNPclientA` / `LNPserverA`), with the
--       bundle-without-LN being `nodeBundleP`'s own builder over the configuration minus
--       that instance (`del-slots`).
--   (E) `lnClientEnds`: NON-VACUITY — on every link configured with LeiosNotify on `lo`, the
--       bundle has a run (the quit command, MsgQuit, MsgDone; every other peer idle) after
--       which the LN client has returned, so (D)'s hypothesis is met.
--
-- WHAT THIS DOES NOT SAY (system level, documented findings, by code reading):
--   * In the SHIPPED system LeiosNotify never terminates.  `apiES` contains every `apiLP`
--     and every `done` event, so the peers' `lnpSendDone` (client quit) and `done`
--     (server's End) steps need a node-logic partner; `NodeLogicL` names neither
--     `lnpSendDone` nor `lnpSendCanceled` (its `using` list), and `Parametric.NodeLogic`
--     offers NO `done` anywhere.  The medium cell `Copy l d LN` never returns either
--     (`LeiosNotifyQuitNet`).  System-level non-interference is therefore vacuous today.
--   * Thread coupling in `NodeLogicL`.  The node's threads are all interleaved (`⦀`) and
--     meet only the five stores on `storeES`; stores are read-pointer MENUS (a read is
--     non-destructive and holds no lock), so a stuck LN thread blocks no other thread and
--     no store.  BUT the coupling is functional: the ONE Notify client thread
--     `lnClientBodyL` also drives the LeiosFetch CLIENT (`fetchBody` / `fetchTxs` issue
--     `lfpSendBlockRequest` / `lfpSendBlockTxsRequest` in response to Notify offers), so
--     with the LN client gone that thread blocks at `lnpSendRequestNext` and the LF client
--     on that endpoint is never driven again (no deadlock, just no more fetches).  On the
--     server side `lnServerLoopL`, `bodyOfferLoop` and `voteOfferLoop` each block after a
--     store read at their LN api send; the LF server threads (`ebServeLoop`,
--     `ebTxsServeLoop`) are untouched.
--   * Below the bundle, both directions of an LN instance share one medium cell, and a
--     `break` is per link and kills every cell of that link (`LeiosNotifyQuitNet`).
--
-- AXIOMS.  (A)–(E) are constructive.  `CSP.Laws.FD.ParallelUnit` (imported for
-- `Par-ret-unit`) imports `Semantics.DRImpliesFD`, whose postulate `¬-divergent→normal`
-- is in the module closure but used by no proof here (no `≈FD` is stated).
------------------------------------------------------------------------

open import Cardano_network.Params using (Params)

module Cardano_network.Parametric.Leios.LeiosNotifyIsolation (p : Params) where

open import Level using (0ℓ)
open import Data.Bool using (if_then_else_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise)
  renaming ([] to []ᵖ; _∷_ to _∷ᵖ_)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
import Data.Unit as U
open import Data.Unit.Polymorphic using (⊤; tt)
open import Function using (case_of_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Class.DecEq using (_≟_)

open import Process_Trees
open import Cardano_network.Base
  using (Dir; lo; hi; IDs; N2N_LeiosNotify; FromInitiator; FromResponder)
open Params p using (linkConfig)
open import Cardano_network.Net p
  using (Link; Net_Api; Net_Api-≟; apiLP; input; output; lnpSendDone)
open import Cardano_network.Data p using (Payload; MsgLNPQuit; MsgLNPDone)
open import Cardano_network.LeiosNotifyP p using (LNPEv; LNPEv-≟; clientStepP)
open import Cardano_network.Parametric.Topology using (opposite)
open import Cardano_network.Parametric.Leios.PeersP p
  using (Proc; ιLNP; ιLNP⁻¹; ιLNP-linv; LNPclientA; LNPserverA; clientPeerP; serverPeerP
        ; nodeBundleP)
-- the client's abstract steps `CPos` / `CStp` and their realisation `cIntroE`
import Cardano_network.Parametric.Leios.LeiosNotifyQuit p as LQ
-- `ren` (a source step, renamed) and `cS` (a client step out of `cIntroE`)
import Cardano_network.Parametric.Leios.LeiosNotifyQuitNet p as QN

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using (Par; ∅ES; _⦀_; ⦀⋆; Skip)
import CSP.Operators LNPEv-≟ as OL
import CSP.Rename {E₁ = LNPEv} {E₂ = Net_Api Payload} ιLNP ιLNP⁻¹ ιLNP-linv as RnP
import CSP.Laws.Traces.RenameDeadlock {E₁ = LNPEv} {E₂ = Net_Api Payload} ιLNP ιLNP⁻¹ ιLNP-linv
  as RP

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
import Semantics.LTS {E = LNPEv} {I = ExtI LNPEv} as L1
open import Semantics.Failures {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev)
open import Semantics.Bisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (_∼_; Sbisim; SSimF; sbisim-refl; sbisim-trans)
open import Semantics.DRBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using (_≈DR_)
open import Semantics.StrongImpliesDR {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (sbisim→drbisim)

open import CSP.Laws.FD.ParallelUnit (Net_Api-≟ {Payload}) using (Par-ret-unit; tm)
open import CSP.Laws.Bisim.ParallelCong (Net_Api-≟ {Payload}) using (cong-Par-∼)
open import CSP.Laws.Bisim.IterCong (Net_Api-≟ {Payload}) using (ret-no-τ)
open import CSP.Laws.Traces.TraceLawsParallelTrace (Net_Api-≟ {Payload})
  using (ParInter; pnil; psoloL; psoloR)
open import CSP.Laws.Traces.ReplicationApprox (Net_Api-≟ {Payload}) using (IsEvl; isEvl; ⟹-++)
open import CSP.Laws.Traces.InterleaveNest (Net_Api-≟ {Payload})
  using (Pick; here; there; ILv; ilv-nil; ilv-step; Runs; ILv-cons; ILv-uncons
        ; Par-reach-elim; Par-reach-intro)
open import CSP.Laws.Traces.InterleaveFold (Net_Api-≟ {Payload}) (tm {0ℓ}) using (inter-evl)

------------------------------------------------------------------------
-- §1  List positions
------------------------------------------------------------------------

-- a trace of a component or of a bundle (√-free in every result below)
Tr : Set₁
Tr = List (Event√ (⊤ {0ℓ}))

-- `At xs i x`: x is the i-th element (counting from 0) of xs
data At {a} {A : Set a} : List A → ℕ → A → Set a where
  at0 : ∀ {x xs} → At (x ∷ xs) zero x
  atS : ∀ {x y xs i} → At xs i x → At (y ∷ xs) (suc i) x

-- the list with its i-th element removed (unchanged when there is none)
del : ∀ {a} {A : Set a} → ℕ → List A → List A
del _       []       = []
del zero    (_ ∷ xs) = xs
del (suc i) (x ∷ xs) = x ∷ del i xs

-- removal commutes with `map`
del-map : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) (i : ℕ) (xs : List A)
        → del i (map f xs) ≡ map f (del i xs)
del-map f _       []       = refl
del-map f zero    (_ ∷ xs) = refl
del-map f (suc i) (x ∷ xs) = cong (f x ∷_) (del-map f i xs)

-- a position survives `map`
At-map : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) {xs i x} → At xs i x → At (map f xs) i (f x)
At-map f at0     = at0
At-map f (atS a) = atS (At-map f a)

-- a list has one element per position
At-fun : ∀ {a} {A : Set a} {xs i} {x y : A} → At xs i x → At xs i y → x ≡ y
At-fun at0     at0     = refl
At-fun (atS a) (atS b) = At-fun a b

-- an `All` fact holds at every position
All-At : ∀ {a ℓ} {A : Set a} {P : A → Set ℓ} {xs i x} → All P xs → At xs i x → P x
All-At (px ∷ _)  at0     = px
All-At (_ ∷ pxs) (atS a) = All-At pxs a

-- an `All` fact survives removal
All-del : ∀ {a ℓ} {A : Set a} {P : A → Set ℓ} (i : ℕ) {xs} → All P xs → All P (del i xs)
All-del _       []         = []
All-del zero    (_ ∷ pxs)  = pxs
All-del (suc i) (px ∷ pxs) = px ∷ All-del i pxs

-- a pointwise relation survives removal at the same position on both sides
Pw-del : ∀ {a b ℓ} {A : Set a} {B : Set b} {R : A → B → Set ℓ} (i : ℕ) {xs ys}
       → Pointwise R xs ys → Pointwise R (del i xs) (del i ys)
Pw-del _       []ᵖ       = []ᵖ
Pw-del zero    (_ ∷ᵖ rs) = rs
Pw-del (suc i) (r ∷ᵖ rs) = r ∷ᵖ Pw-del i rs

-- the left partner, under a pointwise relation, of the element at a position
Pw-At : ∀ {a b ℓ} {A : Set a} {B : Set b} {R : A → B → Set ℓ} {xs ys i y}
      → Pointwise R xs ys → At ys i y → Σ[ x ∈ A ] (At xs i x × R x y)
Pw-At (r ∷ᵖ _)  at0     = _ , at0 , r
Pw-At (_ ∷ᵖ rs) (atS a) = case Pw-At rs a of λ where
  (x , ax , rx) → x , atS ax , rx

------------------------------------------------------------------------
-- §2  (A) A run of an interleaved bundle is one run per component
------------------------------------------------------------------------

-- a √-free run of `Skip` is empty and stays at `Skip`
skip-run : ∀ {s : Tr} {W : Proc} → Skip ⟹⟨ s ⟩ W → All IsEvl s → (s ≡ []) × (W ≡ Skip)
skip-run ⟹-refl               _        = refl , refl
skip-run (⟹-τ st _)           _        = ⊥-elim (ret-no-τ refl st)
skip-run (⟹-ev (sRet _) _)    (() ∷ _)
skip-run (⟹-ev (sVis () _) _) _

-- a √-free run of the bundle `⦀⋆ Ps` to W, told component by component
record BundleRun (Ps : List Proc) (s : Tr) (W : Proc) : Set₁ where
  field
    -- each component's own trace and end state, in bundle order
    cps  : List (Tr × Proc)
    -- component k runs from its initial tree along its trace to its end
    runs : Runs Ps cps
    -- the bundle trace is an interleaving of the component traces
    ilv  : ILv (map proj₁ cps) s
    -- the reached state τ-resolves to the bundle of the component ends
    end  : W ⟹⟨ [] ⟩ ⦀⋆ (map proj₂ cps)
open BundleRun public

-- (A, elimination) every √-free run of a bundle de-interleaves
bundle-elim : (Ps : List Proc) {s : Tr} {W : Proc} → ⦀⋆ Ps ⟹⟨ s ⟩ W → All IsEvl s → BundleRun Ps s W
bundle-elim [] run ok with skip-run run ok
... | refl , refl = record { cps = [] ; runs = []ᵖ ; ilv = ilv-nil [] ; end = ⟹-refl }
bundle-elim (P ∷ Ps) run ok with Par-reach-elim ∅ES tm P (⦀⋆ Ps) run ok
... | sP , sQ , P′ , Q′ , rP , rQ , PI , res =
  record { cps  = (sP , P′) ∷ cps o
         ; runs = rP ∷ᵖ runs o
         ; ilv  = ILv-cons PI (ilv o) ok
         ; end  = ⟹-++ res (Par-reach-intro ∅ES tm P′ Q′ ⟹-refl (end o) pnil []) }
  where
  -- the tail bundle's own decomposition
  o : BundleRun Ps sQ Q′
  o = bundle-elim Ps rQ (proj₂ (inter-evl PI ok))

-- an interleaving of no components is empty
ilv-[] : ∀ {s : Tr} → ILv [] s → s ≡ []
ilv-[] (ilv-nil _)    = refl
ilv-[] (ilv-step () _)

-- (A, introduction) component runs re-interleave into a run of the bundle to the bundle of
-- their ends
bundle-intro : {Ps : List Proc} {cps : List (Tr × Proc)} {s : Tr}
             → Runs Ps cps → ILv (map proj₁ cps) s → All IsEvl s
             → ⦀⋆ Ps ⟹⟨ s ⟩ ⦀⋆ (map proj₂ cps)
bundle-intro []ᵖ w ok with ilv-[] w
... | refl = ⟹-refl
bundle-intro (r ∷ᵖ rs) w ok with ILv-uncons w ok
... | u , PI , w′ =
  Par-reach-intro ∅ES tm _ _ r (bundle-intro rs w′ (proj₂ (inter-evl PI ok))) PI ok

------------------------------------------------------------------------
-- §3  (B) A returned component can be dropped, up to strong bisimulation
------------------------------------------------------------------------

-- a component has TERMINATED: its tree has returned, so √ is its only move (and inside
-- `⦀` that √ only joins the final joint √)
Returned : Proc → Set₁
Returned P = PTree.force P ≡ ret tt

-- a returned tree is strongly bisimilar to `Skip`
ret∼Skip : ∀ {P : Proc} → Returned P → P ∼ Skip
ret∼Skip r .Sbisim.fwd .SSimF.on-ev  (sRet _)    = deadlock , sRet refl , sbisim-refl deadlock
ret∼Skip r .Sbisim.fwd .SSimF.on-ev  (sVis eq _) = case trans (sym r) eq of λ ()
ret∼Skip r .Sbisim.fwd .SSimF.on-tau st          = ⊥-elim (ret-no-τ r st)
ret∼Skip r .Sbisim.bwd .SSimF.on-ev  (sRet _)    = deadlock , sRet r , sbisim-refl deadlock
ret∼Skip r .Sbisim.bwd .SSimF.on-ev  (sVis () _)
ret∼Skip r .Sbisim.bwd .SSimF.on-tau st          = ⊥-elim (ret-no-τ refl st)

-- (B) in an interleaved bundle a returned component can be deleted: `P ⦀ Q ∼ Skip ⦀ Q ∼ Q`
-- at its position, and `∼` is a congruence for `⦀` everywhere above it
⦀⋆-drop∼ : ∀ {Ps : List Proc} {i P} → At Ps i P → Returned P → ⦀⋆ Ps ∼ ⦀⋆ (del i Ps)
⦀⋆-drop∼ {_ ∷ Ps} at0 r =
  sbisim-trans (cong-Par-∼ ∅ES tm (ret∼Skip r) (sbisim-refl (⦀⋆ Ps))) (Par-ret-unit (⦀⋆ Ps))
⦀⋆-drop∼ {Q ∷ _} (atS a) r = cong-Par-∼ ∅ES tm (sbisim-refl Q) (⦀⋆-drop∼ a r)

------------------------------------------------------------------------
-- §4  Removing one component from an n-ary interleaving
------------------------------------------------------------------------

-- where one interleaving step lands relative to position i: ON component i (its trace grows
-- by e, the others are unchanged), or on another component (the step survives removing i)
pick-del : ∀ {e : Event√ (⊤ {0ℓ})} {tss tss′ : List Tr} {t′ : Tr} (i : ℕ)
         → Pick e tss tss′ → At tss′ i t′
         → (Σ[ t ∈ Tr ] ((t′ ≡ e ∷ t) × At tss i t × (del i tss ≡ del i tss′)))
           ⊎ (At tss i t′ × Pick e (del i tss) (del i tss′))
pick-del zero    here       at0     = inj₁ (_ , refl , at0 , refl)
pick-del zero    (there pk) at0     = inj₂ (at0 , pk)
pick-del (suc i) here       (atS a) = inj₂ (atS a , here)
pick-del (suc i) (there pk) (atS a) with pick-del i pk a
... | inj₁ (t , eq , a′ , d) = inj₁ (t , eq , atS a′ , cong (_ ∷_) d)
... | inj₂ (a′ , pk′)        = inj₂ (atS a′ , there pk′)

-- removing component i from an interleaving: the merged trace splits into component i's own
-- trace against the merged trace of the others
ILv-del : ∀ {tss : List Tr} {s t : Tr} (i : ℕ) → At tss i t → ILv tss s → All IsEvl s
        → Σ[ s′ ∈ Tr ] (ParInter ∅ES tm t s′ s × ILv (del i tss) s′)
ILv-del i a (ilv-nil z) _ with All-At z a
... | refl = [] , pnil , ilv-nil (All-del i z)
ILv-del i a (ilv-step pk w) (isEvl _ ∷ ok) with pick-del i pk a
... | inj₁ (_ , refl , a′ , d) = case ILv-del i a′ w ok of λ where
        (s′ , PI , w′) → s′ , psoloL (λ z → z) PI , subst (λ x → ILv x s′) d w′
... | inj₂ (a′ , pk′) = case ILv-del i a′ w ok of λ where
        (s′ , PI , w′) → _ ∷ s′ , psoloR (λ z → z) PI , ilv-step pk′ w′

------------------------------------------------------------------------
-- §5  (C) The main theorem, generic in the bundle
------------------------------------------------------------------------

-- what a bundle run looks like once its terminated component i (trace t, end P) is set aside
record Dropped (Ps : List Proc) (s : Tr) (W : Proc) (i : ℕ) (t : Tr) (P : Proc) : Set₁ where
  field
    -- component i's own run: from its initial tree along t to its returned end P
    own   : Σ[ P₀ ∈ Proc ] (At Ps i P₀ × P₀ ⟹⟨ t ⟩ P)
    -- the reached state, τ-resolved
    W′    : Proc
    res   : W ⟹⟨ [] ⟩ W′
    -- the merged trace of the OTHER components: s is t interleaved with s′
    s′    : Tr
    split : ParInter ∅ES tm t s′ s
    -- a state of the bundle WITHOUT component i, reached by that bundle along s′ …
    V     : Proc
    runV  : ⦀⋆ (del i Ps) ⟹⟨ s′ ⟩ V
    -- … and strongly bisimilar to the reached state
    iso   : W′ ∼ V
open Dropped public

-- (C) ISOLATION OF A TERMINATED COMPONENT.  Along any √-free run of an interleaved bundle, as
-- de-interleaved by any `BundleRun` (e.g. `bundle-elim`'s), once component i has returned the
-- bundle IS (`∼`, after τ-resolution) the bundle without i, in a state that bundle reaches
-- on its own along the run's trace minus component i's events
drop-terminated : ∀ {Ps s W} (o : BundleRun Ps s W) {i t P}
                → At (cps o) i (t , P) → Returned P → All IsEvl s → Dropped Ps s W i t P
drop-terminated {Ps} o {i} {t} {P} a r ok = record
  { own   = Pw-At (runs o) a
  ; W′    = ⦀⋆ (map proj₂ (cps o))
  ; res   = end o
  ; s′    = proj₁ d
  ; split = proj₁ (proj₂ d)
  ; V     = ⦀⋆ (map proj₂ (del i (cps o)))
  ; runV  = bundle-intro (Pw-del i (runs o))
              (subst (λ x → ILv x (proj₁ d)) (del-map proj₁ i (cps o)) (proj₂ (proj₂ d)))
              (proj₂ (inter-evl (proj₁ (proj₂ d)) ok))
  ; iso   = subst (λ x → ⦀⋆ (map proj₂ (cps o)) ∼ ⦀⋆ x) (del-map proj₂ i (cps o))
              (⦀⋆-drop∼ (At-map proj₂ a) r) }
  where
  -- component i's trace split off the bundle trace
  d : Σ[ s′ ∈ Tr ] (ParInter ∅ES tm t s′ _ × ILv (del i (map proj₁ (cps o))) s′)
  d = ILv-del i (At-map proj₁ a) (ilv o) ok

-- (C) at `≈DR`: the same isolation up to divergence-respecting weak bisimulation
drop-terminated-DR : ∀ {Ps s W} (o : BundleRun Ps s W) {i t P}
                   → (a : At (cps o) i (t , P)) (r : Returned P) (ok : All IsEvl s)
                   → W′ (drop-terminated o {i} a r ok) ≈DR V (drop-terminated o {i} a r ok)
drop-terminated-DR o {i} a r ok = sbisim→drbisim (iso (drop-terminated o {i} a r ok))

------------------------------------------------------------------------
-- §6  (D) The LeiosNotify instance in the prototype bundle
------------------------------------------------------------------------

-- one configured instance's slot in `nodeBundleP l cl sv` (the builder's own lambda, named)
slotP : Link → Dir → Dir → Dir × IDs → Proc
slotP l cl sv (d , id) =
  if ⌊ d ≟ cl ⌋ then clientPeerP l d id
  else if ⌊ d ≟ sv ⌋ then serverPeerP l d id
  else Skip

-- the prototype bundle's component list
slots : Link → Dir → Dir → List Proc
slots l cl sv = map (slotP l cl sv) (linkConfig l)

-- `nodeBundleP` IS the interleaving of its slots
nodeBundleP-slots : ∀ l cl sv → nodeBundleP l cl sv ≡ ⦀⋆ (slots l cl sv)
nodeBundleP-slots l cl sv = refl

-- the bundle without instance i is the builder over the configuration without it
del-slots : ∀ l cl sv i → del i (slots l cl sv) ≡ map (slotP l cl sv) (del i (linkConfig l))
del-slots l cl sv i = del-map (slotP l cl sv) i (linkConfig l)

-- a LeiosNotify slot on the client direction is the renamed prototype LN client
slot-client : ∀ l cl sv → slotP l cl sv (cl , N2N_LeiosNotify) ≡ LNPclientA l cl
slot-client l lo sv = refl
slot-client l hi sv = refl

-- a LeiosNotify slot on the server direction (the opposite one, as `Node.bundleAtWith`
-- places it) is the renamed prototype LN server
slot-server : ∀ l cl → slotP l cl (opposite cl) (opposite cl , N2N_LeiosNotify) ≡ LNPserverA l (opposite cl)
slot-server l lo = refl
slot-server l hi = refl

-- (D) LEIOSNOTIFY ENDING DOES NOT AFFECT THE OTHER PEERS OF THE BUNDLE.  For any √-free
-- run of `nodeBundleP l cl sv` (de-interleaved by any `BundleRun`, e.g. `bundle-elim`), if the
-- slot of the configured LeiosNotify instance `(d , N2N_LeiosNotify)` at position i has
-- terminated, then: that slot is the LN peer the builder put there; the run's trace is the LN
-- peer's own trace interleaved with a trace s′ of the bundle built over the configuration
-- WITHOUT that instance; and the reached state is strongly bisimilar to the state that
-- LN-free bundle reaches along s′ — every other peer's past and future are those of a bundle
-- in which LeiosNotify never existed
lnGone : (l : Link) (cl sv : Dir) {s : Tr} {W : Proc} (o : BundleRun (slots l cl sv) s W)
         {i : ℕ} {d : Dir} {t : Tr} {P : Proc}
       → At (linkConfig l) i (d , N2N_LeiosNotify) → At (cps o) i (t , P) → Returned P
       → All IsEvl s
       → Σ[ D ∈ Dropped (slots l cl sv) s W i t P ]
           (proj₁ (own D) ≡ slotP l cl sv (d , N2N_LeiosNotify))
           × (⦀⋆ (del i (slots l cl sv)) ≡ ⦀⋆ (map (slotP l cl sv) (del i (linkConfig l))))
lnGone l cl sv o {i} {d} cfg a r ok =
  D , At-fun (proj₁ (proj₂ (own D))) (At-map (slotP l cl sv) cfg) , cong ⦀⋆ (del-slots l cl sv i)
  where
  -- the generic isolation, at the prototype bundle
  D : Dropped (slots l cl sv) _ _ i _ _
  D = drop-terminated o a r ok

------------------------------------------------------------------------
-- §7  (E) Non-vacuity: the LN client really terminates inside the bundle
------------------------------------------------------------------------

-- the client's quit handshake as the bundle sees it: the application's quit command, MsgQuit
-- out on the wire, MsgDone in from the wire (the peers' fixed envelope)
quitTr : Link → Tr
quitTr l =
    evl (evLabel _ (apiLP l lo lnpSendDone) U.tt)
  ∷ evl (evLabel _ (input  l lo N2N_LeiosNotify) (LQ.pay l FromInitiator MsgLNPQuit))
  ∷ evl (evLabel _ (output l lo N2N_LeiosNotify) (LQ.pay l FromResponder MsgLNPDone))
  ∷ []

-- the quit handshake is √-free
quitTr-evl : ∀ l → All IsEvl (quitTr l)
quitTr-evl l = isEvl _ ∷ isEvl _ ∷ isEvl _ ∷ []

-- the client's source tree at End
cEnd : Link → LQ.Tree
cEnd l = OL.iter-bind (OL.Ret (inj₂ tt)) (clientStepP l lo)

-- the renamed LN client on `lo`, alone, performs the quit handshake and reaches End
lnClientQuits : ∀ l → LNPclientA l lo ⟹⟨ quitTr l ⟩ RnP.renameMap (cEnd l)
lnClientQuits l =
  ⟹-ev (QN.ren l (QN.cS l LQ.cpI (LQ.cQi U.tt)))
  (⟹-ev (QN.ren l (QN.cS l LQ.cpS LQ.cSQ))
  (⟹-τ (RP.ren-τ-fwd {inv = RnP.ι-vis-inv} (L1.sSil refl))
  (⟹-ev (QN.ren l (QN.cS l LQ.cpQ LQ.cDn))
   ⟹-refl)))

-- … and End is a returned tree
lnClientEnd-ret : ∀ l → Returned (RnP.renameMap (cEnd l))
lnClientEnd-ret l = RP.force-ren-ret {inv = RnP.ι-vis-inv} {P = cEnd l} refl

-- an idle component: the empty trace, ending where it started
idleOf : Proc → Tr × Proc
idleOf P = [] , P

-- the solo decomposition: component i runs along q to P′, every other component stays put
solo : List Proc → ℕ → Tr → Proc → List (Tr × Proc)
solo []       _       q P′ = []
solo (_ ∷ Ps) zero    q P′ = (q , P′) ∷ map idleOf Ps
solo (P ∷ Ps) (suc i) q P′ = ([] , P) ∷ solo Ps i q P′

-- idle components run along the empty trace
runs-idle : (Ps : List Proc) → Runs Ps (map idleOf Ps)
runs-idle []       = []ᵖ
runs-idle (P ∷ Ps) = ⟹-refl ∷ᵖ runs-idle Ps

-- idle components carry empty traces
idle-[] : (Ps : List Proc) → All (_≡ []) (map proj₁ (map idleOf Ps))
idle-[] []       = []
idle-[] (P ∷ Ps) = refl ∷ idle-[] Ps

-- the solo decomposition is one run per component
runs-solo : ∀ {Ps i P₀ q P′} → At Ps i P₀ → P₀ ⟹⟨ q ⟩ P′ → Runs Ps (solo Ps i q P′)
runs-solo {_ ∷ Ps} at0     r = r ∷ᵖ runs-idle Ps
runs-solo {P ∷ _}  (atS a) r = ⟹-refl ∷ᵖ runs-solo a r

-- the soloist's entry sits at its position
at-solo : ∀ {Ps i P₀ q P′} → At Ps i P₀ → At (solo Ps i q P′) i (q , P′)
at-solo at0     = at0
at-solo (atS a) = atS (at-solo a)

-- a √-free trace interleaves with the empty trace, on the left
inter-L : ∀ {q : Tr} → All IsEvl q → ParInter ∅ES tm q [] q
inter-L []             = pnil
inter-L (isEvl _ ∷ ok) = psoloL (λ z → z) (inter-L ok)

-- a √-free trace interleaves with the empty trace, on the right
inter-R : ∀ {q : Tr} → All IsEvl q → ParInter ∅ES tm [] q q
inter-R []             = pnil
inter-R (isEvl _ ∷ ok) = psoloR (λ z → z) (inter-R ok)

-- the solo decomposition interleaves to the soloist's trace
ilv-solo : ∀ {Ps i P₀ q P′} → At Ps i P₀ → All IsEvl q → ILv (map proj₁ (solo Ps i q P′)) q
ilv-solo {_ ∷ Ps} at0     ok = ILv-cons (inter-L ok) (ilv-nil (idle-[] Ps)) ok
ilv-solo          (atS a) ok = ILv-cons (inter-R ok) (ilv-solo a ok) ok

-- (E) NON-VACUITY.  On every link whose configuration carries LeiosNotify on `lo` (position
-- i), the bundle `nodeBundleP l lo sv` has a √-free run — the quit handshake, every other peer
-- idle — whose de-interleaving has the LN client's slot RETURNED, so `lnGone` applies to it
lnClientEnds : (l : Link) (sv : Dir) {i : ℕ} → At (linkConfig l) i (lo , N2N_LeiosNotify)
             → Σ[ W ∈ Proc ] Σ[ o ∈ BundleRun (slots l lo sv) (quitTr l) W ]
                 (nodeBundleP l lo sv ⟹⟨ quitTr l ⟩ W)
                 × At (cps o) i (quitTr l , RnP.renameMap (cEnd l))
                 × Returned (RnP.renameMap (cEnd l))
lnClientEnds l sv cfg =
  _ , o , bundle-intro (runs o) (ilv o) (quitTr-evl l) , at-solo a , lnClientEnd-ret l
  where
  -- the LN client's slot
  a : At (slots l lo sv) _ (LNPclientA l lo)
  a = At-map (slotP l lo sv) cfg
  -- the solo de-interleaving
  o : BundleRun (slots l lo sv) (quitTr l) (⦀⋆ (map proj₂ (solo (slots l lo sv) _ (quitTr l) (RnP.renameMap (cEnd l)))))
  o = record { cps  = solo (slots l lo sv) _ (quitTr l) (RnP.renameMap (cEnd l))
             ; runs = runs-solo a (lnClientQuits l)
             ; ilv  = ilv-solo a (quitTr-evl l)
             ; end  = ⟹-refl }
