{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Deadlock-freedom groundwork for the Cardano `Network` example.
--
-- This module proves the single `Copy l dr id` buffer (the per-connection
-- component of the `CopySpec` specification) is `Live`: it always has an
-- enabled LTS move and every τ / visible successor is again live.  The
-- proof enumerates the small reachable control-state cycle of the
-- `loop0 (pchoice v)` buffer (head A → after-input B → loop-back C), in
-- the style of the dining-philosophers deadlock-free proof.
------------------------------------------------------------------------

open import Level using (0ℓ; Lift; lift)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Unit using () renaming (tt to tt₀)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; proj₁; proj₂; Σ-syntax; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Function using (case_of_)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees using (PTree; ptree; AnyTypes; ContinueType; ExtI; NodeKind; ret; sil; react; deadlock; react-injective)
open ExtI using (base; pair; fin)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; map)
open PTree
open import CSP.Examples.Cardano_network.Params using (Params)

-- `d₀ : Data` is an inhabitant witness: the head `Copy l dr id` offers `input l dr id ? d`
-- for `d : Data`, so liveness genuinely requires the payload type to be inhabited
-- (an empty `Data` would deadlock the buffer at its first input).
module CSP.Examples.Cardano_network.NetworkVerification.NetworkDeadlockFree
  (p : Params) (Data : Set) ⦃ _ : DecEq Data ⦄ (d₀ : Data) where

open import CSP.Examples.Cardano_network.Net p
  using ( Net; Link; Net-≟
        ; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack )
open import CSP.Examples.Cardano_network.Base using (IDs; Dir)
open Params p using (numLinks; linkConfig)

import CSP.Operators {E = Net Data} (Net-≟ {Data}) as Op
open Op using (pchoice; Skip; loop0; Par; _⦀_; ∅ES; par-pVis; par-brBoth; EventSet; ⦀Fin; ⦀⋆)
open EventSet

open import CSP.Examples.Cardano_network.Network p Data
  using (Copy; NetProc; Menu; copyMenu; linkCopy; CopySpec; Network)
open Op using (Output; _>>=_; Ret; iter; iter-bind)

open import Semantics.LTS {E = Net Data} {I = ExtI (Net Data)}
open import Semantics.DRBisim {E = Net Data} {I = ExtI (Net Data)} using (_≈DR_)
open import Semantics.Deadlock {E = Net Data} {I = ExtI (Net Data)} using (DeadlockFree)
open import Semantics.DeadlockDR {E = Net Data} {I = ExtI (Net Data)}
open Live

-- Single-step parallel transition INTRO / ELIM lemmas (specialised below to ∅ES).
open import CSP.Laws.Traces.TraceLawsParallel (Net-≟ {Data})
  using (Par-τ-L; Par-τ-R; Par-soloL; Par-soloR; fPar-nn)
open import CSP.Laws.Traces.TraceLawsParallelElim (Net-≟ {Data})
  using ( ParτR; τL; τR
        ; ParevR; evSync; evL; evR; evBoth; ev√
        ; Par-τ-elim; Par-ev-elim; fPar-rr )

------------------------------------------------------------------------
-- Probe A (head): `Copy l dr id` is react-headed and stable.
------------------------------------------------------------------------

-- The loop0 step that `Copy l dr id = loop0 (pchoice (copyMenu l dr id))` unfolds to:
-- `loop0 body = iter (λ _ → body >>= λ a′ → Ret (inj₁ a′)) tt`.  Reconstructed here
-- (top-level `copyMenu` makes this possible) so the bind/iter residuals are nameable.
copyStep : (l : Link) (dr : Dir) (id : IDs) → ⊤ {0ℓ} → PTree (Net Data) (ExtI (Net Data)) (⊤ {0ℓ} ⊎ ⊤ {0ℓ})
copyStep l dr id _ = pchoice (copyMenu l dr id) >>= λ a′ → Ret (inj₁ a′)

-- The head of a Copy buffer, before any input: `iter (copyStep l dr id) tt`.
copy-A : (l : Link) (dr : Dir) (id : IDs) → NetProc
copy-A l dr id = iter (copyStep l dr id) tt

-- `copy-A` is definitionally Network's `Copy` (loop0 unfolds to iter of copyStep).
Copy≡ : (l : Link) (dr : Dir) (id : IDs) → Copy l dr id ≡ copy-A l dr id
Copy≡ l dr id = refl

-- Probe: copy-A's force is `react v τc` (recover v, τc by refl).
probe-A : (l : Link) (dr : Dir) (id : IDs)
        → Σ[ v ∈ _ ] Σ[ τc ∈ _ ] (copy-A l dr id .force ≡ react v τc)
probe-A l dr id = _ , _ , refl

-- The head's visible-offer map.
copy-A-v : (l : Link) (dr : Dir) (id : IDs) → _
copy-A-v l dr id = let (v , _ , _) = probe-A l dr id in v

-- The head's τ-branch map.
copy-A-τc : (l : Link) (dr : Dir) (id : IDs) → _
copy-A-τc l dr id = let (_ , τc , _) = probe-A l dr id in τc

-- Stability of A: the τ-branch map is everywhere `nothing` (no τ enabled).
-- `iterT` reads `viewT (react v ∅t) = ∅t = nothing` regardless of the index.
st-A : (l : Link) (dr : Dir) (id : IDs) (i : AnyTypes (ExtI (Net Data))) (a : proj₁ i)
     → copy-A-τc l dr id i a ≡ nothing
st-A l dr id i a = refl

-- Reflexivity of the decidable equalities at a fixed (id , c): they reduce to
-- `yes refl`, but only after case-splitting (id / c are abstract parameters).
id≟id : (id : IDs) → (id ≟ id) ≡ yes refl
id≟id id with id ≟ id
... | yes refl = refl
... | no ¬p    = ⊥-elim (¬p refl)

dr≟dr : (dr : Dir) → (dr ≟ dr) ≡ yes refl
dr≟dr dr with dr ≟ dr
... | yes refl = refl
... | no ¬p    = ⊥-elim (¬p refl)

l≟l : (l : Link) → (l ≟ l) ≡ yes refl
l≟l l with l ≟ l
... | yes refl = refl
... | no ¬p    = ⊥-elim (¬p refl)

-- B d: the residual after `input l dr id d`.  The head's `input` offer maps to
-- `Output (output l dr id) d Skip` (via copyMenu), which `bindV`/`iterV` wrap into the
-- `iter-bind (… >>= k₀) (copyStep l dr id)` below.  Transparent ⇒ its force reduces.
copy-B : (l : Link) (dr : Dir) (id : IDs) → Data → NetProc
copy-B l dr id d =
  iter-bind (Output (output l dr id) d Skip >>= (λ a′ → Ret (inj₁ a′))) (copyStep l dr id)

-- A offers `input l dr id` for any `d : Data`, continuing to `copy-B l dr id d`.
probe-A-off : (l : Link) (dr : Dir) (id : IDs) (d : Data)
            → copy-A-v l dr id (Data , input l dr id) d ≡ just (copy-B l dr id d)
probe-A-off l dr id d rewrite l≟l l | dr≟dr dr | id≟id id = refl

-- Probe: B d's force is `react v τc` (Output is react-headed; bind preserves this).
probe-B : (l : Link) (dr : Dir) (id : IDs) (d : Data)
        → Σ[ v ∈ _ ] Σ[ τc ∈ _ ] (copy-B l dr id d .force ≡ react v τc)
probe-B l dr id d = _ , _ , refl

-- B d's visible-offer map.
copy-B-v : (l : Link) (dr : Dir) (id : IDs) (d : Data) → _
copy-B-v l dr id d = let (v , _ , _) = probe-B l dr id d in v

-- B d's τ-branch map.
copy-B-τc : (l : Link) (dr : Dir) (id : IDs) (d : Data) → _
copy-B-τc l dr id d = let (_ , τc , _) = probe-B l dr id d in τc

-- Stability of B: the τ-branch map is everywhere `nothing` (Output has ∅t τ-part,
-- and `bindT`/`iterT` read `viewT (react … ∅t) = ∅t = nothing` at every index).
st-B : (l : Link) (dr : Dir) (id : IDs) (d : Data)
       (i : AnyTypes (ExtI (Net Data))) (a : proj₁ i)
     → copy-B-τc l dr id d i a ≡ nothing
st-B l dr id d i a = refl

-- C d: the loop-back residual after `output l dr id ! d`.  B's `output` offer maps to
-- `Skip` (Output-cont on the matching value), wrapped to `iter-bind (Skip >>= k₀) …`.
copy-C : (l : Link) (dr : Dir) (id : IDs) → Data → NetProc
copy-C l dr id d =
  iter-bind (Skip >>= (λ a′ → Ret (inj₁ a′))) (copyStep l dr id)

-- B d offers `output l dr id` carrying exactly `d`, continuing to `copy-C l dr id d`.
probe-B-off : (l : Link) (dr : Dir) (id : IDs) (d : Data)
            → copy-B-v l dr id d (Data , output l dr id) d ≡ just (copy-C l dr id d)
probe-B-off l dr id d rewrite l≟l l | dr≟dr dr | id≟id id with d ≟ d
... | yes refl = refl
... | no ¬p    = ⊥-elim (¬p refl)

-- C is sil-headed, looping back to the head A (= Copy l dr id).
probe-C : (l : Link) (dr : Dir) (id : IDs) (d : Data)
        → copy-C l dr id d .force ≡ sil (copy-A l dr id)
probe-C l dr id d = refl

------------------------------------------------------------------------
-- Reachable control states of a Copy buffer and their liveness.
------------------------------------------------------------------------

-- The three reachable control states of `Copy l dr id`: head A, post-input B d,
-- loop-back C d.  (B/C are indexed by the carried datum `d`.)
data CopyPos (l : Link) (dr : Dir) (id : IDs) : NetProc → Set where
  is-A : CopyPos l dr id (copy-A l dr id)
  is-B : (d : Data) → CopyPos l dr id (copy-B l dr id d)
  is-C : (d : Data) → CopyPos l dr id (copy-C l dr id d)

-- Every reachable state has an enabled move: A offers `input l dr id d₀`, B offers
-- `output l dr id d`, C does a τ (loop-back to A).
copyPos-move : ∀ {l dr id t} → CopyPos l dr id t
             → Σ[ l ∈ Label (⊤ {0ℓ}) ] Σ[ t″ ∈ NetProc ] (t ─[ l ]─► t″)
copyPos-move {l} {dr} {id} is-A =
  _ , _ , sVis {at = Data , input l dr id} {a = d₀}
                (let (_ , _ , eq) = probe-A l dr id in eq) (probe-A-off l dr id d₀)
copyPos-move {l} {dr} {id} (is-B d) =
  _ , _ , sVis {at = Data , output l dr id} {a = d}
                (let (_ , _ , eq) = probe-B l dr id d in eq) (probe-B-off l dr id d)
copyPos-move {l} {dr} {id} (is-C d) = _ , _ , sSil (probe-C l dr id d)

-- A τ-step from any Copy position lands on a Copy position.  Only C has a τ
-- (loop-back to A); A and B are stable react nodes (τ-map ≡ nothing everywhere),
-- so their `sSil`/`sTau` are impossible.
copyPos-stepτ : ∀ {l dr id t t″} → CopyPos l dr id t → t ─[ τ ]─► t″ → CopyPos l dr id t″
-- A: react-headed, no sil; τc ≡ nothing everywhere ⇒ no sTau.
copyPos-stepτ {l} {dr} {id} is-A (sSil eq) = case eq of λ ()
copyPos-stepτ {l} {dr} {id} is-A (sTau {i = i} {a = a} refl br) =
  case trans (sym (st-A l dr id i a)) br of λ ()
-- B: same (Output is a stable react node).
copyPos-stepτ {l} {dr} {id} (is-B d) (sSil eq) = case eq of λ ()
copyPos-stepτ {l} {dr} {id} (is-B d) (sTau {i = i} {a = a} refl br) =
  case trans (sym (st-B l dr id d i a)) br of λ ()
-- C: sil-headed, τ-steps to A.
copyPos-stepτ {l} {dr} {id} (is-C d) (sSil refl)      = is-A
copyPos-stepτ {l} {dr} {id} (is-C d) (sTau eq br)     = case eq of λ ()

-- Helper: A's `input l′ dr′ id′` offer is `just (copy-B l dr id a)` exactly when the event
-- targets this buffer (id′ ≡ id, c′ ≡ c); otherwise it is `nothing`.  Keeping the
-- buffer ids (id , c) and event ids (id′ , c′) as distinct explicit arguments avoids
-- the `with`-abstraction conflating them.
A-off-pos : (l : Link) (dr : Dir) (id : IDs) (l′ : Link) (dr′ : Dir) (id′ : IDs) (a : Data) {t″ : NetProc}
          → copy-A-v l dr id (Data , input l′ dr′ id′) a ≡ just t″ → CopyPos l dr id t″
A-off-pos l dr id l′ dr′ id′ a br with l′ ≟ l
... | no  _ = case br of λ ()
A-off-pos l dr id l′ dr′ id′ a br | yes refl with dr′ ≟ dr
... | no  _ = case br of λ ()
A-off-pos l dr id l′ dr′ id′ a br | yes refl | yes refl with id′ ≟ id
... | no  _    = case br of λ ()
... | yes refl = subst (CopyPos l dr id) (just-injective br) (is-B a)

-- Helper (dual): B d's `output l′ dr′ id′` offer fires to `copy-C l dr id d` exactly when the
-- event targets this buffer AND carries the stored datum d; otherwise `nothing`.
B-off-pos : (l : Link) (dr : Dir) (id : IDs) (d : Data)
            (l′ : Link) (dr′ : Dir) (id′ : IDs) (a : Data) {t″ : NetProc}
          → copy-B-v l dr id d (Data , output l′ dr′ id′) a ≡ just t″ → CopyPos l dr id t″
-- B's offer fires through `Output-cont (output l dr id) d Skip`, whose `Net-≟` decision
-- compares buffer-first (`id ≟ id′`, then `c ≟ c′`) and then the value (`a ≟ d`); we
-- mirror that order so the offer reduces (to `nothing` off-target, `just (copy-C)` on).
B-off-pos l dr id d l′ dr′ id′ a br with l ≟ l′
... | no  _ = case br of λ ()
B-off-pos l dr id d l′ dr′ id′ a br | yes refl with dr ≟ dr′
... | no  _ = case br of λ ()
B-off-pos l dr id d l′ dr′ id′ a br | yes refl | yes refl with id ≟ id′
... | no  _ = case br of λ ()
B-off-pos l dr id d l′ dr′ id′ a br | yes refl | yes refl | yes refl with a ≟ d
... | no  _    = case br of λ ()
... | yes refl = subst (CopyPos l dr id) (just-injective br) (is-C d)

-- A visible step from any Copy position lands on a Copy position.  A's only offer
-- is `input l dr id` (→ B); B's only offer is `output l dr id` carrying the stored `d`
-- (→ C); C is sil-headed (no visible offer).  All other events are refused.
copyPos-stepev : ∀ {l dr id t e t″} → CopyPos l dr id t
               → t ─[ ev (evl e) ]─► t″ → CopyPos l dr id t″
-- A: split on the offered event; only `input l dr id` (with matching id/conn) fires.
copyPos-stepev {l} {dr} {id} is-A (sVis {at = _ , input l′ dr′ id′} {a = a} refl br) =
  A-off-pos l dr id l′ dr′ id′ a br
copyPos-stepev {l} {dr} {id} is-A (sVis {at = _ , output _ _ _} refl br) = case br of λ ()
copyPos-stepev {l} {dr} {id} is-A (sVis {at = _ , sndmsg _ _ _} refl br) = case br of λ ()
copyPos-stepev {l} {dr} {id} is-A (sVis {at = _ , rcvmsg _ _ _} refl br) = case br of λ ()
copyPos-stepev {l} {dr} {id} is-A (sVis {at = _ , tx _ _ _}     refl br) = case br of λ ()
copyPos-stepev {l} {dr} {id} is-A (sVis {at = _ , sndack _ _ _} refl br) = case br of λ ()
copyPos-stepev {l} {dr} {id} is-A (sVis {at = _ , rcvack _ _ _} refl br) = case br of λ ()
copyPos-stepev {l} {dr} {id} is-A (sVis {at = _ , ack _ _ _}    refl br) = case br of λ ()
-- B: only `output l dr id` (with matching id/conn AND stored value d) fires.
copyPos-stepev {l} {dr} {id} (is-B d) (sVis {at = _ , output l′ dr′ id′} {a = a} refl br) =
  B-off-pos l dr id d l′ dr′ id′ a br
copyPos-stepev {l} {dr} {id} (is-B d) (sVis {at = _ , input _ _ _}  refl br) = case br of λ ()
copyPos-stepev {l} {dr} {id} (is-B d) (sVis {at = _ , sndmsg _ _ _} refl br) = case br of λ ()
copyPos-stepev {l} {dr} {id} (is-B d) (sVis {at = _ , rcvmsg _ _ _} refl br) = case br of λ ()
copyPos-stepev {l} {dr} {id} (is-B d) (sVis {at = _ , tx _ _ _}     refl br) = case br of λ ()
copyPos-stepev {l} {dr} {id} (is-B d) (sVis {at = _ , sndack _ _ _} refl br) = case br of λ ()
copyPos-stepev {l} {dr} {id} (is-B d) (sVis {at = _ , rcvack _ _ _} refl br) = case br of λ ()
copyPos-stepev {l} {dr} {id} (is-B d) (sVis {at = _ , ack _ _ _}    refl br) = case br of λ ()
-- C: sil-headed, so no visible step (force ≡ sil ≠ react).
copyPos-stepev {l} {dr} {id} (is-C d) (sVis eq br) = case eq of λ ()

-- Coinductive liveness of every Copy position (guarded: the recursive calls sit
-- directly under the `.stepτ`/`.stepev` copatterns of the `Live` record).
copy-live′ : ∀ {l dr id t} → CopyPos l dr id t → Live t
copy-live′ pos .move      = copyPos-move pos
copy-live′ pos .stepτ  st = copy-live′ (copyPos-stepτ  pos st)
copy-live′ pos .stepev st = copy-live′ (copyPos-stepev pos st)

-- The single Copy buffer is live: it always offers a move and stays live.
copy-live : ∀ l dr id → Live (Copy l dr id)
copy-live l dr id = copy-live′ {l} {dr} {id} is-A

------------------------------------------------------------------------
-- Binary interleaving `_⦀_` preserves liveness.
--
-- `P ⦀ Q = Par ∅ES (λ _ _ → tt) P Q`.  We build `Live (P ⦀ Q)` from
-- `Live P`, `Live Q` using the single-step Par INTRO lemmas for `.move`
-- and the single-step Par ELIM lemmas (`Par-τ-elim`/`Par-ev-elim`) for
-- the successors.  The recursive `⦀-live`/`live-brBoth` calls sit directly
-- under the `.stepτ`/`.stepev` copatterns, so the coinduction is guarded.
------------------------------------------------------------------------

-- The interleaving merge: on joint √ both ⊤ values collapse to `tt`.
mtt : ⊤ {0ℓ} → ⊤ {0ℓ} → ⊤ {0ℓ}
mtt _ _ = tt

-- `Skip = Ret tt` is live: it offers the √ move and refuses every τ / visible step.
skip-live : Live (Skip {ℓr = 0ℓ})
skip-live .move          = ev (√ tt) , deadlock , sRet refl
skip-live .stepτ  (sSil eq)   = case eq of λ ()
skip-live .stepτ  (sTau eq _) = case eq of λ ()
skip-live .stepev (sVis eq _) = case eq of λ ()

-- The ∅ES synchronisation set refuses membership of EVERY event: used both to
-- supply the `¬ A .mem` premise of the solo intro lemmas and to refute `evSync`.
∅ES-¬mem : (at : AnyTypes (Net Data)) (a : proj₁ at) → ¬ (∅ES .mem at a)
∅ES-¬mem at a = λ z → z

-- A `just` result of `par-brBoth` is one of its exactly-two τ-targets.
par-brBoth-just-inv : ∀ {P Q P' Q' : NetProc}
                        {i : AnyTypes (ExtI (Net Data))} {a : proj₁ i} {M : NetProc}
                    → par-brBoth ∅ES mtt P Q P' Q' i a ≡ just M
                    → (M ≡ Par ∅ES mtt P' Q) ⊎ (M ≡ Par ∅ES mtt P Q')
par-brBoth-just-inv {i = _ , fin}      {lift fzero}            eq = inj₁ (just-injective (sym eq))
par-brBoth-just-inv {i = _ , fin}      {lift (fsuc fzero)}     eq = inj₂ (just-injective (sym eq))
par-brBoth-just-inv {i = _ , fin}      {lift (fsuc (fsuc _))}  eq = case eq of λ ()
par-brBoth-just-inv {i = _ , base _}   eq = case eq of λ ()
par-brBoth-just-inv {i = _ , pair _ _} eq = case eq of λ ()

-- The both-offer (outside ∅ES) visible step lands in the inline ⊓ overlap node
-- `ptree (react (λ _ _ → nothing) (par-brBoth …))` — an intro for the `no|just|just`
-- branch of `par-pVis` (the dual of `par-pVis-sync-eq`, specialised to ∅ES).
par-pVis-both-eq : ∀ (nP nQ : NodeKind (Net Data) (ExtI (Net Data)) (⊤ {0ℓ}))
                     (P Q : NetProc) {at : AnyTypes (Net Data)} {a : proj₁ at}
                     {P' Q' : NetProc}
                 → Op.viewV nP at a ≡ just P' → Op.viewV nQ at a ≡ just Q'
                 → par-pVis ∅ES mtt nP nQ P Q at a
                   ≡ just (ptree (react (λ _ _ → nothing) (par-brBoth ∅ES mtt P Q P' Q')))
par-pVis-both-eq nP nQ P Q {at = at} {a = a} veP veQ
  with ∅ES .dec at a | Op.viewV nP at a | Op.viewV nQ at a
... | no  _  | just _  | just _  = case veP of λ { refl → case veQ of λ { refl → refl } }
... | yes () | _       | _
... | no  _  | nothing | _       = case veP of λ ()
... | no  _  | just _  | nothing = case veQ of λ ()

-- Closure invariant for interleaving liveness.  A reachable interleaving state is
-- either a genuine `P ⦀ Q` (both halves live), the inline ⊓ overlap node reached by an
-- `evBoth` step (its two τ-targets are already-live `Par` trees), or — for the overlap
-- targets — any already-`Live` tree.  This data type lets the corecursion (`⦀-live′`)
-- close under steps via DATA-returning helpers, keeping every recursive call directly
-- under a `Live` copattern (cf. `copy-live′` / `CopyPos`).
data InterLive : NetProc → Set₁ where
  inter : (P Q : NetProc)       → Live P → Live Q → InterLive (P ⦀ Q)
  brB   : (P Q P' Q' : NetProc) → InterLive (Par ∅ES mtt P' Q) → InterLive (Par ∅ES mtt P Q')
        → InterLive (ptree (react (λ _ _ → nothing) (par-brBoth ∅ES mtt P Q P' Q')))
  emb   : (t : NetProc)         → Live t → InterLive t

-- .move: exhibit ONE enabled move.  P's τ lifts (Par-τ-L); else Q's τ (Par-τ-R);
-- else both are stable (visible/√) and we combine their offers.
⦀-move : ∀ {P Q : NetProc} → Live P → Live Q
       → Σ[ l ∈ Label (⊤ {0ℓ}) ] Σ[ t″ ∈ NetProc ] ((P ⦀ Q) ─[ l ]─► t″)
⦀-move {P} {Q} lP lQ with lP .move
... | τ      , P' , stP = τ , Par ∅ES mtt P' Q , Par-τ-L ∅ES mtt P Q stP
... | ev x   , P' , stP with lQ .move
...   | τ      , Q' , stQ = τ , Par ∅ES mtt P Q' , Par-τ-R ∅ES mtt P Q stQ
...   | ev y   , Q' , stQ = ⦀-move-stable x P' stP y Q' stQ
  where
    -- both operands stable: case on the two visible/√ steps.
    ⦀-move-stable :
        (x : Event√ (⊤ {0ℓ})) (P' : NetProc) → P ─[ ev x ]─► P'
      → (y : Event√ (⊤ {0ℓ})) (Q' : NetProc) → Q ─[ ev y ]─► Q'
      → Σ[ l ∈ Label (⊤ {0ℓ}) ] Σ[ t″ ∈ NetProc ] ((P ⦀ Q) ─[ l ]─► t″)
    -- P at √ (force P ≡ ret): Q solo (or joint √ if Q also at ret).
    ⦀-move-stable (√ _) P' (sRet eqP) (√ _) Q' (sRet eqQ) =
      ev (√ tt) , deadlock , sRet (fPar-rr ∅ES mtt eqP eqQ)
    ⦀-move-stable (√ _) P' (sRet eqP) (evl (evLabel X e a)) Q' stQ =
      ev (evl (evLabel X e a)) , Par ∅ES mtt P Q'
        , Par-soloR ∅ES mtt P Q (∅ES-¬mem (X , e) a) stQ
            (cong (λ n → Op.viewV n (X , e) a) eqP)
    -- P at visible event, Q at √ (force Q ≡ ret): P solo.
    ⦀-move-stable (evl (evLabel X e a)) P' stP (√ _) Q' (sRet eqQ) =
      ev (evl (evLabel X e a)) , Par ∅ES mtt P' Q
        , Par-soloL ∅ES mtt P Q (∅ES-¬mem (X , e) a) stP
            (cong (λ n → Op.viewV n (X , e) a) eqQ)
    -- both at a visible event: inspect whether Q ALSO offers P's event (X,e,a).
    ⦀-move-stable (evl (evLabel X e a)) P' stP (evl _) Q'' stQ
      with ev-inv stP | ev-inv stQ
    ... | vP , τcP , eqP , brP | vQ , τcQ , eqQ , _
        with vQ (X , e) a in vqeq
    ...   | nothing =
            ev (evl (evLabel X e a)) , Par ∅ES mtt P' Q
              , Par-soloL ∅ES mtt P Q (∅ES-¬mem (X , e) a) stP
                  (trans (cong (λ n → Op.viewV n (X , e) a) eqQ) vqeq)
    ...   | just Q' =
            ev (evl (evLabel X e a))
              , ptree (react (λ _ _ → nothing) (par-brBoth ∅ES mtt P Q P' Q'))
              , sVis {at = X , e} {a = a} (fPar-nn ∅ES mtt eqP eqQ tt₀ tt₀)
                  (par-pVis-both-eq (react vP τcP) (react vQ τcQ) P Q brP vqeq)

-- Coinductive liveness of every InterLive state (forward-declared; defined by the
-- same `copy-live′` shape — recursive calls directly under `.stepτ`/`.stepev`).
⦀-live′ : ∀ {t} → InterLive t → Live t

-- An InterLive state always has an enabled move.
inter-move : ∀ {t} → InterLive t
           → Σ[ l ∈ Label (⊤ {0ℓ}) ] Σ[ t″ ∈ NetProc ] (t ─[ l ]─► t″)
inter-move (inter P Q lP lQ) = ⦀-move lP lQ
-- the overlap node offers the τ to its first par-brBoth target (Par P′ Q).
inter-move (brB P Q P' Q' lL lR) =
  τ , Par ∅ES mtt P' Q , sTau {i = Lift 0ℓ (Fin 2) , fin} {a = lift fzero} refl refl
inter-move (emb t lt) = lt .move

-- A τ-step out of an InterLive state lands on an InterLive state.
inter-stepτ : ∀ {t t″} → InterLive t → t ─[ τ ]─► t″ → InterLive t″
inter-stepτ (inter P Q lP lQ) st with Par-τ-elim ∅ES mtt P Q st
... | τL P' stP refl = inter P' Q (lP .stepτ stP) lQ
... | τR Q' stQ refl = inter P Q' lP (lQ .stepτ stQ)
-- the overlap node's two τ's land on the already-live `Par` halves.
inter-stepτ (brB P Q P' Q' lL lR) (sSil eq) = case eq of λ ()
inter-stepτ (brB P Q P' Q' lL lR) (sTau {i = i} {a = a} eq br)
  with par-brBoth-just-inv {P} {Q} {P'} {Q'} {i} {a}
         (subst (λ f → f i a ≡ just _) (sym (proj₂ (react-injective eq))) br)
... | inj₁ refl = lL
... | inj₂ refl = lR
inter-stepτ (emb t lt) st = emb _ (lt .stepτ st)

-- A visible step out of an InterLive state lands on an InterLive state.
inter-stepev : ∀ {t} {e : Event} {t″} → InterLive t → t ─[ ev (evl e) ]─► t″ → InterLive t″
inter-stepev (inter P Q lP lQ) st with Par-ev-elim ∅ES mtt P Q st
... | evSync mem _ _   = ⊥-elim mem
... | evL  _ stP       = inter _ Q (lP .stepev stP) lQ
... | evR  _ stQ       = inter P _ lP (lQ .stepev stQ)
-- evBoth: the overlap node, whose two τ-targets are the stepped-then-paired InterLives.
... | evBoth _ stP stQ =
      brB P Q _ _ (inter _ Q (lP .stepev stP) lQ) (inter P _ lP (lQ .stepev stQ))
-- the overlap node has empty visible-offer map ⇒ no visible step.
inter-stepev (brB P Q P' Q' lL lR) (sVis {at = at} {a = a} eq br) =
  case subst (λ f → f at a ≡ just _) (sym (proj₁ (react-injective eq))) br of λ ()
inter-stepev (emb t lt) st = emb _ (lt .stepev st)

⦀-live′ il .move      = inter-move il
⦀-live′ il .stepτ  st = ⦀-live′ (inter-stepτ  il st)
⦀-live′ il .stepev st = ⦀-live′ (inter-stepev il st)

-- Binary interleaving preserves liveness.
⦀-live : ∀ {P Q : NetProc} → Live P → Live Q → Live (P ⦀ Q)
⦀-live {P} {Q} lP lQ = ⦀-live′ (inter P Q lP lQ)

-- The inline ⊓ overlap node `(P′ ⦀ Q) ⊓ (P ⦀ Q′)` is live whenever both halves are.
live-brBoth : ∀ {P Q P' Q' : NetProc}
            → Live (Par ∅ES mtt P' Q) → Live (Par ∅ES mtt P Q')
            → Live (ptree (react (λ _ _ → nothing) (par-brBoth ∅ES mtt P Q P' Q')))
live-brBoth {P} {Q} {P'} {Q'} lL lR =
  ⦀-live′ (brB P Q P' Q' (emb (Par ∅ES mtt P' Q) lL) (emb (Par ∅ES mtt P Q') lR))

------------------------------------------------------------------------
-- Fold lemmas: lift Copy liveness through replicated interleavings to
-- CopySpec, then produce Progress and the deadlock-freedom transfer.
------------------------------------------------------------------------

-- ||| over Fin n of live components is live (base ⦀Fin 0 = Skip).
interFin-live : ∀ (n : ℕ) (f : Fin n → NetProc) → (∀ i → Live (f i)) → Live (⦀Fin n f)
interFin-live zero    f h = skip-live
interFin-live (suc n) f h = ⦀-live (h fzero) (interFin-live n (λ i → f (fsuc i)) (λ i → h (fsuc i)))

-- linkCopy l = ⦀⋆ (map (λ (d,id) → Copy l d id) (linkConfig l)) is live.
linkCopy-live : ∀ l → Live (linkCopy l)
linkCopy-live l = go (linkConfig l)
  where
  go : (xs : List (Dir × IDs))
     → Live (⦀⋆ (map (λ { (dr , id) → Copy l dr id }) xs))
  go []               = skip-live
  go ((dr , id) ∷ xs) = ⦀-live (copy-live l dr id) (go xs)

-- CopySpec = ⦀Fin numLinks linkCopy is live.
network-live : Live CopySpec
network-live = interFin-live numLinks linkCopy linkCopy-live

-- CopySpec is progress: every √-free-reachable state has a next move.
network-progress : Progress CopySpec
network-progress = Live⇒Progress network-live

-- Deadlock-freedom of Network from ANY Network ≈DR CopySpec (generic in p).
network-deadlockFree-fromBisim : Network ≈DR CopySpec → DeadlockFree Network
network-deadlockFree-fromBisim bisim = drbisim-deadlockFree bisim network-progress
