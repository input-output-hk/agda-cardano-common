{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- LeiosNotify (cardano-blueprint table, no pipelining): FAIRNESS-CONDITIONAL QUIT
-- LIVENESS of the real pair, in the csp-ptree LTL library's run semantics, with no fixed
-- server or client policy.
--
-- RUNS.  A run is the library's `Trace Rr t` (`Semantics.LTL.Traces_Based`): a MAXIMAL
-- weak run — weak visible steps (τ* e τ*), ending only in a `done` leaf (returned), a
-- `stuck` leaf (no move at all) or a `div` leaf (τ forever); otherwise infinite.
-- Temporal operators are the library's (`◇ᵗ`, `□ᵗ`, `drop`, `atom`, `Fires`, `WEnabled`).
-- The goal is `◇ᵗ (atom Ended)`: a √ step or a returned leaf is eventually observed.
--
-- THE ENVIRONMENT.  The api / done events are offered by the two applications.  The
-- peers' OUTPUTS (deliveries, the server's `doneLNP`) are always accepted; the
-- applications' COMMANDS — the client's `lnpSendRequestNext` / `lnpSendDone`, the server's
-- five `lnpSend*` — may be WITHHELD.  An environment is an event set `X` of commands it
-- never offers (`CmdOnly X`), and the runs of the pair in it are the runs of
--     envP X = sys [| X |] Skip
-- (`X = ∅ES`: the always-willing environment; `X = srvApi`: `blk`, the server's
-- application never sends; `Skip` refuses everything in `X` and lets the rest through).
-- `sys` itself is the closed world (every api / done event always offered).
--
-- THE ASSUMPTIONS, on a run `tr` of `envP X`:
--   (F1) `F1 tr`: the client eventually stops requesting — ◇□ ¬(RequestNext fires).
--   (F2) `PFair X QuitC tr`: WEAK FAIRNESS of the quit command.
--   (F3) `PFair X SrvSend tr`: WEAK FAIRNESS of the server's sends (its five api sends and
--        the reply messages on the wire: any notification or MsgCanceled).
-- `PFair X C` is the library's `Fair C` with ENABLEDNESS READ IN THE PAIR: "if, from some
-- point on, the pair continuously offers an event of `C`, an event of `C` eventually
-- fires".  The library's `Fair` reads enabledness in the run's own process; for `envP X`
-- that is enabledness AFTER the environment's refusal, so an application that withholds
-- a command forever would satisfy it vacuously.  Reading it in the pair (`PEn`: the
-- tree is `Par⊤ X t₁ Skip` with `C` weakly enabled in `t₁`) makes F2 / F3 constrain
-- exactly the applications' commands.
--
-- THE RESULTS (∀ `Params`, ∀ link `l`):
--   MAIN `quit-live`: for every command-only `X`, every run of `envP X` satisfying F1, F2
--       and F3 reaches √.  Derived from `LeiosNotifyQuitCancel`: the rank `rk true`
--       (bound 8) strictly drops at every visible step without RequestNext (`kstep`), so
--       after F1's point there are at most 8 more visible steps; `div` is impossible (the
--       pair's τ-measure); a `stuck` leaf is the pair idle (quit enabled, never taken: F2
--       violated) or busy (a send enabled, never taken: F3 violated).
--   CLOSED WORLD `quit-live-sys`: every run of `sys` satisfying F1 alone reaches √.  With
--       every command offered, a maximal run cannot stay idle or busy (the pair is
--       deadlock-free), so F2 and F3 are not needed there.
--   NECESSITY (each with a concrete run that never reaches √):
--     `nf3` (F1, F2 hold, F3 fails): in `blk` the client commands and sends RequestNext,
--         then the run is stuck forever with the server busy (the stall of `blk-stall`).
--     `nf2` (F1, F3 hold, F2 fails): in the environment withholding the client's two
--         commands (`cliCmd`), the run is stuck at the start, the client idle forever.
--     `nf1` (F2, F3 hold, F1 fails): in the always-willing environment the client
--         requests forever and the server always answers (here: cancels); the infinite run
--         never quits.  F2 holds there because quit is not continuously enabled (the
--         client is busy half of the time) — weak fairness cannot force the quit.
------------------------------------------------------------------------

open import Cardano_network.Params using (Params)

module Cardano_network.Parametric.Leios.LeiosNotifyQuitLive (p : Params) where

open import Level using (Level; _⊔_; Lift; lift; lower) renaming (zero to lzero; suc to lsuc)
open import Data.Bool using (Bool; true; false; T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_)
open import Data.Nat.Properties using (≤-refl; <-≤-trans; ≤-pred; ≤ᵇ⇒≤; +-comm)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Data.Unit as U
open import Data.Unit.Polymorphic using (tt)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable.Core using (T?)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import Process_Trees hiding (div)
open import Cardano_network.Base
open import Cardano_network.Net p
open import Cardano_network.Data p
open import Cardano_network.LeiosNotifyP p
open import Cardano_network.Parametric.Leios.LeiosNotifyQuit p
open import Cardano_network.Parametric.Leios.LeiosNotifyQuitCancel p using (noRN; rk; kstep)

open import CSP.Operators LNPEv-≟ using (Par⊤; Skip; EventSet; ∅ES)
open EventSet
open import Semantics.LTS {E = LNPEv} {I = ExtI LNPEv}
open import Semantics.Deadlock {E = LNPEv} {I = ExtI LNPEv}
  using (IsStuck; _⟹∖√⟨_⟩_; ∖√-refl; ∖√-τ; ∖√-ev)
open import Semantics.WeakBisim {E = LNPEv} {I = ExtI LNPEv}
  using (_═[_]═►_; wev; _─[τ*]─►_; τ*-refl; τ*-step)
open import Semantics.LTL.Traces_Based {E = LNPEv} {I = ExtI LNPEv}
  using ( Trace; ∞Trace; step; done; stuck; div; frameOf; frameState; tail; drop; dropIdx
        ; FramePred; LTLᵗ; atom; ⟦_⟧; ◇ᵗ; ◇ᵗ-now; ◇ᵗ-later; □ᵗ; □ᵗ-now; □ᵗ-tail )
  renaming (¬_ to ¬ᵗ_)
open import Semantics.LTL.Fairness {E = LNPEv} {I = ExtI LNPEv} using (WEnabled; Fires)
open import CSP.Laws.Traces.TraceLawsParallel LNPEv-≟ using (Par-τ-L; Par-soloL)

------------------------------------------------------------------------
-- §0  Generic helpers on runs and weak steps (no Leios content)
------------------------------------------------------------------------

-- a τ-run, prefixed to a √-free run
τ*∖√ : ∀ {t u u′ : Tree} {s} → t ─[τ*]─► u → u ⟹∖√⟨ s ⟩ u′ → t ⟹∖√⟨ s ⟩ u′
τ*∖√ τ*-refl        r = r
τ*∖√ (τ*-step x xs) r = ∖√-τ x (τ*∖√ xs r)

-- a weak visible step, as a √-free run of one event
w2r : ∀ {t t′ : Tree} {e} → t ═[ ev (evl e) ]═► t′ → t ⟹∖√⟨ e ∷ [] ⟩ t′
w2r (wev a st b) = τ*∖√ a (∖√-ev st (τ*∖√ b ∖√-refl))

-- a √-free run with no visible event is a τ-run
r2τ : ∀ {t t′ : Tree} → t ⟹∖√⟨ [] ⟩ t′ → t ─[τ*]─► t′
r2τ ∖√-refl    = τ*-refl
r2τ (∖√-τ x r) = τ*-step x (r2τ r)

-- a √-free run of one event, as a weak visible step
r2w : ∀ {t t′ : Tree} {e} → t ⟹∖√⟨ e ∷ [] ⟩ t′ → t ═[ ev (evl e) ]═► t′
r2w (∖√-τ x r) with r2w r
... | wev a st b = wev (τ*-step x a) st b
r2w (∖√-ev st r) = wev τ*-refl st (r2τ r)

-- a weak step cannot start at a stuck tree
firstStep : ∀ {u u′ : Tree} {e} → u ═[ ev e ]═► u′ → IsStuck u → ⊥
firstStep (wev τ*-refl st _)      stk = stk st
firstStep (wev (τ*-step x _) _ _) stk = stk x

-- every suffix of a stuck leaf observes that leaf's tree
stkFS : ∀ k {t : Tree} {stk : IsStuck t} → frameState (frameOf (drop k (stuck stk))) ≡ t
stkFS zero    = refl
stkFS (suc k) = stkFS k

-- an atom false at stuck frames is never reached from a stuck leaf
noAt◇ : ∀ {ℓa} {P : FramePred ℓa Rr} → (∀ {t} → P (stuck t) → ⊥)
      → ∀ {t : Tree} {stk : IsStuck t} → ◇ᵗ (atom P) (stuck stk) → ⊥
noAt◇ nP (◇ᵗ-now h)   = nP h
noAt◇ nP (◇ᵗ-later h) = noAt◇ nP h

-- a formula true at a stuck leaf holds there forever
□stk : ∀ {ℓa} {φ : LTLᵗ ℓa Rr} {t : Tree} {stk : IsStuck t} → ⟦ φ ⟧ (stuck stk) → □ᵗ φ (stuck stk)
□stk h .□ᵗ-now  = h
□stk h .□ᵗ-tail = □stk h

-- what a suffix eventually reaches, the run eventually reaches
◇drop : ∀ {ℓa} {φ : LTLᵗ ℓa Rr} n {t : Tree} (tr : Trace Rr t) → ◇ᵗ φ (drop n tr) → ◇ᵗ φ tr
◇drop zero    _  h = h
◇drop (suc n) tr h = ◇ᵗ-later (◇drop n (tail tr) h)

-- SUCCESSFUL TERMINATION observed at a frame: a √ step, or a returned leaf
Ended : FramePred lzero Rr
Ended (step _ (√ _)) = U.⊤
Ended (done _ _)     = U.⊤
Ended _              = ⊥

-- whether a payload is a server reply: a notification or MsgCanceled
replyP : Payload → Bool
replyP (_ , _ , _ , leiosNotifyP (MsgLNPBlockAnnouncement _)) = true
replyP (_ , _ , _ , leiosNotifyP (MsgLNPBlockOffer _ _))      = true
replyP (_ , _ , _ , leiosNotifyP (MsgLNPBlockTxsOffer _))     = true
replyP (_ , _ , _ , leiosNotifyP (MsgLNPVotes _))             = true
replyP (_ , _ , _ , leiosNotifyP MsgLNPCanceled)              = true
replyP _                                                      = false

-- the client's two api commands: RequestNext and the quit
cliTag : ApiLPTag → Bool
cliTag lnpSendRequestNext = true
cliTag lnpSendDone        = true
cliTag _                  = false

-- whether an event is one of the client's (direction `lo`) api commands
cliEv : ∀ {A} → LNPEv A → Bool
cliEv (apiLPev _ lo m) = cliTag m
cliEv _                = false

-- the client's commands, as an event set (withheld in `nf2`)
cliCmd : EventSet
cliCmd = record { mem = λ at _ → T (cliEv (proj₂ at)) ; dec = λ at _ → T? (cliEv (proj₂ at)) }

------------------------------------------------------------------------
-- everything below is for one link `l`
------------------------------------------------------------------------

module _ (l : Link) where

  -- this link's abstract labels, read as events
  ⌞_⌟ : Lab l → Event
  ⌞_⌟ = ⌜_⌝ l

  ------------------------------------------------------------------------
  -- §1  Event classes, environments, the assumptions
  ------------------------------------------------------------------------

  -- the client's RequestNext api command (the events of `noRN`)
  RNc : Event → Set
  RNc = InEv l (noRN l)

  -- the client's quit command `lnpSendDone`
  QuitC : Event → Set₁
  QuitC = QuitApi l

  -- whether an event is a server send: one of its five api sends, or a reply on the wire
  srvSendEv : ∀ {A} → LNPEv A → A → Bool
  srvSendEv (apiLPev _ hi m)  _ = srvCmd l m
  srvSendEv (receiveLNP _ lo) x = replyP x
  srvSendEv _                 _ = false

  -- the server's sends, as an event class
  SrvSend : Event → Set
  SrvSend e = T (srvSendEv (Event.e e) (Event.a e))

  -- the applications' COMMANDS, as labels: the client's two, the server's five
  cmdL : Lab l → Bool
  cmdL (ap lo m _) = cliTag m
  cmdL (ap hi m _) = srvCmd l m
  cmdL _           = false

  -- an environment that withholds only commands (never a wire event, delivery or done)
  CmdOnly : EventSet → Set
  CmdOnly X = ∀ ω → InE l X ω → T (cmdL ω)

  -- THE PAIR IN AN ENVIRONMENT that never offers the events of `X`
  envP : EventSet → Tree
  envP X = Par⊤ X (sys l) Skip

  -- `C` is ENABLED IN THE PAIR at a state of `envP X` (the environment may still withhold it)
  PEn : ∀ {ℓc} → EventSet → (Event → Set ℓc) → Tree → Set (lsuc lzero ⊔ ℓc)
  PEn X C t = Σ[ t₁ ∈ Tree ] (t ≡ Par⊤ X t₁ Skip × WEnabled C t₁)

  -- WEAK FAIRNESS of `C` relative to the pair: the library's `Fair C`, with enabledness
  -- read in the pair — if from point `n` on `C` stays enabled in the pair, `C` fires
  PFair : ∀ {ℓc} → EventSet → (Event → Set ℓc) → ∀ {t} → Trace Rr t → Set (lsuc lzero ⊔ ℓc)
  PFair X C tr = ∀ n → (∀ k → PEn X C (frameState (frameOf (drop (n + k) tr))))
               → ◇ᵗ (atom (Fires C)) (drop n tr)

  -- (F1) THE CLIENT EVENTUALLY STOPS REQUESTING: ◇□ ¬(RequestNext fires)
  F1 : ∀ {t} → Trace Rr t → Set₁
  F1 tr = Σ[ n ∈ ℕ ] □ᵗ (¬ᵗ (atom (Fires RNc))) (drop n tr)

  ------------------------------------------------------------------------
  -- §2  The abstraction of `envP X`
  ------------------------------------------------------------------------

  -- the pair, synchronised with `Skip` on `X`
  module PX (X : EventSet) = Prod l (SysA l) (SkA l) X (λ {ω} → disjSk l {X} {ω})

  -- the abstraction of `envP X`
  EnvA : EventSet → Abs l (SysS l × U.⊤)
  EnvA X = PX.ParA X

  -- (intro)
  EnvI : ∀ X → AbsI l (EnvA X)
  EnvI X = PX.ParI X (SysI l) (SkI l)

  -- `envP X` starts at the initial state
  env₀ : ∀ X → Abs.Pos (EnvA X) (σ₀ l , U.tt) (envP X)
  env₀ X = _ , _ , refl , sys₀ l , refl

  -- a step of `envP X` is a step of the pair
  unX : ∀ X {σ u ℓ σ′ u′} → Abs.Stp (EnvA X) (σ , u) ℓ (σ′ , u′) → Abs.Stp (SysA l) σ ℓ σ′
  unX _ (PX.pτL a)   = a
  unX _ (PX.psL _ a) = a
  unX _ (PX.pτR ())
  unX _ (PX.psy _ _ ())
  unX _ (PX.psR _ ())

  -- a weak step of the pair, off `X`, is one of its composite with `Skip`
  liftW : ∀ X {t₁ t′ : Tree} {e} → ¬ InEv l X e → t₁ ═[ ev (evl e) ]═► t′
        → Par⊤ X t₁ Skip ═[ ev (evl e) ]═► Par⊤ X t′ Skip
  liftW X ¬m (wev a st b) = wev (lτ a) (Par-soloL X (λ _ _ → tt) _ Skip ¬m st refl) (lτ b)
    where
    -- (its τ-runs)
    lτ : ∀ {u u′ : Tree} → u ─[τ*]─► u′ → Par⊤ X u Skip ─[τ*]─► Par⊤ X u′ Skip
    lτ τ*-refl        = τ*-refl
    lτ (τ*-step x xs) = τ*-step (Par-τ-L X (λ _ _ → tt) _ Skip x) (lτ xs)

  ------------------------------------------------------------------------
  -- §3  The descent, generic in the system and in what is known at a stuck leaf
  ------------------------------------------------------------------------

  -- a system abstracted by `A` (projecting to the pair by `π`), and a suffix-closed
  -- context `Ctx` (the fairness assumptions) that refutes stuck leaves
  module Live {S : Set} (A : Abs l S) (π : S → SysS l)
              (un : ∀ {σ ℓ σ′} → Abs.Stp A σ ℓ σ′ → Abs.Stp (SysA l) (π σ) ℓ (π σ′))
              {ℓx : Level} (Ctx : ∀ {t} → Trace Rr t → Set ℓx)
              (ctxT : ∀ {t} {tr : Trace Rr t} → Ctx tr → Ctx (tail tr))
              (hStk : ∀ {σ t} (stk : IsStuck t) → Abs.Pos A σ t → JJ l (π σ) → Ctx (stuck stk) → ⊥) where
    open Gen l A using (ARun; r0; rτ; rE; runE; noDiv)

    -- the invariant `J` along runs (reused)
    module W = Walk l A π un

    -- a τ-only run keeps the invariant and the rank
    kτ : ∀ {σ σ′} → ARun σ [] σ′ → (j : JJ l (π σ)) → Σ[ j′ ∈ JJ l (π σ′) ] rk l true j′ ≡ rk l true j
    kτ r0        j = j , refl
    kτ (rτ a ar) j with kstep l true j (un a) U.tt U.tt
    ... | j₁ , eq with kτ ar j₁
    ...   | j′ , eq′ = j′ , trans eq′ eq

    -- a one-event run whose event is not RequestNext strictly lowers the rank
    k1 : ∀ {σ e σ′} → ARun σ (e ∷ []) σ′ → ¬ InEv l (noRN l) e → (j : JJ l (π σ))
       → Σ[ j′ ∈ JJ l (π σ′) ] rk l true j′ < rk l true j
    k1 (rτ a ar) nr j with kstep l true j (un a) U.tt U.tt
    ... | j₁ , eq with k1 ar nr j₁
    ...   | j′ , lt = j′ , subst (rk l true j′ <_) eq lt
    k1 (rE a ar) nr j with kstep l true j (un a) U.tt nr
    ... | j₁ , d with kτ ar j₁
    ...   | j′ , eq = j′ , subst (_< rk l true j) (sym eq) (≤ᵇ⇒≤ (suc (rk l true j₁)) (rk l true j) d)

    -- the state after `n` frames is positioned and satisfies `J`, unless √ came first
    posAt : ∀ n {σ t} (tr : Trace Rr t) → Abs.Pos A σ t → JJ l (π σ)
          → ◇ᵗ (atom Ended) tr ⊎ Σ[ σ′ ∈ S ] (Abs.Pos A σ′ (dropIdx n tr) × JJ l (π σ′))
    posAt zero    _                        p j = inj₂ (_ , p , j)
    posAt (suc n) (step {e = √ _} _ _)     _ _ = inj₁ (◇ᵗ-now U.tt)
    posAt (suc n) (step {e = evl _} w tr′) p j with runE p (w2r w)
    ... | _ , ar , p′ with posAt n (∞Trace.force tr′) p′ (proj₁ (W.walk ar j))
    ...   | inj₁ h = inj₁ (◇ᵗ-later h)
    ...   | inj₂ q = inj₂ q
    posAt (suc n) (done _)  _ _ = inj₁ (◇ᵗ-now U.tt)
    posAt (suc n) (stuck s) p j = posAt n (stuck s) p j
    posAt (suc n) (div d)   p j = posAt n (div d) p j

    -- THE DESCENT: with RequestNext never firing, every visible step lowers the rank, a
    -- `div` leaf is impossible, a `stuck` leaf is refuted by the context; so √ comes
    desc : ∀ n {σ t} (tr : Trace Rr t) → Abs.Pos A σ t → (j : JJ l (π σ)) → rk l true j < n
         → □ᵗ (¬ᵗ (atom (Fires RNc))) tr → Ctx tr → ◇ᵗ (atom Ended) tr
    desc zero    _ _ _ () _ _
    desc (suc n) (step {e = √ _} _ _)     _ _ _  _  _  = ◇ᵗ-now U.tt
    desc (suc n) (step {e = evl _} w tr′) p j lt nr cx with runE p (w2r w)
    ... | _ , ar , p′ with k1 ar (λ m → lower (□ᵗ-now nr m)) j
    ...   | j′ , lt′ = ◇ᵗ-later (desc n (∞Trace.force tr′) p′ j′ (<-≤-trans lt′ (≤-pred lt))
                                      (□ᵗ-tail nr) (ctxT cx))
    desc (suc n) (done _)  _ _ _ _ _  = ◇ᵗ-now U.tt
    desc (suc n) (stuck s) p j _ _ cx = ⊥-elim (hStk s p j cx)
    desc (suc n) (div d)   p _ _ _ _  = ⊥-elim (noDiv p d)

    -- the context along a suffix
    ctxD : ∀ n {t} {tr : Trace Rr t} → Ctx tr → Ctx (drop n tr)
    ctxD zero    c = c
    ctxD (suc n) c = ctxD n (ctxT c)

    -- LIVENESS from a positioned state: F1 and the context give √
    live : ∀ {σ t} (tr : Trace Rr t) → Abs.Pos A σ t → JJ l (π σ) → F1 tr → Ctx tr → ◇ᵗ (atom Ended) tr
    live tr p j (n , nr) cx with posAt n tr p j
    ... | inj₁ h             = h
    ... | inj₂ (_ , p′ , j′) =
      ◇drop n tr (desc (suc (rk l true j′)) (drop n tr) p′ j′ ≤-refl nr (ctxD n cx))

  ------------------------------------------------------------------------
  -- §4  The theorems
  ------------------------------------------------------------------------

  -- in the closed world a stuck leaf is impossible: the pair is deadlock-free
  sysStuck : ∀ {σ t} (stk : IsStuck t) → Abs.Pos (SysA l) σ t → JJ l σ → U.⊤ → ⊥
  sysStuck stk p j _ = GenI.notStuck l (SysI l) p (progS l j p) stk

  -- the descent over `sys` (no context needed)
  module LS = Live (SysA l) (λ σ → σ) (λ a → a) (λ _ → U.⊤) (λ _ → U.tt) sysStuck

  -- CLOSED WORLD: every run of `sys` in which the client eventually stops requesting
  -- reaches √ (every command always offered: no fairness needed)
  quit-live-sys : (tr : Trace Rr (sys l)) → F1 tr → ◇ᵗ (atom Ended) tr
  quit-live-sys tr f1 = LS.live tr (sys₀ l) j1 f1 U.tt

  -- a τ of the pair is one of `envP X`, so a stuck `envP X` has none
  noT : ∀ X {σ σ′ t} → Abs.Pos (EnvA X) (σ , U.tt) t → IsStuck t → Abs.Stp (SysA l) σ τ′ σ′ → ⊥
  noT X pp stk a = stk (proj₁ (proj₂ (AbsI.introτ (EnvI X) pp (PX.pτL a))))

  -- a visible step of the pair off `X` is one of `envP X`, so a stuck `envP X` has none
  noE : ∀ X {σ σ′ t ω} → Abs.Pos (EnvA X) (σ , U.tt) t → IsStuck t → ¬ InE l X ω
      → Abs.Stp (SysA l) σ (ev′ ω) σ′ → ⊥
  noE X pp stk m a = stk (proj₁ (proj₂ (AbsI.introE (EnvI X) pp (PX.psL m a))))

  -- … in particular a step on a non-command label, when `X` withholds only commands
  noE′ : ∀ X → CmdOnly X → ∀ {σ σ′ t ω} → Abs.Pos (EnvA X) (σ , U.tt) t → IsStuck t
       → Abs.Stp (SysA l) σ (ev′ ω) σ′ → ¬ T (cmdL ω) → ⊥
  noE′ X cx {ω = ω} pp stk a nc = noE X pp stk (λ m → nc (cx ω m)) a

  -- a visible step of the pair on an event of `C` makes `C` enabled in the pair
  en : ∀ X {ℓc} {C : Event → Set ℓc} {σ σ′ t ω} → Abs.Pos (EnvA X) (σ , U.tt) t
     → Abs.Stp (SysA l) σ (ev′ ω) σ′ → C ⌞ ω ⌟ → PEn X C t
  en X (t₁ , _ , refl , p₁ , refl) a c =
    t₁ , refl , _ , _ , wev τ*-refl (proj₁ (proj₂ (AbsI.introE (SysI l) p₁ a))) τ*-refl , c

  -- a stuck `envP X` with no loop-back pending: the pair is idle (quit enabled in it) or
  -- busy (the cancel enabled in it); every other phase has a non-command step
  stuckJ : ∀ X → CmdOnly X → ∀ {c s t} → Abs.Pos (EnvA X) (((c , false) , (s , false)) , U.tt) t
         → J l c s → IsStuck t → PEn X QuitC t ⊎ PEn X SrvSend t
  stuckJ X _  pp j1 _ = inj₁ (en X pp (P1.psL (λ ()) (cQi U.tt)) refl)
  stuckJ X cx pp j2 stk = ⊥-elim (noE′ X cx pp stk (P1.psy U.tt cSR sRN) (λ ()))
  stuckJ X _  pp j3 _ = inj₂ (en X pp (P1.psR (λ ()) (sAC U.tt)) U.tt)
  stuckJ X cx pp (j4 (rA h))      stk = ⊥-elim (noE′ X cx pp stk (P1.psy U.tt (cRA h) (sNA h)) (λ ()))
  stuckJ X cx pp (j4 (rO q sz))   stk = ⊥-elim (noE′ X cx pp stk (P1.psy U.tt (cRO q sz) (sNO q sz)) (λ ()))
  stuckJ X cx pp (j4 (rT q))      stk = ⊥-elim (noE′ X cx pp stk (P1.psy U.tt (cRT q) (sNT q)) (λ ()))
  stuckJ X cx pp (j4 (rV vs))     stk = ⊥-elim (noE′ X cx pp stk (P1.psy U.tt (cRV vs) (sNV vs)) (λ ()))
  stuckJ X cx pp (j4 rC)          stk = ⊥-elim (noE′ X cx pp stk (P1.psy U.tt cRC sNC) (λ ()))
  stuckJ X cx pp (j5 (dAnn h))    stk = ⊥-elim (noE′ X cx pp stk (P1.psL (λ ()) (cDA h)) (λ ()))
  stuckJ X cx pp (j5 (dOff q sz)) stk = ⊥-elim (noE′ X cx pp stk (P1.psL (λ ()) (cDO q sz)) (λ ()))
  stuckJ X cx pp (j5 (dTxs q))    stk = ⊥-elim (noE′ X cx pp stk (P1.psL (λ ()) (cDT q)) (λ ()))
  stuckJ X cx pp (j5 (dVot vs))   stk = ⊥-elim (noE′ X cx pp stk (P1.psL (λ ()) (cDV vs)) (λ ()))
  stuckJ X cx pp q1 stk = ⊥-elim (noE′ X cx pp stk (P1.psy U.tt cSQ sQi) (λ ()))
  stuckJ X cx pp q2 stk = ⊥-elim (noE′ X cx pp stk (P1.psR (λ ()) sDn) (λ ()))
  stuckJ X cx pp q3 stk = ⊥-elim (noE′ X cx pp stk (P1.psy U.tt cDn sDS) (λ ()))
  stuckJ X _  pp q4 stk = ⊥-elim (stk (sRet (AbsI.introR (EnvI X) pp ((U.tt , U.tt) , U.tt))))

  -- at a stuck `envP X` the pair is idle with quit enabled, or busy with a send enabled
  stuckEn : ∀ X → CmdOnly X → ∀ {σ t} → Abs.Pos (EnvA X) (σ , U.tt) t → JJ l σ → IsStuck t
          → PEn X QuitC t ⊎ PEn X SrvSend t
  stuckEn X cx pp@(_ , _ , _ , (_ , _ , _ , pc , (_ , _ , ps)) , _) j stk with cτ? l pc | sτ? l ps
  ... | inj₂ (_ , a) | _            = ⊥-elim (noT X pp stk (P1.pτL a))
  ... | inj₁ refl    | inj₂ (_ , a) = ⊥-elim (noT X pp stk (P1.pτR a))
  ... | inj₁ refl    | inj₁ refl    = stuckJ X cx pp j stk

  -- F2 and F3 together: the context the descent carries in `envP X`
  FX : EventSet → ∀ {t} → Trace Rr t → Set₁
  FX X tr = PFair X QuitC tr × PFair X SrvSend tr

  -- … which passes to the tail
  ctxFX : ∀ X {t} {tr : Trace Rr t} → FX X tr → FX X (tail tr)
  ctxFX X (f2 , f3) = (λ n → f2 (suc n)) , (λ n → f3 (suc n))

  -- a stuck leaf of `envP X` contradicts F2 (idle: quit enabled forever, never fires) or
  -- F3 (busy: a send enabled forever, never fires)
  envStuck : ∀ X → CmdOnly X → ∀ {σ t} (stk : IsStuck t) → Abs.Pos (EnvA X) σ t → JJ l (proj₁ σ)
           → FX X (stuck stk) → ⊥
  envStuck X cx stk pp j (f2 , f3) with stuckEn X cx pp j stk
  ... | inj₁ q = noAt◇ (λ { (lift ()) }) (f2 0 (λ k → subst (PEn X QuitC) (sym (stkFS k)) q))
  ... | inj₂ s = noAt◇ (λ { (lift ()) }) (f3 0 (λ k → subst (PEn X SrvSend) (sym (stkFS k)) s))

  -- the descent over `envP X`, carrying F2 and F3
  module LE (X : EventSet) (cx : CmdOnly X) =
    Live (EnvA X) proj₁ (unX X) (FX X) (ctxFX X) (envStuck X cx)

  -- MAIN.  In every environment that withholds only commands, every run of the pair in
  -- which (F1) the client eventually stops requesting, (F2) the quit command is taken
  -- if the pair keeps offering it, and (F3) the server sends if the pair keeps offering a
  -- send, REACHES SUCCESSFUL TERMINATION (√).  No server or client policy is fixed: the
  -- server may answer with any notification or cancel, the client may request any
  -- finite number of times
  quit-live : ∀ X → CmdOnly X → (tr : Trace Rr (envP X))
            → F1 tr → PFair X QuitC tr → PFair X SrvSend tr → ◇ᵗ (atom Ended) tr
  quit-live X cx tr f1 f2 f3 = LE.live X cx tr (env₀ X) j1 f1 (f2 , f3)

  ------------------------------------------------------------------------
  -- §5  Necessity: the shared pieces
  ------------------------------------------------------------------------

  -- a class whose events lie off `X` is not enabled in the pair at a stuck `envP X`
  cenStk : ∀ X {ℓc} {C : Event → Set ℓc} {t} → (∀ {e} → C e → ¬ InEv l X e) → IsStuck t
         → PEn X C t → ⊥
  cenStk X off stk (_ , refl , _ , _ , w , c) = firstStep (liftW X (off c) w) stk

  -- the joint states the counterexamples visit: idle, RequestNext commanded, busy, cancelling
  σI σR σB σC : SysS l × U.⊤
  σI = σ₀ l , U.tt
  σR = ((cR , false) , (sI , false)) , U.tt
  σB = ((cB , false) , (sB , false)) , U.tt
  σC = ((cB , false) , (sN rC , false)) , U.tt

  -- the client commands RequestNext
  aRN : ∀ X → ¬ InE l X (ap lo lnpSendRequestNext U.tt)
      → Gen.ARun l (EnvA X) σI (⌞ ap lo lnpSendRequestNext U.tt ⌟ ∷ []) σR
  aRN X m = rE (PX.psL m (P1.psL (λ ()) (cRN U.tt))) r0
    where open Gen l (EnvA X) using (rE; r0)

  -- MsgRequestNext on the wire, then both loop-backs
  aWR : ∀ X → ¬ InE l X (wS lo (pay l FromInitiator MsgLNPRequestNext))
      → Gen.ARun l (EnvA X) σR (⌞ wS lo (pay l FromInitiator MsgLNPRequestNext) ⌟ ∷ []) σB
  aWR X m = rE (PX.psL m (P1.psy U.tt cSR sRN)) (rτ (PX.pτL (P1.pτL cτB)) (rτ (PX.pτL (P1.pτR sτB)) r0))
    where open Gen l (EnvA X) using (rE; rτ; r0)

  -- the server's application commands the cancel
  aSC : ∀ X → ¬ InE l X (ap hi lnpSendCanceled U.tt)
      → Gen.ARun l (EnvA X) σB (⌞ ap hi lnpSendCanceled U.tt ⌟ ∷ []) σC
  aSC X m = rE (PX.psL m (P1.psR (λ ()) (sAC U.tt))) r0
    where open Gen l (EnvA X) using (rE; r0)

  -- MsgCanceled on the wire, then both loop-backs
  aWC : ∀ X → ¬ InE l X (wR lo (pay l FromResponder MsgLNPCanceled))
      → Gen.ARun l (EnvA X) σC (⌞ wR lo (pay l FromResponder MsgLNPCanceled) ⌟ ∷ []) σI
  aWC X m = rE (PX.psL m (P1.psy U.tt cRC sNC)) (rτ (PX.pτL (P1.pτL cτI)) (rτ (PX.pτL (P1.pτR sτI)) r0))
    where open Gen l (EnvA X) using (rE; rτ; r0)

  -- the concrete weak step and successor position of a one-event abstract run
  stepI : ∀ {S} {A : Abs l S} (I : AbsI l A) {σ σ′ t e} → Gen.ARun l A σ (e ∷ []) σ′ → Abs.Pos A σ t
        → Σ[ t′ ∈ Tree ] (t ═[ ev (evl e) ]═► t′ × Abs.Pos A σ′ t′)
  stepI I ar p = proj₁ (GenI.runI l I ar p) , r2w (proj₁ (proj₂ (GenI.runI l I ar p)))
               , proj₂ (proj₂ (GenI.runI l I ar p))

  ------------------------------------------------------------------------
  -- §6  (N-F3) The server never sends: `blk`
  ------------------------------------------------------------------------

  -- `blk` withholds only commands
  cmdSrv : CmdOnly (srvApi l)
  cmdSrv (ap hi _ _) c = c
  cmdSrv (ap lo _ _) ()
  cmdSrv (wS _ _)    ()
  cmdSrv (wR _ _)    ()
  cmdSrv (dn _)      ()

  -- the quit command is not a server send
  qNotSrv : ∀ {e} → QuitC e → ¬ InEv l (srvApi l) e
  qNotSrv refl ()

  -- the stall's first step: RequestNext commanded
  b1 : ∀ {t} → Abs.Pos (EnvA (srvApi l)) σI t
     → Σ[ t′ ∈ Tree ] (t ═[ ev (evl ⌞ ap lo lnpSendRequestNext U.tt ⌟) ]═► t′ × Abs.Pos (EnvA (srvApi l)) σR t′)
  b1 = stepI (EnvI (srvApi l)) (aRN (srvApi l) (λ ()))

  -- … its second: MsgRequestNext sent, both peers busy
  b2 : ∀ {t} → Abs.Pos (EnvA (srvApi l)) σR t
     → Σ[ t′ ∈ Tree ] (t ═[ ev (evl ⌞ wS lo (pay l FromInitiator MsgLNPRequestNext) ⌟) ]═► t′
                       × Abs.Pos (EnvA (srvApi l)) σB t′)
  b2 = stepI (EnvI (srvApi l)) (aWR (srvApi l) (λ ()))

  -- the state after the first step
  tB1 : Tree
  tB1 = proj₁ (b1 (env₀ (srvApi l)))

  -- (its position)
  pB1 : Abs.Pos (EnvA (srvApi l)) σR tB1
  pB1 = proj₂ (proj₂ (b1 (env₀ (srvApi l))))

  -- the stall state
  tB2 : Tree
  tB2 = proj₁ (b2 pB1)

  -- (its position)
  pB2 : Abs.Pos (EnvA (srvApi l)) σB tB2
  pB2 = proj₂ (proj₂ (b2 pB1))

  -- the stall state is stuck (`noStepX` of `LeiosNotifyQuit`: `blk`'s abstraction is `EnvA srvApi`)
  stkB : IsStuck tB2
  stkB = Gen.stuckE l (EnvA (srvApi l)) pB2 (noStepX l) (λ { ((() , _) , _) })

  -- THE STALL RUN of `blk`: RequestNext commanded, sent, then stuck forever (forward
  -- declarations: the run and its two delayed tails)
  stall : Trace Rr (blk l)
  -- (after the first step)
  ∞stall₁ : ∞Trace Rr tB1
  -- (after the second step)
  ∞stall₂ : ∞Trace Rr tB2

  stall = step (proj₁ (proj₂ (b1 (env₀ (srvApi l))))) ∞stall₁
  ∞stall₁ .∞Trace.force = step (proj₁ (proj₂ (b2 pB1))) ∞stall₂
  ∞stall₂ .∞Trace.force = stuck stkB

  -- from the second frame on, RequestNext never fires
  □B : □ᵗ (¬ᵗ (atom (Fires RNc))) (∞Trace.force ∞stall₁)
  □B .□ᵗ-now  ()
  □B .□ᵗ-tail = □stk (λ x → x)

  -- every frame from the third on observes the stall state
  fsB : ∀ n → frameState (frameOf (drop (n + 2) stall)) ≡ tB2
  fsB n = subst (λ m → frameState (frameOf (drop m stall)) ≡ tB2) (+-comm 2 n) (stkFS n)

  -- at the stall state the server's cancel is enabled in the pair
  srvB : PEn (srvApi l) SrvSend tB2
  srvB = en (srvApi l) pB2 (P1.psR (λ ()) (sAC U.tt)) U.tt

  -- the stall run never reaches √
  noEndB : ◇ᵗ (atom Ended) stall → ⊥
  noEndB (◇ᵗ-now ())
  noEndB (◇ᵗ-later (◇ᵗ-now ()))
  noEndB (◇ᵗ-later (◇ᵗ-later h)) = noAt◇ (λ ()) h

  -- quit is never continuously enabled in the stall run: not at the stall state
  f2B : PFair (srvApi l) QuitC stall
  f2B n h = ⊥-elim (cenStk (srvApi l) {C = QuitC} (λ {e} → qNotSrv {e}) stkB (subst (PEn (srvApi l) QuitC) (fsB n) (h 2)))

  -- the cancel is enabled in the pair forever from the third frame, and never fires
  ¬f3B : ¬ PFair (srvApi l) SrvSend stall
  ¬f3B f3 = noAt◇ (λ { (lift ()) }) (f3 2 (λ k → subst (PEn (srvApi l) SrvSend) (sym (stkFS k)) srvB))

  -- (N-F3) F3 IS NEEDED.  In `blk` (the server's application never sends) the run
  -- "RequestNext commanded, sent, then stuck with both peers busy" satisfies F1 (no
  -- RequestNext after the first frame) and F2 (quit is never enabled in the pair after
  -- the first frame: the client is busy), violates F3 (the cancel stays enabled in the
  -- pair and never fires), and never reaches √: the library's run ends in a `stuck` leaf,
  -- which is not √
  nf3 : CmdOnly (srvApi l)
      × Σ[ tr ∈ Trace Rr (blk l) ]
          (F1 tr × PFair (srvApi l) QuitC tr × ¬ PFair (srvApi l) SrvSend tr × ¬ ◇ᵗ (atom Ended) tr)
  nf3 = cmdSrv , stall , (1 , □B) , f2B , ¬f3B , noEndB

  ------------------------------------------------------------------------
  -- §7  (N-F2) The client never quits: its commands withheld
  ------------------------------------------------------------------------

  -- withholding the client's commands withholds only commands
  cmdCli : CmdOnly cliCmd
  cmdCli (ap lo _ _) c = c
  cmdCli (ap hi _ _) ()
  cmdCli (wS _ _)    ()
  cmdCli (wR _ _)    ()
  cmdCli (dn _)      ()

  -- a server send is not a client command
  srvNotCli : ∀ {e} → SrvSend e → ¬ InEv l cliCmd e
  srvNotCli {evLabel _ (apiLPev _ lo _) _} ()
  srvNotCli {evLabel _ (apiLPev _ hi _) _} _ ()
  srvNotCli {evLabel _ (sendLNP _ _) _}    ()
  srvNotCli {evLabel _ (receiveLNP _ _) _} _ ()
  srvNotCli {evLabel _ (doneLNP _ _) _}    ()

  -- with both client commands withheld, the initial state has no step
  noStepI : ∀ {ℓ σ′} → Abs.Stp (EnvA cliCmd) σI ℓ σ′ → ⊥
  noStepI (PX.pτL (P1.pτL ()))
  noStepI (PX.pτL (P1.pτR ()))
  noStepI (PX.pτR ())
  noStepI (PX.psy _ _ ())
  noStepI (PX.psR _ ())
  noStepI (PX.psL ¬c (P1.psL _ (cRN _))) = ¬c U.tt
  noStepI (PX.psL ¬c (P1.psL _ (cQi _))) = ¬c U.tt
  noStepI (PX.psL _ (P1.psR ¬w sRN))     = ¬w U.tt
  noStepI (PX.psL _ (P1.psR ¬w sQi))     = ¬w U.tt
  noStepI (PX.psL _ (P1.psy _ (cRN _) ()))
  noStepI (PX.psL _ (P1.psy _ (cQi _) ()))

  -- … so it is stuck
  stkI : IsStuck (envP cliCmd)
  stkI = Gen.stuckE l (EnvA cliCmd) (env₀ cliCmd) noStepI (λ { ((() , _) , _) })

  -- at the initial state the quit command is enabled in the pair
  qI : PEn cliCmd QuitC (envP cliCmd)
  qI = en cliCmd (env₀ cliCmd) (P1.psL (λ ()) (cQi U.tt)) refl

  -- quit is enabled in the pair forever and never fires
  ¬f2I : ¬ PFair cliCmd QuitC (stuck stkI)
  ¬f2I f2 = noAt◇ (λ { (lift ()) }) (f2 0 (λ k → subst (PEn cliCmd QuitC) (sym (stkFS k)) qI))

  -- no server send is ever enabled in the pair (the server is idle)
  f3I : PFair cliCmd SrvSend (stuck stkI)
  f3I n h = ⊥-elim (cenStk cliCmd {C = SrvSend} (λ {e} → srvNotCli {e}) stkI (subst (PEn cliCmd SrvSend) (stkFS (n + 0)) (h 0)))

  -- (N-F2) F2 IS NEEDED.  When the client's application withholds its commands, the run
  -- of `envP cliCmd` is stuck at the start: F1 holds (nothing ever fires), F3 holds (no
  -- server send is ever enabled: the server is idle), F2 fails (quit is enabled in the
  -- pair forever and never fires), and √ is never reached
  nf2 : CmdOnly cliCmd
      × Σ[ tr ∈ Trace Rr (envP cliCmd) ]
          (F1 tr × ¬ PFair cliCmd QuitC tr × PFair cliCmd SrvSend tr × ¬ ◇ᵗ (atom Ended) tr)
  nf2 = cmdCli , stuck stkI , (0 , □stk (λ x → x)) , ¬f2I , f3I , noAt◇ (λ ())

  ------------------------------------------------------------------------
  -- §8  (N-F1) The client requests forever: the always-willing environment
  ------------------------------------------------------------------------

  -- one round of the loop, per phase: its weak step and the next position (RequestNext)
  s1 : ∀ {t} → Abs.Pos (EnvA ∅ES) σI t
     → Σ[ t′ ∈ Tree ] (t ═[ ev (evl ⌞ ap lo lnpSendRequestNext U.tt ⌟) ]═► t′ × Abs.Pos (EnvA ∅ES) σR t′)
  s1 = stepI (EnvI ∅ES) (aRN ∅ES (λ ()))

  -- (MsgRequestNext)
  s2 : ∀ {t} → Abs.Pos (EnvA ∅ES) σR t
     → Σ[ t′ ∈ Tree ] (t ═[ ev (evl ⌞ wS lo (pay l FromInitiator MsgLNPRequestNext) ⌟) ]═► t′
                       × Abs.Pos (EnvA ∅ES) σB t′)
  s2 = stepI (EnvI ∅ES) (aWR ∅ES (λ ()))

  -- (the cancel command)
  s3 : ∀ {t} → Abs.Pos (EnvA ∅ES) σB t
     → Σ[ t′ ∈ Tree ] (t ═[ ev (evl ⌞ ap hi lnpSendCanceled U.tt ⌟) ]═► t′ × Abs.Pos (EnvA ∅ES) σC t′)
  s3 = stepI (EnvI ∅ES) (aSC ∅ES (λ ()))

  -- (MsgCanceled)
  s4 : ∀ {t} → Abs.Pos (EnvA ∅ES) σC t
     → Σ[ t′ ∈ Tree ] (t ═[ ev (evl ⌞ wR lo (pay l FromResponder MsgLNPCanceled) ⌟) ]═► t′
                       × Abs.Pos (EnvA ∅ES) σI t′)
  s4 = stepI (EnvI ∅ES) (aWC ∅ES (λ ()))

  -- the next positions, per phase
  π1 : ∀ {t} (p : Abs.Pos (EnvA ∅ES) σI t) → Abs.Pos (EnvA ∅ES) σR (proj₁ (s1 p))
  π1 p = proj₂ (proj₂ (s1 p))

  -- (phase 2)
  π2 : ∀ {t} (p : Abs.Pos (EnvA ∅ES) σR t) → Abs.Pos (EnvA ∅ES) σB (proj₁ (s2 p))
  π2 p = proj₂ (proj₂ (s2 p))

  -- (phase 3)
  π3 : ∀ {t} (p : Abs.Pos (EnvA ∅ES) σB t) → Abs.Pos (EnvA ∅ES) σC (proj₁ (s3 p))
  π3 p = proj₂ (proj₂ (s3 p))

  -- (phase 4)
  π4 : ∀ {t} (p : Abs.Pos (EnvA ∅ES) σC t) → Abs.Pos (EnvA ∅ES) σI (proj₁ (s4 p))
  π4 p = proj₂ (proj₂ (s4 p))

  -- THE REQUEST/CANCEL LOOP, one phase per definition (forward declarations: the four
  -- phases, then their delayed tails)
  lp1 : ∀ {t} → Abs.Pos (EnvA ∅ES) σI t → Trace Rr t
  -- (RequestNext commanded)
  lp2 : ∀ {t} → Abs.Pos (EnvA ∅ES) σR t → Trace Rr t
  -- (both busy)
  lp3 : ∀ {t} → Abs.Pos (EnvA ∅ES) σB t → Trace Rr t
  -- (cancel commanded)
  lp4 : ∀ {t} → Abs.Pos (EnvA ∅ES) σC t → Trace Rr t
  -- (delayed: phase 1)
  ∞lp1 : ∀ {t} → Abs.Pos (EnvA ∅ES) σI t → ∞Trace Rr t
  -- (delayed: phase 2)
  ∞lp2 : ∀ {t} → Abs.Pos (EnvA ∅ES) σR t → ∞Trace Rr t
  -- (delayed: phase 3)
  ∞lp3 : ∀ {t} → Abs.Pos (EnvA ∅ES) σB t → ∞Trace Rr t
  -- (delayed: phase 4)
  ∞lp4 : ∀ {t} → Abs.Pos (EnvA ∅ES) σC t → ∞Trace Rr t

  lp1 p = step (proj₁ (proj₂ (s1 p))) (∞lp2 (π1 p))
  lp2 p = step (proj₁ (proj₂ (s2 p))) (∞lp3 (π2 p))
  lp3 p = step (proj₁ (proj₂ (s3 p))) (∞lp4 (π3 p))
  lp4 p = step (proj₁ (proj₂ (s4 p))) (∞lp1 (π4 p))
  ∞lp1 p .∞Trace.force = lp1 p
  ∞lp2 p .∞Trace.force = lp2 p
  ∞lp3 p .∞Trace.force = lp3 p
  ∞lp4 p .∞Trace.force = lp4 p

  -- the loop never reaches √ (forward declarations, one per phase)
  ne1 : ∀ {t} (p : Abs.Pos (EnvA ∅ES) σI t) → ◇ᵗ (atom Ended) (lp1 p) → ⊥
  -- (phase 2)
  ne2 : ∀ {t} (p : Abs.Pos (EnvA ∅ES) σR t) → ◇ᵗ (atom Ended) (lp2 p) → ⊥
  -- (phase 3)
  ne3 : ∀ {t} (p : Abs.Pos (EnvA ∅ES) σB t) → ◇ᵗ (atom Ended) (lp3 p) → ⊥
  -- (phase 4)
  ne4 : ∀ {t} (p : Abs.Pos (EnvA ∅ES) σC t) → ◇ᵗ (atom Ended) (lp4 p) → ⊥

  ne1 p (◇ᵗ-now ())
  ne1 p (◇ᵗ-later h) = ne2 (π1 p) h
  ne2 p (◇ᵗ-now ())
  ne2 p (◇ᵗ-later h) = ne3 (π2 p) h
  ne3 p (◇ᵗ-now ())
  ne3 p (◇ᵗ-later h) = ne4 (π3 p) h
  ne4 p (◇ᵗ-now ())
  ne4 p (◇ᵗ-later h) = ne1 (π4 p) h

  -- RequestNext fires within every four frames (forward declarations, one per phase)
  rn1 : ∀ n {t} (p : Abs.Pos (EnvA ∅ES) σI t) → □ᵗ (¬ᵗ (atom (Fires RNc))) (drop n (lp1 p)) → ⊥
  -- (phase 2)
  rn2 : ∀ n {t} (p : Abs.Pos (EnvA ∅ES) σR t) → □ᵗ (¬ᵗ (atom (Fires RNc))) (drop n (lp2 p)) → ⊥
  -- (phase 3)
  rn3 : ∀ n {t} (p : Abs.Pos (EnvA ∅ES) σB t) → □ᵗ (¬ᵗ (atom (Fires RNc))) (drop n (lp3 p)) → ⊥
  -- (phase 4)
  rn4 : ∀ n {t} (p : Abs.Pos (EnvA ∅ES) σC t) → □ᵗ (¬ᵗ (atom (Fires RNc))) (drop n (lp4 p)) → ⊥

  rn1 zero    p b = lower (□ᵗ-now b U.tt)
  rn1 (suc n) p b = rn2 n (π1 p) b
  rn2 zero    p b = lower (□ᵗ-now (□ᵗ-tail (□ᵗ-tail (□ᵗ-tail b))) U.tt)
  rn2 (suc n) p b = rn3 n (π2 p) b
  rn3 zero    p b = lower (□ᵗ-now (□ᵗ-tail (□ᵗ-tail b)) U.tt)
  rn3 (suc n) p b = rn4 n (π3 p) b
  rn4 zero    p b = lower (□ᵗ-now (□ᵗ-tail b) U.tt)
  rn4 (suc n) p b = rn1 n (π4 p) b

  -- a server send fires within every three frames (forward declarations, one per phase)
  sv1 : ∀ n {t} (p : Abs.Pos (EnvA ∅ES) σI t) → ◇ᵗ (atom (Fires SrvSend)) (drop n (lp1 p))
  -- (phase 2)
  sv2 : ∀ n {t} (p : Abs.Pos (EnvA ∅ES) σR t) → ◇ᵗ (atom (Fires SrvSend)) (drop n (lp2 p))
  -- (phase 3)
  sv3 : ∀ n {t} (p : Abs.Pos (EnvA ∅ES) σB t) → ◇ᵗ (atom (Fires SrvSend)) (drop n (lp3 p))
  -- (phase 4)
  sv4 : ∀ n {t} (p : Abs.Pos (EnvA ∅ES) σC t) → ◇ᵗ (atom (Fires SrvSend)) (drop n (lp4 p))

  sv1 zero    p = ◇ᵗ-later (◇ᵗ-later (◇ᵗ-now U.tt))
  sv1 (suc n) p = sv2 n (π1 p)
  sv2 zero    p = ◇ᵗ-later (◇ᵗ-now U.tt)
  sv2 (suc n) p = sv3 n (π2 p)
  sv3 zero    p = ◇ᵗ-now U.tt
  sv3 (suc n) p = sv4 n (π3 p)
  sv4 zero    p = ◇ᵗ-now U.tt
  sv4 (suc n) p = sv1 n (π4 p)

  -- a wire send is not an api label
  wsAp : ∀ {d x d′ m v} → _≡_ {A = Lab l} (wS d x) (ap d′ m v) → ⊥
  wsAp ()

  -- at σR the pair has no τ
  noτR : ∀ {σ′} → Abs.Stp (EnvA ∅ES) σR τ′ σ′ → ⊥
  noτR (PX.pτL (P1.pτL ()))
  noτR (PX.pτL (P1.pτR ()))
  noτR (PX.pτR ())

  -- at σR no step is the quit command (only MsgRequestNext is possible)
  noQstep : ∀ {ω σ′} → Abs.Stp (EnvA ∅ES) σR (ev′ ω) σ′ → ω ≡ ap lo lnpSendDone U.tt → ⊥
  noQstep (PX.psL _ (P1.psy _ cSR _)) e = wsAp e
  noQstep (PX.psL _ (P1.psL ¬w cSR))  _ = ¬w U.tt
  noQstep (PX.psL _ (P1.psR ¬w sRN))  _ = ¬w U.tt
  noQstep (PX.psL _ (P1.psR ¬w sQi))  _ = ¬w U.tt
  noQstep (PX.psR _ ())
  noQstep (PX.psy _ _ ())

  -- … nor any one-event run from σR
  noQrun : ∀ {σ′ e} → Gen.ARun l (EnvA ∅ES) σR (e ∷ []) σ′ → QuitC e → ⊥
  noQrun (Gen.rτ a _) _ = noτR a
  noQrun (Gen.rE a _) q = noQstep a (⌜⌝-inj l q)

  -- at σR (RequestNext commanded, not yet sent) quit is not enabled in the pair
  noQR : ∀ {t} → Abs.Pos (EnvA ∅ES) σR t → PEn ∅ES QuitC t → ⊥
  noQR p (_ , refl , _ , _ , w , q) = noQrun (proj₁ (proj₂ (Gen.runE l (EnvA ∅ES) p (w2r (liftW ∅ES (λ ()) w))))) q

  -- quit is never continuously enabled: the client passes σR every four frames
  -- (forward declarations, one per phase)
  nq1 : ∀ n {t} (p : Abs.Pos (EnvA ∅ES) σI t)
      → (∀ k → PEn ∅ES QuitC (frameState (frameOf (drop (n + k) (lp1 p))))) → ⊥
  -- (phase 2)
  nq2 : ∀ n {t} (p : Abs.Pos (EnvA ∅ES) σR t)
      → (∀ k → PEn ∅ES QuitC (frameState (frameOf (drop (n + k) (lp2 p))))) → ⊥
  -- (phase 3)
  nq3 : ∀ n {t} (p : Abs.Pos (EnvA ∅ES) σB t)
      → (∀ k → PEn ∅ES QuitC (frameState (frameOf (drop (n + k) (lp3 p))))) → ⊥
  -- (phase 4)
  nq4 : ∀ n {t} (p : Abs.Pos (EnvA ∅ES) σC t)
      → (∀ k → PEn ∅ES QuitC (frameState (frameOf (drop (n + k) (lp4 p))))) → ⊥

  nq1 zero    p h = noQR (π1 p) (h 1)
  nq1 (suc n) p h = nq2 n (π1 p) h
  nq2 zero    p h = noQR p (h 0)
  nq2 (suc n) p h = nq3 n (π2 p) h
  nq3 zero    p h = noQR (π1 (π4 (π3 p))) (h 3)
  nq3 (suc n) p h = nq4 n (π3 p) h
  nq4 zero    p h = noQR (π1 (π4 p)) (h 2)
  nq4 (suc n) p h = nq1 n (π4 p) h

  -- (N-F1) F1 IS NEEDED.  In the always-willing environment (`∅ES`), the client requests
  -- forever and the server always answers (with MsgCanceled): F2 holds (quit is enabled
  -- only while the client is idle, never continuously), F3 holds (the server sends every
  -- four frames), F1 fails (RequestNext fires every four frames), and √ is never reached
  nf1 : CmdOnly ∅ES
      × Σ[ tr ∈ Trace Rr (envP ∅ES) ]
          (¬ F1 tr × PFair ∅ES QuitC tr × PFair ∅ES SrvSend tr × ¬ ◇ᵗ (atom Ended) tr)
  nf1 = (λ _ ()) , lp1 (env₀ ∅ES) , (λ (n , b) → rn1 n (env₀ ∅ES) b)
      , (λ n h → ⊥-elim (nq1 n (env₀ ∅ES) h)) , (λ n _ → sv1 n (env₀ ∅ES)) , ne1 (env₀ ∅ES)
