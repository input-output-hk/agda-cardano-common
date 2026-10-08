{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- LeiosNotify (cardano-blueprint table, no pipelining): A CLIENT THAT WANTS OUT ALWAYS GETS
-- OUT, IN BOUNDED TIME, PROVIDED THE SERVER CANCELS WHEN IT HAS NOTHING TO ANNOUNCE.
--
-- Everything is reused from `LeiosNotifyQuit.agda`: the real client at `(l , lo)`, the
-- renamed real server `srv`, the pair `sys`, the cancel-only system `blkC` (the server's
-- four notification api sends refused, `lnpSendCanceled` open), the abstraction framework
-- (`Abs` / `AbsI` / `Gen` / `GenI` / `Prod` / `Walk`), the component abstractions, the
-- 9-phase invariant `J` (`J-step` via `Walk.walk`), `cτ?` / `sτ?`, and the stall `blk-stall`.
--
-- "THE CLIENT DECIDES TO STOP REQUESTING".  At an ARBITRARY point of a run (any trace `s`
-- to any state `W`), the client's application stops issuing `lnpSendRequestNext`:
--     stop W = W [| noRN |] Skip        (`noRN`: the client's RequestNext api trigger)
-- i.e. from `W` on that event is refused; everything else (the quit command `lnpSendDone`,
-- the deliveries, the server's api, its done) stays open to the environment.  NO FAIRNESS:
-- the conclusions bound EVERY run of `stop W`, whatever the environment / scheduler picks.
--
-- THE RESULTS (∀ `Params`, ∀ link `l`):
--   (N) NO LOAD — the server cancels (its notification sends refused: `blkC`).
--       `cancel-quitCompletes`: for every `blkC`-reachable `W`, `stop W` is deadlock-free,
--       divergence-free, and every √-free trace of it has at most 7 visible events.
--       `cancel-√reachable`: from every state reachable in `stop W`, √ is reachable.
--       `cancel-tight`: the bound 7 is attained (so it is the tightest uniform bound).
--   (L) LOAD — all server api sends open (`sys` itself: the server may answer with a real
--       notification or cancel).  `load-quitCompletes` (bound 8), `load-√reachable`,
--       `load-tight` (8 attained).
--   (X) CONTRAST — the cancel refused too (`blk`).  `blk-stall-stop`: after RequestNext
--       the blocked pair is stuck (`blk-stall`), and `stop` does not help (`stuckStop`).
-- Together, DeadlockFree × DivergenceFree × (bounded √-free traces) say that EVERY MAXIMAL
-- RUN of `stop W` IS FINITE AND ENDS IN √: an infinite run would have infinitely many τ's
-- after its last visible event (divergence), and a finite run that cannot be extended
-- either has a √ step available or is stuck (deadlock).  The library has no "every maximal
-- run" predicate, so this is stated as the three conjuncts plus the constructive
-- √-reachability corollary (`*-√reachable`).
------------------------------------------------------------------------

open import Cardano_network.Params using (Params)

module Cardano_network.Parametric.Leios.LeiosNotifyQuitCancel (p : Params) where

open import Data.Bool using (Bool; true; false; T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _≤ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; <-≤-trans; ≤ᵇ⇒≤; ≤-pred; n≤1+n)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Data.Unit as U
open import Data.Unit.Polymorphic using (tt)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable.Core using (T?)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Process_Trees
open import Cardano_network.Base
open import Cardano_network.Net p
open import Cardano_network.Data p
open import Cardano_network.LeiosNotifyP p
open import Cardano_network.Parametric.Leios.LeiosNotifyQuit p

open import CSP.Operators LNPEv-≟ using (Par⊤; Skip; EventSet)
open EventSet
open import Semantics.LTS {E = LNPEv} {I = ExtI LNPEv}
open import Semantics.Deadlock {E = LNPEv} {I = ExtI LNPEv}
  using (IsStuck; DeadlockFree; _⟹∖√⟨_⟩_; ∖√-refl; ∖√-τ; ∖√-ev)
open import Semantics.DivergenceFree {E = LNPEv} {I = ExtI LNPEv} using (DivergenceFree)
open import CSP.Laws.Traces.TraceLawsParallelElim LNPEv-≟
  using (τL; τR; evSync; evL; evR; evBoth; ev√; Par-τ-elim; Par-ev-elim)

------------------------------------------------------------------------
-- everything below is for one link `l`
------------------------------------------------------------------------

module _ (l : Link) where

  -- this link's abstract labels, read as events
  ⌞_⌟ : Lab l → Event
  ⌞_⌟ = ⌜_⌝ l

  ------------------------------------------------------------------------
  -- §1  The client's decision to stop requesting
  ------------------------------------------------------------------------

  -- whether an event is the client's (direction `lo`) RequestNext api trigger
  rnEv : ∀ {A} → LNPEv A → Bool
  rnEv (apiLPev _ lo lnpSendRequestNext) = true
  rnEv _                                 = false

  -- the client's RequestNext api trigger, as an event set (refused by `stop`)
  noRN : EventSet
  noRN = record { mem = λ at _ → T (rnEv (proj₂ at)) ; dec = λ at _ → T? (rnEv (proj₂ at)) }

  -- THE CLIENT WANTS OUT: from `W` on, the client's application never again commands
  -- RequestNext (everything else is unchanged and stays open)
  stop : Tree → Tree
  stop W = Par⊤ noRN W Skip

  -- a step label that `stop` lets through (a τ, or a label off `noRN`)
  NoRN : ALbl l → Set
  NoRN τ′      = U.⊤
  NoRN (ev′ ω) = ¬ InE l noRN ω

  -- a step label the server policy lets through: under load (`true`) everything, with no
  -- load (`false`) a τ or a label off the four notification sends `srvApiN`
  Allowed : Bool → ALbl l → Set
  Allowed true  _       = U.⊤
  Allowed false τ′      = U.⊤
  Allowed false (ev′ ω) = ¬ InE l (srvApiN l) ω

  ------------------------------------------------------------------------
  -- §2  The rank: the most visible events left once RequestNext is refused
  ------------------------------------------------------------------------

  -- the rank at `j3` (both peers in StBusy): with no load the server's only move is the
  -- cancel (cancel api, Canceled, then the quit's 4 = 6); under load it may instead send
  -- a notification, which the client still has to deliver (api, wire, delivery, 4 = 7)
  r3 : Bool → ℕ
  r3 false = 6
  r3 true  = 7

  -- the rank of a joint phase.  After the quit command: MsgQuit, done, MsgDone (q1 = 3).
  -- j1 (StIdle, RequestNext refused): the quit's 4.  j2 (RequestNext commanded, not yet
  -- sent): one wire event more than j3.  j4: the reply on the wire (+ a delivery for a
  -- notification) then j1.  j5: the delivery then j1
  rk : Bool → ∀ {c s} → J l c s → ℕ
  rk _  j1      = 4
  rk ld j2      = suc (r3 ld)
  rk ld j3      = r3 ld
  rk _  (j4 rC) = 5
  rk _  (j4 _)  = 6
  rk _  (j5 _)  = 5
  rk _  q1      = 3
  rk _  q2      = 2
  rk _  q3      = 1
  rk _  q4      = 0

  -- the rank at `j3` is at least 6
  six≤ : ∀ ld → 6 ≤ r3 ld
  six≤ false = ≤-refl
  six≤ true  = n≤1+n 6

  -- a constant up to 7 is below the top rank
  upTo : ∀ ld {n} → T (n ≤ᵇ 7) → n ≤ suc (r3 ld)
  upTo ld {n} t = ≤-trans (≤ᵇ⇒≤ n 7 t) (s≤s (six≤ ld))

  -- every rank is at most the top rank `suc (r3 ld)` (7 with no load, 8 under load)
  rk≤ : ∀ ld {c s} (j : J l c s) → rk ld j ≤ suc (r3 ld)
  rk≤ ld j1            = upTo ld _
  rk≤ ld j2            = ≤-refl
  rk≤ ld j3            = n≤1+n (r3 ld)
  rk≤ ld (j4 rC)       = upTo ld _
  rk≤ ld (j4 (rA _))   = upTo ld _
  rk≤ ld (j4 (rO _ _)) = upTo ld _
  rk≤ ld (j4 (rT _))   = upTo ld _
  rk≤ ld (j4 (rV _))   = upTo ld _
  rk≤ ld (j5 _)        = upTo ld _
  rk≤ ld q1            = upTo ld _
  rk≤ ld q2            = upTo ld _
  rk≤ ld q3            = upTo ld _
  rk≤ ld q4            = upTo ld _

  -- the side fact of a step: a τ keeps the rank, a visible event strictly lowers it
  KSide : Bool → ∀ {c s c′ s′} → ALbl l → J l c s → J l c′ s′ → Set
  KSide ld τ′      j j′ = rk ld j′ ≡ rk ld j
  KSide ld (ev′ _) j j′ = T (suc (rk ld j′) ≤ᵇ rk ld j)

  -- a client api step lowers the rank (RequestNext is refused)
  kcapi : ∀ ld {c fc c′ fc′ s ω} → ¬ InE l (wireES l) ω → ¬ InE l noRN ω
        → CStp l (c , fc) (ev′ ω) (c′ , fc′) → (j : J l c s) → Σ[ j′ ∈ J l c′ s ] KSide ld (ev′ ω) j j′
  kcapi _ _  nr (cRN _)   j1     = ⊥-elim (nr U.tt)
  kcapi _ _  _  (cQi _)   j1     = q1 , _
  kcapi _ _  _  (cDA _)   (j5 _) = j1 , _
  kcapi _ _  _  (cDO _ _) (j5 _) = j1 , _
  kcapi _ _  _  (cDT _)   (j5 _) = j1 , _
  kcapi _ _  _  (cDV _)   (j5 _) = j1 , _
  kcapi _ ¬w _  cSR       _      = ⊥-elim (¬w U.tt)
  kcapi _ ¬w _  cSQ       _      = ⊥-elim (¬w U.tt)
  kcapi _ ¬w _  (cRA _)   _      = ⊥-elim (¬w U.tt)
  kcapi _ ¬w _  (cRO _ _) _      = ⊥-elim (¬w U.tt)
  kcapi _ ¬w _  (cRT _)   _      = ⊥-elim (¬w U.tt)
  kcapi _ ¬w _  (cRV _)   _      = ⊥-elim (¬w U.tt)
  kcapi _ ¬w _  cRC       _      = ⊥-elim (¬w U.tt)
  kcapi _ ¬w _  cDn       _      = ⊥-elim (¬w U.tt)

  -- a server api / done step lowers the rank (with no load, a notification is refused)
  ksapi : ∀ ld {c s fs s′ fs′ ω} → ¬ InE l (wireES l) ω → Allowed ld (ev′ ω)
        → SStp l (s , fs) (ev′ ω) (s′ , fs′) → (j : J l c s) → Σ[ j′ ∈ J l c s′ ] KSide ld (ev′ ω) j j′
  ksapi true  _  _  (sAA _)   j3 = j4 _ , _
  ksapi true  _  _  (sAO _ _) j3 = j4 _ , _
  ksapi true  _  _  (sAT _)   j3 = j4 _ , _
  ksapi true  _  _  (sAV _)   j3 = j4 _ , _
  ksapi true  _  _  (sAC _)   j3 = j4 _ , _
  ksapi false _  al (sAA _)   j3 = ⊥-elim (al U.tt)
  ksapi false _  al (sAO _ _) j3 = ⊥-elim (al U.tt)
  ksapi false _  al (sAT _)   j3 = ⊥-elim (al U.tt)
  ksapi false _  al (sAV _)   j3 = ⊥-elim (al U.tt)
  ksapi false _  _  (sAC _)   j3 = j4 _ , _
  ksapi _     _  _  sDn       q2 = q3 , _
  ksapi _     ¬w _  sRN       _  = ⊥-elim (¬w U.tt)
  ksapi _     ¬w _  sQi       _  = ⊥-elim (¬w U.tt)
  ksapi _     ¬w _  (sNA _)   _  = ⊥-elim (¬w U.tt)
  ksapi _     ¬w _  (sNO _ _) _  = ⊥-elim (¬w U.tt)
  ksapi _     ¬w _  (sNT _)   _  = ⊥-elim (¬w U.tt)
  ksapi _     ¬w _  (sNV _)   _  = ⊥-elim (¬w U.tt)
  ksapi _     ¬w _  sNC       _  = ⊥-elim (¬w U.tt)
  ksapi _     ¬w _  sDS       _  = ⊥-elim (¬w U.tt)

  -- a rendezvous lowers the rank
  ksync : ∀ ld {c fc c′ fc′ s fs s′ fs′ ω} → CStp l (c , fc) (ev′ ω) (c′ , fc′) → SStp l (s , fs) (ev′ ω) (s′ , fs′)
        → (j : J l c s) → Σ[ j′ ∈ J l c′ s′ ] KSide ld (ev′ ω) j j′
  ksync false cSR        sRN       j2     = j3 , _
  ksync true  cSR        sRN       j2     = j3 , _
  ksync _     cSQ        sQi       q1     = q2 , _
  ksync _     (cRA h)    (sNA _)   (j4 _) = j5 (dAnn h) , _
  ksync _     (cRO q sz) (sNO _ _) (j4 _) = j5 (dOff q sz) , _
  ksync _     (cRT q)    (sNT _)   (j4 _) = j5 (dTxs q) , _
  ksync _     (cRV vs)   (sNV _)   (j4 _) = j5 (dVot vs) , _
  ksync _     cRC        sNC       (j4 _) = j1 , _
  ksync _     cDn        sDS       q3     = q4 , _
  ksync _ (cRN _)   ()
  ksync _ (cQi _)   ()
  ksync _ (cDA _)   ()
  ksync _ (cDO _ _) ()
  ksync _ (cDT _)   ()
  ksync _ (cDV _)   ()

  -- THE RANK IS A VARIANT: every system step the policy and `stop` let through keeps the
  -- invariant `J`, keeps the rank on a τ and strictly lowers it on a visible event
  kstep : ∀ ld {σ ℓ σ′} (j : JJ l σ) → Abs.Stp (SysA l) σ ℓ σ′ → Allowed ld ℓ → NoRN ℓ
        → Σ[ j′ ∈ JJ l σ′ ] KSide ld ℓ j j′
  kstep _  j (P1.pτL cτI)   _  _  = j , refl
  kstep _  j (P1.pτL cτB)   _  _  = j , refl
  kstep _  j (P1.pτL cτQ)   _  _  = j , refl
  kstep _  j (P1.pτR sτI)   _  _  = j , refl
  kstep _  j (P1.pτR sτB)   _  _  = j , refl
  kstep _  j (P1.pτR sτQ)   _  _  = j , refl
  kstep ld j (P1.psL ¬w a)  _  nr = kcapi ld ¬w nr a j
  kstep ld j (P1.psR ¬w a)  al _  = ksapi ld ¬w al a j
  kstep ld j (P1.psy _ a b) _  _  = ksync ld a b j

  ------------------------------------------------------------------------
  -- §3  Progress without RequestNext and without a notification send
  ------------------------------------------------------------------------

  -- PROGRESS with no loop-back pending: every joint phase has a step that is neither
  -- RequestNext nor a notification send, or has terminated.  At `j1` the step is the quit
  -- command, at `j3` the cancel
  kprogJ : ∀ {c s} (j : J l c s)
         → Abs.Fin (SysA l) ((c , false) , (s , false))
         ⊎ Σ[ ℓ ∈ ALbl l ] Σ[ σ′ ∈ SysS l ] (Abs.Stp (SysA l) ((c , false) , (s , false)) ℓ σ′ × Allowed false ℓ × NoRN ℓ)
  kprogJ j1               = inj₂ (_ , _ , P1.psL (λ ()) (cQi U.tt) , (λ ()) , (λ ()))
  kprogJ j2               = inj₂ (_ , _ , P1.psy U.tt cSR sRN , (λ ()) , (λ ()))
  kprogJ j3               = inj₂ (_ , _ , P1.psR (λ ()) (sAC U.tt) , (λ ()) , (λ ()))
  kprogJ (j4 (rA h))      = inj₂ (_ , _ , P1.psy U.tt (cRA h) (sNA h) , (λ ()) , (λ ()))
  kprogJ (j4 (rO q sz))   = inj₂ (_ , _ , P1.psy U.tt (cRO q sz) (sNO q sz) , (λ ()) , (λ ()))
  kprogJ (j4 (rT q))      = inj₂ (_ , _ , P1.psy U.tt (cRT q) (sNT q) , (λ ()) , (λ ()))
  kprogJ (j4 (rV vs))     = inj₂ (_ , _ , P1.psy U.tt (cRV vs) (sNV vs) , (λ ()) , (λ ()))
  kprogJ (j4 rC)          = inj₂ (_ , _ , P1.psy U.tt cRC sNC , (λ ()) , (λ ()))
  kprogJ (j5 (dAnn h))    = inj₂ (_ , _ , P1.psL (λ ()) (cDA h) , (λ ()) , (λ ()))
  kprogJ (j5 (dOff q sz)) = inj₂ (_ , _ , P1.psL (λ ()) (cDO q sz) , (λ ()) , (λ ()))
  kprogJ (j5 (dTxs q))    = inj₂ (_ , _ , P1.psL (λ ()) (cDT q) , (λ ()) , (λ ()))
  kprogJ (j5 (dVot vs))   = inj₂ (_ , _ , P1.psL (λ ()) (cDV vs) , (λ ()) , (λ ()))
  kprogJ q1               = inj₂ (_ , _ , P1.psy U.tt cSQ sQi , (λ ()) , (λ ()))
  kprogJ q2               = inj₂ (_ , _ , P1.psR (λ ()) sDn , (λ ()) , (λ ()))
  kprogJ q3               = inj₂ (_ , _ , P1.psy U.tt cDn sDS , (λ ()) , (λ ()))
  kprogJ q4               = inj₁ (U.tt , U.tt)

  -- PROGRESS at every positioned system state: a pending loop-back τ, or the phase's witness
  kprog : ∀ {σ t} (j : JJ l σ) → Abs.Pos (SysA l) σ t
        → Abs.Fin (SysA l) σ ⊎ Σ[ ℓ ∈ ALbl l ] Σ[ σ′ ∈ SysS l ] (Abs.Stp (SysA l) σ ℓ σ′ × Allowed false ℓ × NoRN ℓ)
  kprog j (_ , _ , _ , pc , (_ , _ , ps)) with cτ? l pc | sτ? l ps
  ... | inj₂ (_ , a) | _            = inj₂ (τ′ , _ , P1.pτL a , U.tt , U.tt)
  ... | inj₁ refl    | inj₂ (_ , a) = inj₂ (τ′ , _ , P1.pτR a , U.tt , U.tt)
  ... | inj₁ refl    | inj₁ refl    = kprogJ j

  ------------------------------------------------------------------------
  -- §4  `stop` over a policy-restricted system (generic in the policy)
  ------------------------------------------------------------------------

  -- `stop` applied to the states of a system abstracted by `A` (whose states project to
  -- system states by `π`, whose steps are system steps the policy `ld` allows, and which
  -- has progress without RequestNext)
  module Stop (ld : Bool) {S : Set} (A : Abs l S) (I : AbsI l A) (π : S → SysS l)
              (un : ∀ {σ ℓ σ′} → Abs.Stp A σ ℓ σ′ → Abs.Stp (SysA l) (π σ) ℓ (π σ′))
              (okA : ∀ {σ ℓ σ′} → Abs.Stp A σ ℓ σ′ → Allowed ld ℓ)
              (progA : ∀ {σ t} → JJ l (π σ) → Abs.Pos A σ t
                     → Abs.Fin A σ ⊎ Σ[ ℓ ∈ ALbl l ] Σ[ σ′ ∈ S ] (Abs.Stp A σ ℓ σ′ × NoRN ℓ)) where

    -- the system with RequestNext refused
    module P6 = Prod l A (SkA l) noRN (λ {ω} → disjSk l {noRN} {ω})

    -- its abstraction
    StopA : Abs l (S × U.⊤)
    StopA = P6.ParA

    -- … and intro facts
    StopI : AbsI l StopA
    StopI = P6.ParI I (SkI l)

    open Gen l StopA using (ARun; r0; rτ; rE; runE)

    -- `stop` of a positioned tree is positioned
    stop₀ : ∀ {σ t} → Abs.Pos A σ t → Abs.Pos StopA (σ , U.tt) (stop t)
    stop₀ p = _ , _ , refl , p , refl

    -- a step of `stop` is a step of the system that avoids `noRN`
    unS : ∀ {σ ℓ σ′} → Abs.Stp StopA σ ℓ σ′ → Abs.Stp A (proj₁ σ) ℓ (proj₁ σ′) × NoRN ℓ
    unS (P6.pτL a)      = a , U.tt
    unS (P6.psL nr a)   = a , nr
    unS (P6.pτR ())
    unS (P6.psy _ _ ())
    unS (P6.psR _ ())

    -- the variant along a step of `stop`
    kS : ∀ {σ ℓ σ′} (j : JJ l (π (proj₁ σ))) → Abs.Stp StopA σ ℓ σ′
       → Σ[ j′ ∈ JJ l (π (proj₁ σ′)) ] KSide ld ℓ j j′
    kS j a = kstep ld j (un (proj₁ (unS a))) (okA (proj₁ (unS a))) (proj₂ (unS a))

    -- the invariant `J` along runs of `stop` (reused: `Walk`)
    module WSt = Walk l StopA (λ σ → π (proj₁ σ)) (λ a → un (proj₁ (unS a)))

    -- a run of `stop` has at most `rk` visible events
    kbound : ∀ {σ s σ′} → ARun σ s σ′ → (j : JJ l (π (proj₁ σ))) → length s ≤ rk ld j
    kbound r0        _ = z≤n
    kbound (rτ a ar) j with kS j a
    ... | j₁ , eq = subst (_ ≤_) eq (kbound ar j₁)
    kbound (rE a ar) j with kS j a
    ... | j₁ , d = ≤-trans (s≤s (kbound ar j₁)) (≤ᵇ⇒≤ (suc (rk ld j₁)) (rk ld j) d)

    -- progress of `stop`
    progS6 : ∀ {σ t} → JJ l (π (proj₁ σ)) → Abs.Pos StopA σ t
           → Abs.Fin StopA σ ⊎ Σ[ ℓ ∈ ALbl l ] Σ[ σ′ ∈ S × U.⊤ ] Abs.Stp StopA σ ℓ σ′
    progS6 j (_ , _ , refl , p , refl) with progA j p
    ... | inj₁ f                      = inj₁ (f , U.tt)
    ... | inj₂ (τ′ , _ , a , _)       = inj₂ (τ′ , _ , P6.pτL a)
    ... | inj₂ (ev′ _ , _ , a , nr)   = inj₂ (ev′ _ , _ , P6.psL nr a)

    -- `stop` of a positioned tree satisfying `J`: deadlock-free, divergence-free, and
    -- every √-free trace has at most `suc (r3 ld)` visible events
    completes : ∀ {σ t} → Abs.Pos A σ t → JJ l (π σ)
              → DeadlockFree (stop t) × DivergenceFree (stop t)
              × (∀ {s′ W′} → stop t ⟹∖√⟨ s′ ⟩ W′ → length s′ ≤ suc (r3 ld))
    completes {t = t} p j = WSt.dlFree StopI progS6 (stop₀ p) j , Gen.divFree l StopA (stop₀ p) , bd
      where
      -- the bound, from the variant
      bd : ∀ {s′ W′} → stop t ⟹∖√⟨ s′ ⟩ W′ → length s′ ≤ suc (r3 ld)
      bd r with runE (stop₀ p) r
      ... | _ , ar , _ = ≤-trans (kbound ar j) (rk≤ ld j)

    -- a run from a tree to √
    ToEnd : Tree → Set₁
    ToEnd t = Σ[ s ∈ List Event ] Σ[ t′ ∈ Tree ] (t ⟹∖√⟨ s ⟩ t′ × PTree.force t′ ≡ ret tt)

    -- from a positioned state of `stop`, follow the progress witnesses to √: by the rank
    -- on visible events (`toEnd`) and, between them, the τ-measure on τ's (`toEndτ`)
    toEnd  : ∀ n {σ t} (j : JJ l (π (proj₁ σ))) → rk ld j < n → Abs.Pos StopA σ t → ToEnd t
    -- (the inner recursion, on a bound of the τ-measure, at rank at most `n`)
    toEndτ : ∀ n k {σ t} (j : JJ l (π (proj₁ σ))) → rk ld j < suc n → Abs.μ StopA σ < k
           → Abs.Pos StopA σ t → ToEnd t

    toEnd zero    _ () _
    toEnd (suc n) {σ} j lt p = toEndτ n (suc (Abs.μ StopA σ)) j lt ≤-refl p

    toEndτ _ zero _ _ () _
    toEndτ n (suc k) j lt lk p with progS6 j p
    ... | inj₁ f = [] , _ , ∖√-refl , AbsI.introR StopI p f
    ... | inj₂ (τ′ , _ , a) with kS j a | AbsI.introτ StopI p a
    ...   | j′ , eq | _ , st , p′
            with toEndτ n k j′ (subst (_< suc n) (sym eq) lt) (<-≤-trans (Abs.μτ StopA a) (≤-pred lk)) p′
    ...     | s , t′ , r , f = s , t′ , ∖√-τ st r , f
    toEndτ n (suc k) j lt lk p | inj₂ (ev′ _ , _ , a) with kS j a | AbsI.introE StopI p a
    ...   | j′ , d | _ , st , p′
            with toEnd n j′ (<-≤-trans (≤ᵇ⇒≤ (suc (rk ld j′)) _ d) (≤-pred lt)) p′
    ...     | s , t′ , r , f = _ ∷ s , t′ , ∖√-ev st r , f

    -- from every state reachable in `stop t`, √ is reachable
    reach : ∀ {σ t} → Abs.Pos A σ t → JJ l (π σ) → ∀ {s′ W′} → stop t ⟹∖√⟨ s′ ⟩ W′
          → ToEnd W′
    reach p j r with runE (stop₀ p) r
    ... | _ , ar , p′ with WSt.walk ar j
    ...   | j′ , _ = toEnd (suc (rk ld j′)) j′ ≤-refl p′

  ------------------------------------------------------------------------
  -- §5  (N) No load: the server cancels
  ------------------------------------------------------------------------

  -- a step of the cancel-only system is a system step
  unblkC : ∀ {σ u ℓ σ′ u′} → Abs.Stp (BlkCA l) (σ , u) ℓ (σ′ , u′) → Abs.Stp (SysA l) σ ℓ σ′
  unblkC (P5.pτL a)   = a
  unblkC (P5.psL _ a) = a
  unblkC (P5.pτR ())
  unblkC (P5.psy _ _ ())
  unblkC (P5.psR _ ())

  -- … which the no-load policy allows
  okC : ∀ {σ ℓ σ′} → Abs.Stp (BlkCA l) σ ℓ σ′ → Allowed false ℓ
  okC (P5.pτL _)    = U.tt
  okC (P5.psL ¬m _) = ¬m
  okC (P5.pτR ())
  okC (P5.psy _ _ ())
  okC (P5.psR _ ())

  -- progress of the cancel-only system without RequestNext
  progC : ∀ {σ t} → JJ l (proj₁ σ) → Abs.Pos (BlkCA l) σ t
        → Abs.Fin (BlkCA l) σ ⊎ Σ[ ℓ ∈ ALbl l ] Σ[ σ′ ∈ SysS l × U.⊤ ] (Abs.Stp (BlkCA l) σ ℓ σ′ × NoRN ℓ)
  progC j (_ , _ , refl , p , refl) with kprog j p
  ... | inj₁ f                         = inj₁ (f , U.tt)
  ... | inj₂ (τ′ , _ , a , _ , nr)     = inj₂ (τ′ , _ , P5.pτL a , nr)
  ... | inj₂ (ev′ _ , _ , a , al , nr) = inj₂ (ev′ _ , _ , P5.psL al a , nr)

  -- `stop` over the cancel-only system
  module StC = Stop false (BlkCA l) (BlkCI l) proj₁ unblkC okC progC
  -- the invariant along runs of the cancel-only system
  module WC = Walk l (BlkCA l) proj₁ unblkC

  -- (N) WITH A SERVER THAT CANCELS WHEN IT HAS NOTHING TO ANNOUNCE, A CLIENT THAT STOPS
  -- REQUESTING ALWAYS GETS OUT.  Whatever has happened so far (any trace `s` of `blkC` to
  -- any `W`), once RequestNext is refused the rest never gets stuck before √, never
  -- diverges, and has AT MOST 7 VISIBLE EVENTS, on every run (no fairness).  7 is the
  -- worst case: RequestNext commanded but not yet sent (phase j2) still owes MsgRequestNext,
  -- then the cancel api, MsgCanceled, the quit command `lnpSendDone`, MsgQuit, the
  -- server's done, MsgDone.  From StBusy (j3) it is 6, from StIdle (j1) 4.  DeadlockFree
  -- is relative to the environment offering the open api events the peers ask for (here
  -- `lnpSendCanceled`, `lnpSendDone`, the deliveries and `doneLNP`): the pair itself never
  -- refuses everything
  cancel-quitCompletes : ∀ {s W} → blkC l ⟹∖√⟨ s ⟩ W
                       → DeadlockFree (stop W) × DivergenceFree (stop W)
                       × (∀ {s′ W′} → stop W ⟹∖√⟨ s′ ⟩ W′ → length s′ ≤ 7)
  cancel-quitCompletes r with Gen.runE l (BlkCA l) (blkC₀ l) r
  ... | _ , ar , p = StC.completes p (proj₁ (WC.walk ar j1))

  -- (N) … COROLLARY: from every state reachable after the client stops requesting, √ is
  -- reachable.  With the three conjuncts above: every maximal run of `stop W` is finite
  -- and ends in √
  cancel-√reachable : ∀ {s W} → blkC l ⟹∖√⟨ s ⟩ W → ∀ {s′ W′} → stop W ⟹∖√⟨ s′ ⟩ W′
                    → Σ[ s″ ∈ List Event ] Σ[ W″ ∈ Tree ] (W′ ⟹∖√⟨ s″ ⟩ W″ × PTree.force W″ ≡ ret tt)
  cancel-√reachable r with Gen.runE l (BlkCA l) (blkC₀ l) r
  ... | _ , ar , p = StC.reach p (proj₁ (WC.walk ar j1))

  -- the client commands RequestNext (not yet sent)
  trRN1 : List Event
  trRN1 = ⌞ ap lo lnpSendRequestNext U.tt ⌟ ∷ []

  -- the 7 events from there: MsgRequestNext, cancel, MsgCanceled, quit, MsgQuit, done, MsgDone
  trC7 : List Event
  trC7 = ⌞ wS lo (pay l FromInitiator MsgLNPRequestNext) ⌟ ∷ ⌞ ap hi lnpSendCanceled U.tt ⌟
       ∷ ⌞ wR lo (pay l FromResponder MsgLNPCanceled) ⌟ ∷ ⌞ ap lo lnpSendDone U.tt ⌟
       ∷ ⌞ wS lo (pay l FromInitiator MsgLNPQuit) ⌟ ∷ ⌞ dn hi ⌟ ∷ ⌞ wR lo (pay l FromResponder MsgLNPDone) ⌟ ∷ []

  -- the system state after `trRN1`: client committed to send RequestNext, server idle
  σR : SysS l
  σR = (cR , false) , (sI , false)

  -- the terminated system state
  σE : SysS l
  σE = (cE , false) , (sE , false)

  -- the abstract run of the cancel-only system along `trRN1`
  runRN1 : Gen.ARun l (BlkCA l) (σ₀ l , U.tt) trRN1 (σR , U.tt)
  runRN1 = rE (P5.psL (λ ()) (P1.psL (λ ()) (cRN U.tt))) r0
    where open Gen l (BlkCA l) using (rE; r0)

  -- the abstract run of `stop` along `trC7`, to the terminated state
  runC7 : Gen.ARun l StC.StopA ((σR , U.tt) , U.tt) trC7 ((σE , U.tt) , U.tt)
  runC7 = rE (StC.P6.psL (λ ()) (P5.psL (λ ()) (P1.psy U.tt cSR sRN)))
        (rτ (StC.P6.pτL (P5.pτL (P1.pτL cτB)))
        (rτ (StC.P6.pτL (P5.pτL (P1.pτR sτB)))
        (rE (StC.P6.psL (λ ()) (P5.psL (λ ()) (P1.psR (λ ()) (sAC U.tt))))
        (rE (StC.P6.psL (λ ()) (P5.psL (λ ()) (P1.psy U.tt cRC sNC)))
        (rτ (StC.P6.pτL (P5.pτL (P1.pτL cτI)))
        (rτ (StC.P6.pτL (P5.pτL (P1.pτR sτI)))
        (rE (StC.P6.psL (λ ()) (P5.psL (λ ()) (P1.psL (λ ()) (cQi U.tt))))
        (rE (StC.P6.psL (λ ()) (P5.psL (λ ()) (P1.psy U.tt cSQ sQi)))
        (rτ (StC.P6.pτL (P5.pτL (P1.pτL cτQ)))
        (rτ (StC.P6.pτL (P5.pτL (P1.pτR sτQ)))
        (rE (StC.P6.psL (λ ()) (P5.psL (λ ()) (P1.psR (λ ()) sDn)))
        (rE (StC.P6.psL (λ ()) (P5.psL (λ ()) (P1.psy U.tt cDn sDS)))
         r0))))))))))))
    where open Gen l StC.StopA using (rE; rτ; r0)

  -- (N) THE BOUND 7 IS TIGHT: after RequestNext is commanded, `stop` has a 7-event run to √.
  -- (The two runs are consumed by helper functions, not by `with`: with-abstracting the
  -- second run over this goal exhausts a 20 GB heap.)
  cancel-tight : Σ[ W ∈ Tree ] Σ[ W′ ∈ Tree ]
                   (blkC l ⟹∖√⟨ trRN1 ⟩ W × stop W ⟹∖√⟨ trC7 ⟩ W′ × length trC7 ≡ 7 × PTree.force W′ ≡ ret tt)
  cancel-tight = go (GenI.runI l (BlkCI l) runRN1 (blkC₀ l))
    where
    -- the second run, from `stop` of the first run's end
    go : Σ[ W ∈ Tree ] (blkC l ⟹∖√⟨ trRN1 ⟩ W × Abs.Pos (BlkCA l) (σR , U.tt) W)
       → Σ[ W ∈ Tree ] Σ[ W′ ∈ Tree ]
           (blkC l ⟹∖√⟨ trRN1 ⟩ W × stop W ⟹∖√⟨ trC7 ⟩ W′ × length trC7 ≡ 7 × PTree.force W′ ≡ ret tt)
    go (W , r , p) = go′ (GenI.runI l StC.StopI runC7 (StC.stop₀ p))
      where
      -- the end of the second run has terminated
      go′ : Σ[ W′ ∈ Tree ] (stop W ⟹∖√⟨ trC7 ⟩ W′ × Abs.Pos StC.StopA ((σE , U.tt) , U.tt) W′)
          → Σ[ W ∈ Tree ] Σ[ W′ ∈ Tree ]
              (blkC l ⟹∖√⟨ trRN1 ⟩ W × stop W ⟹∖√⟨ trC7 ⟩ W′ × length trC7 ≡ 7 × PTree.force W′ ≡ ret tt)
      go′ (W′ , r′ , p′) = W , W′ , r , r′ , refl , AbsI.introR StC.StopI p′ (((U.tt , U.tt) , U.tt) , U.tt)

  ------------------------------------------------------------------------
  -- §6  (L) Load: every server api send open
  ------------------------------------------------------------------------

  -- progress of the system without RequestNext
  progL : ∀ {σ t} → JJ l σ → Abs.Pos (SysA l) σ t
        → Abs.Fin (SysA l) σ ⊎ Σ[ ℓ ∈ ALbl l ] Σ[ σ′ ∈ SysS l ] (Abs.Stp (SysA l) σ ℓ σ′ × NoRN ℓ)
  progL j p with kprog j p
  ... | inj₁ f                    = inj₁ f
  ... | inj₂ (ℓ , σ′ , a , _ , nr) = inj₂ (ℓ , σ′ , a , nr)

  -- `stop` over the open system
  module StL = Stop true (SysA l) (SysI l) (λ σ → σ) (λ a → a) (λ _ → U.tt) progL
  -- the invariant along runs of the open system
  module WL = Walk l (SysA l) (λ σ → σ) (λ a → a)

  -- (L) UNDER LOAD THE CLIENT STILL GETS OUT.  All server api sends open: in StBusy the
  -- server may answer with a real notification (any payload) or cancel.  Same conclusions,
  -- bound 8: the worst case (j2) owes MsgRequestNext, a notification api send and its wire
  -- message, the client's delivery, then the quit's 4 (lnpSendDone, MsgQuit, done,
  -- MsgDone); after that delivery the client is in StIdle, where RequestNext is refused,
  -- so at most ONE further notification is ever delivered.  The open payload types make
  -- the branching infinite (any header / point / size / vote list), but not the depth:
  -- the bound is uniform.  DeadlockFree means: provided the environment offers the api
  -- events the peers ask for (the server's sends are environment-supplied here)
  load-quitCompletes : ∀ {s W} → sys l ⟹∖√⟨ s ⟩ W
                     → DeadlockFree (stop W) × DivergenceFree (stop W)
                     × (∀ {s′ W′} → stop W ⟹∖√⟨ s′ ⟩ W′ → length s′ ≤ 8)
  load-quitCompletes r with Gen.runE l (SysA l) (sys₀ l) r
  ... | _ , ar , p = StL.completes p (proj₁ (WL.walk ar j1))

  -- (L) … COROLLARY: √ stays reachable from every state after the client stops requesting
  load-√reachable : ∀ {s W} → sys l ⟹∖√⟨ s ⟩ W → ∀ {s′ W′} → stop W ⟹∖√⟨ s′ ⟩ W′
                  → Σ[ s″ ∈ List Event ] Σ[ W″ ∈ Tree ] (W′ ⟹∖√⟨ s″ ⟩ W″ × PTree.force W″ ≡ ret tt)
  load-√reachable r with Gen.runE l (SysA l) (sys₀ l) r
  ... | _ , ar , p = StL.reach p (proj₁ (WL.walk ar j1))

  -- the 8 events of the worst case under load (an empty vote list as the notification)
  trL8 : List Event
  trL8 = ⌞ wS lo (pay l FromInitiator MsgLNPRequestNext) ⌟ ∷ ⌞ ap hi lnpSendVotes [] ⌟
       ∷ ⌞ wR lo (pay l FromResponder (MsgLNPVotes [])) ⌟ ∷ ⌞ ap lo lnpRecvVotes [] ⌟
       ∷ ⌞ ap lo lnpSendDone U.tt ⌟ ∷ ⌞ wS lo (pay l FromInitiator MsgLNPQuit) ⌟ ∷ ⌞ dn hi ⌟
       ∷ ⌞ wR lo (pay l FromResponder MsgLNPDone) ⌟ ∷ []

  -- the abstract run of the open system along `trRN1`
  runRN1L : Gen.ARun l (SysA l) (σ₀ l) trRN1 σR
  runRN1L = rE (P1.psL (λ ()) (cRN U.tt)) r0
    where open Gen l (SysA l) using (rE; r0)

  -- the abstract run of `stop` along `trL8`, to the terminated state
  runL8 : Gen.ARun l StL.StopA (σR , U.tt) trL8 (σE , U.tt)
  runL8 = rE (StL.P6.psL (λ ()) (P1.psy U.tt cSR sRN))
        (rτ (StL.P6.pτL (P1.pτL cτB))
        (rτ (StL.P6.pτL (P1.pτR sτB))
        (rE (StL.P6.psL (λ ()) (P1.psR (λ ()) (sAV [])))
        (rE (StL.P6.psL (λ ()) (P1.psy U.tt (cRV []) (sNV [])))
        (rE (StL.P6.psL (λ ()) (P1.psL (λ ()) (cDV [])))
        (rτ (StL.P6.pτL (P1.pτL cτI))
        (rτ (StL.P6.pτL (P1.pτR sτI))
        (rE (StL.P6.psL (λ ()) (P1.psL (λ ()) (cQi U.tt)))
        (rE (StL.P6.psL (λ ()) (P1.psy U.tt cSQ sQi))
        (rτ (StL.P6.pτL (P1.pτL cτQ))
        (rτ (StL.P6.pτL (P1.pτR sτQ))
        (rE (StL.P6.psL (λ ()) (P1.psR (λ ()) sDn))
        (rE (StL.P6.psL (λ ()) (P1.psy U.tt cDn sDS))
         r0)))))))))))))
    where open Gen l StL.StopA using (rE; rτ; r0)

  -- (L) THE BOUND 8 IS TIGHT: after RequestNext is commanded, `stop` has an 8-event run to √
  load-tight : Σ[ W ∈ Tree ] Σ[ W′ ∈ Tree ]
                 (sys l ⟹∖√⟨ trRN1 ⟩ W × stop W ⟹∖√⟨ trL8 ⟩ W′ × length trL8 ≡ 8 × PTree.force W′ ≡ ret tt)
  load-tight = go (GenI.runI l (SysI l) runRN1L (sys₀ l))
    where
    -- the second run, from `stop` of the first run's end
    go : Σ[ W ∈ Tree ] (sys l ⟹∖√⟨ trRN1 ⟩ W × Abs.Pos (SysA l) σR W)
       → Σ[ W ∈ Tree ] Σ[ W′ ∈ Tree ]
           (sys l ⟹∖√⟨ trRN1 ⟩ W × stop W ⟹∖√⟨ trL8 ⟩ W′ × length trL8 ≡ 8 × PTree.force W′ ≡ ret tt)
    go (W , r , p) = go′ (GenI.runI l StL.StopI runL8 (StL.stop₀ p))
      where
      -- the end of the second run has terminated
      go′ : Σ[ W′ ∈ Tree ] (stop W ⟹∖√⟨ trL8 ⟩ W′ × Abs.Pos StL.StopA (σE , U.tt) W′)
          → Σ[ W ∈ Tree ] Σ[ W′ ∈ Tree ]
              (sys l ⟹∖√⟨ trRN1 ⟩ W × stop W ⟹∖√⟨ trL8 ⟩ W′ × length trL8 ≡ 8 × PTree.force W′ ≡ ret tt)
      go′ (W′ , r′ , p′) = W , W′ , r , r′ , refl , AbsI.introR StL.StopI p′ ((U.tt , U.tt) , U.tt)

  ------------------------------------------------------------------------
  -- §7  (X) Contrast: the cancel refused too
  ------------------------------------------------------------------------

  -- `stop` never unsticks a stuck process (`Skip` only waits to terminate jointly)
  stuckStop : ∀ {X : Tree} → IsStuck X → IsStuck (stop X)
  stuckStop {X} stk {τ} st with Par-τ-elim noRN (λ _ _ → tt) X Skip st
  ... | τL _ s _          = stk s
  ... | τR _ (sSil ()) _
  ... | τR _ (sTau () _) _
  stuckStop {X} stk {ev _} st with Par-ev-elim noRN (λ _ _ → tt) X Skip st
  ... | evSync _ s _      = stk s
  ... | evL _ s           = stk s
  ... | evR _ (sVis () _)
  ... | evBoth _ s _      = stk s
  ... | ev√ f _           = stk (sRet f)

  -- (X) WITHOUT THE CANCEL THE BUSY CLIENT NEVER GETS OUT.  With every server api send
  -- refused (`blk`, the cancel included), "RequestNext commanded and sent" reaches a stuck
  -- state (`blk-stall`); the client is in StBusy with no agency, so deciding to stop
  -- requesting changes nothing: `stop` of that state is still stuck.  The cancel is what
  -- makes (N) hold
  blk-stall-stop : Σ[ W ∈ Tree ] (blk l ⟹∖√⟨ trRN l ⟩ W × IsStuck (stop W))
  blk-stall-stop with blk-stall l
  ... | W , r , stk = W , r , stuckStop stk
