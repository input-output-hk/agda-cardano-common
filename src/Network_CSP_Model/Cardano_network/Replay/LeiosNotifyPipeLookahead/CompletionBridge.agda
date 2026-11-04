{-# OPTIONS --guardedness #-}

-- Exact hidden flush counting on actual native paired traces via source step inversion.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.LeiosNotifyPipeLookahead.CompletionBridge (p : Params) (Return : Set) where

open import Data.List using (List; [])
open import Data.List.Relation.Unary.Any using (Any)
open import Data.Bool using (true)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; suc; _+_; _≤_; z≤n)
open import Data.Nat.Properties using (+-identityʳ; +-mono-≤; ≤-trans; n≤1+n; m≤m+n; m≤n+m)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import Cardano_network.Base using (Dir)
open import Cardano_network.Net p using (Link)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications p
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification Return as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverNetwork p Return as Native
import Cardano_network.LeiosNotifyPipeLookahead.CompletionAccounting Notification as Source
import Cardano_network.LeiosNotifyPipeLookahead.CompletionDriver Notification Return as Count
import Cardano_network.LeiosNotifyPipeLookahead.Properties Notification as Control
import Cardano_network.LeiosNotifyPipeLookahead.ShutdownWork Notification Return as DriverOperations
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverNetworkBridge p Return as Bridge
import Cardano_network.Replay.LeiosNotifyPipeLookahead.SchedulingBridge p Return as Scheduling

-- The native callback contract and endpoint coordinates stay fixed across the actual path.
module At (contract : S.Contract) (cl sl : Link) (cd sd : Dir) where
  -- The unchanged native paired tree provides visible records and hidden source scheduling.
  module Tree = Native.At contract cl sl cd sd
  -- Inversion retains every actual native step and its exact source continuation.
  module B = Bridge.At contract cl sl cd sd
  -- This is the existing count of actual native hidden-plus-visible operations.
  module Operations = Scheduling.At contract cl sl cd sd
  open Native using (module LTS; module Traces)

  -- Only a native hidden step whose actual source is server flush contributes a unit.
  flushes : ∀ {s es} {P : Native.Proc} → Tree.tree s Traces.⟹∖√⟨ es ⟩ P → ℕ

  -- Forward-declared tail counting exposes transport of the actual inverted hidden target.
  hidden-tail : ∀ {s es} {P Q : Native.Proc} → P Traces.⟹∖√⟨ es ⟩ Q →
    (Σ[ t ∈ D.State ] (D.Tau contract s t × P ≡ Tree.tree t)) → ℕ

  -- Forward-declared visible counting retains the exact independently decoded row and target.
  visible-tail : ∀ {s e es} {P Q : Native.Proc} → P Traces.⟹∖√⟨ es ⟩ Q →
    (Σ[ row ∈ D.Event ] Σ[ t ∈ D.State ]
      (Tree.decode e ≡ just row × D.Step contract s row t × P ≡ Tree.tree t)) → ℕ

  flushes Traces.∖√-refl = 0
  flushes (Traces.∖√-τ step run) = hidden-tail run (B.hidden-elim step)
  flushes {s = s} (Traces.∖√-ev {e = e} step run) = visible-tail {s = s} {e = e} run (B.visible-elim {s = s} {e = e} step)
  hidden-tail run (t , source , refl) = Count.flush-step source + flushes run
  visible-tail run (row , t , decoded , source , refl) = flushes run

  -- Source reconstruction also certifies equality of independently defined native/source counts.
  record Analysis {s es} {P : Native.Proc} (trace : Tree.tree s Traces.⟹∖√⟨ es ⟩ P) : Set₁ where
    constructor analyzed
    field
      rows : List D.Event
      target : D.State
      matching : B.Matches es rows
      source : D.Run contract s rows target
      same : P ≡ Tree.tree target
      count-agrees : Count.flushes source ≡ flushes trace
  open Analysis public

  -- Every actual native path has an exact source witness and matching flush count.
  analyze : ∀ {s es} {P : Native.Proc} (trace : Tree.tree s Traces.⟹∖√⟨ es ⟩ P) → Analysis trace
  analyze Traces.∖√-refl = analyzed [] _ B.empty D.stop refl refl
  analyze (Traces.∖√-τ step run) with B.hidden-elim step in inverted
  ... | t , sourceStep , refl with analyze run
  ...   | analyzed rows u matches source same count =
    analyzed rows u matches (D.internal sourceStep source) same
      (trans (cong (Count.flush-step sourceStep +_) count) (sym (cong (hidden-tail run) inverted)))
  analyze {s = s} (Traces.∖√-ev {e = e} step run) with B.visible-elim {s = s} {e = e} step in inverted
  ... | row , t , decoded , sourceStep , refl with analyze run
  ...   | analyzed rows u matches source same count =
    analyzed (row Data.List.∷ rows) u (B.matched decoded matches) (D.visible sourceStep source) same
      (trans count (sym (cong (visible-tail {s = s} {e = e} run) inverted)))

  -- Native initial work plus decoded server requests equals actual flushes plus reconstructed work.
  balance : ∀ {s es} {P : Native.Proc} (trace : Tree.tree s Traces.⟹∖√⟨ es ⟩ P) →
    Count.work s + Count.requests (rows (analyze trace)) ≡ flushes trace + Count.work (target (analyze trace))
  balance trace = trans (Count.run-balance (source (analyze trace)))
    (cong (_+ Count.work (target (analyze trace))) (count-agrees (analyze trace)))

  -- Exact reconstructed server closure discharges all source work without tree injectivity.
  closed-flushes : ∀ {s es} {P : Native.Proc} (trace : Tree.tree s Traces.⟹∖√⟨ es ⟩ P) →
    D.serverState (target (analyze trace)) ≡ S.state S.closed 0 S.idle 0 true →
    flushes trace ≡ Count.work s + Count.requests (rows (analyze trace))
  closed-flushes trace closed = trans (sym (count-agrees (analyze trace)))
    (Count.closed-flushes (source (analyze trace)) closed)

  -- A fresh native successful close flushes every decoded server RequestNext exactly once.
  fresh-closed-flushes : ∀ {es} {P : Native.Proc} (trace : Tree.tree D.initial Traces.⟹∖√⟨ es ⟩ P) →
    D.serverState (target (analyze trace)) ≡ S.state S.closed 0 S.idle 0 true →
    flushes trace ≡ Count.requests (rows (analyze trace))
  fresh-closed-flushes = closed-flushes

  -- Every successful post-Quit native schedule flushes exactly its initial source work.
  shutdown-flushes : ∀ {s es} {P : Native.Proc} (trace : Tree.tree s Traces.⟹∖√⟨ es ⟩ P) →
    Control.stopping (S.reader (D.serverState s)) ≡ true →
    D.serverState (target (analyze trace)) ≡ S.state S.closed 0 S.idle 0 true → flushes trace ≡ Count.work s
  shutdown-flushes trace stopping closed = trans (sym (count-agrees (analyze trace)))
    (Count.shutdown-flushes (source (analyze trace)) stopping closed)

  -- Actual native flush occurrences are a subset of actual native operations.
  flushes≤steps : ∀ {s es} {P : Native.Proc} (trace : Tree.tree s Traces.⟹∖√⟨ es ⟩ P) →
    flushes trace ≤ Operations.steps trace

  -- Inverted hidden tails contribute at most the one actual native operation just taken.
  hidden-bound : ∀ {s es} {P Q : Native.Proc} (run : P Traces.⟹∖√⟨ es ⟩ Q)
    (inv : Σ[ t ∈ D.State ] (D.Tau contract s t × P ≡ Tree.tree t)) →
    hidden-tail run inv ≤ suc (Operations.steps run)

  -- Visible tails contribute no flush but still count their real native operation.
  visible-bound : ∀ {s e es} {P Q : Native.Proc} (run : P Traces.⟹∖√⟨ es ⟩ Q)
    (inv : Σ[ row ∈ D.Event ] Σ[ t ∈ D.State ]
      (Tree.decode e ≡ just row × D.Step contract s row t × P ≡ Tree.tree t)) →
    visible-tail {s = s} {e = e} run inv ≤ suc (Operations.steps run)

  flushes≤steps Traces.∖√-refl = z≤n
  flushes≤steps (Traces.∖√-τ step run) = hidden-bound run (B.hidden-elim step)
  flushes≤steps {s = s} (Traces.∖√-ev {e = e} step run) =
    visible-bound {s = s} {e = e} run (B.visible-elim {s = s} {e = e} step)
  hidden-bound run (t , source , refl) = +-mono-≤ (Count.flush-step≤1 source) (flushes≤steps run)
  visible-bound run (row , t , decoded , source , refl) = ≤-trans (flushes≤steps run) (n≤1+n (Operations.steps run))

  -- Existing completed tokens lower-bound every actual native path that successfully closes the server.
  completed-lower-bound : ∀ {s es} {P : Native.Proc} (trace : Tree.tree s Traces.⟹∖√⟨ es ⟩ P) →
    D.serverState (target (analyze trace)) ≡ S.state S.closed 0 S.idle 0 true →
    S.completed (D.serverState s) ≤ Operations.steps trace
  completed-lower-bound {s = s} trace closed = ≤-trans
    (≤-trans (m≤n+m (S.completed (D.serverState s)) (Source.unretired (S.sender (D.serverState s))))
      (m≤n+m (Source.unretired (S.sender (D.serverState s)) + S.completed (D.serverState s)) (S.owed (D.serverState s))))
    (≤-trans (m≤m+n (Count.work s) (Count.requests (rows (analyze trace))))
      (subst (_≤ Operations.steps trace) (closed-flushes trace closed) (flushes≤steps trace)))

  -- Actual decoded Send-Done is enough to discharge the reconstructed closure condition.
  seen-done : ∀ {s es} {P : Native.Proc} (trace : Tree.tree s Traces.⟹∖√⟨ es ⟩ P) →
    Any (λ row → row ≡ D.serverSend D.done) (rows (analyze trace)) →
    D.serverState (target (analyze trace)) ≡ S.state S.closed 0 S.idle 0 true
  seen-done trace observed = Count.seen-done (source (analyze trace)) observed

  -- A fresh native prefix containing server Send-Done has exactly one flush per decoded request.
  recorded-done-flushes : ∀ {es} {P : Native.Proc} (trace : Tree.tree D.initial Traces.⟹∖√⟨ es ⟩ P) →
    Any (λ row → row ≡ D.serverSend D.done) (rows (analyze trace)) →
    flushes trace ≡ Count.requests (rows (analyze trace))
  recorded-done-flushes trace observed = fresh-closed-flushes trace (seen-done trace observed)

  -- Matching-row realization preserves operation counts even when the next row is not yet exposed.
  complete-steps : ∀ {s rows t es} (matching : B.Matches es rows) (run : D.Run contract s rows t) →
    Operations.steps (B.complete matching run) ≡ DriverOperations.steps run
  complete-steps B.empty D.stop = refl
  complete-steps B.empty (D.internal pr run) = cong suc (complete-steps B.empty run)
  complete-steps matching@(B.matched decoded rest) (D.internal pr run) = cong suc (complete-steps matching run)
  complete-steps (B.matched decoded rest) (D.visible pr run) = cong suc (complete-steps rest run)

  -- Canonical realization adds exactly one native step per source operation, with no silent padding.
  realize-steps : ∀ {s rows t} (run : D.Run contract s rows t) →
    Operations.steps (B.realize run) ≡ DriverOperations.steps run
  realize-steps {rows = rows} run = complete-steps (B.canonical-matches rows) run
