{-# OPTIONS --guardedness #-}

-- Native phase-step introduction/inversion for the bounded Notify peers.
open import Cardano_network.Params using (Params)
open import Data.Nat using (ℕ)
open import Cardano_network.Base using (Dir)
import Cardano_network.Net
module Cardano_network.Replay.LeiosNotifyPipeParts
  (p : Params) (k : ℕ) (l : Cardano_network.Net.Link p) (d : Dir) where

open import Cardano_network.Net p
open import Cardano_network.LeiosNotifyP p using (LNPEv)
open import Cardano_network.LeiosNotifyPipe p
open Machine k l d
open import Process_Trees using (ExtI)
open import Cardano_network.Data p
open import Data.Nat using (_<ᵇ_)
open import Data.Bool using (true)
import Data.Bool.Properties as Bool
open import Relation.Nullary.Decidable using (_×-dec_)
open import Data.Empty using (⊥-elim)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Nullary using (yes; no)
open import Class.DecEq using (_≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
import Semantics.LTS {E = LNPEv} {I = ExtI LNPEv} as LTS

-- A successful target lookup retains its independent transition certificate.
selected : ∀ {r s e t} → next r s e ≡ just t → Step r s e t
selected {r} {s} {e} pr with select r s e
... | nothing with () ← pr
... | just (t , st) with refl ← pr = st

-- Every independent phase step is offered by the executable lookup.
next-complete : ∀ {r s e t} → Step r s e t → next r s e ≡ just t
next-complete (cRequest {n} credit) = checked-target ((l ≟ l) ×-dec ((d ≟ d) ×-dec ((n <ᵇ k) Bool.≟ true)))
  (refl , refl , credit)
next-complete cDone = checked-target ((l ≟ l) ×-dec (d ≟ d))
  (refl , refl)
next-complete (cNotification (announcement h)) = checked-target ((l ≟ l) ×-dec (d ≟ d))
  (refl , refl)
next-complete (cNotification (offer pt sz)) = checked-target ((l ≟ l) ×-dec (d ≟ d))
  (refl , refl)
next-complete (cNotification (txsOffer pt)) = checked-target ((l ≟ l) ×-dec (d ≟ d))
  (refl , refl)
next-complete (cNotification (votes vs)) = checked-target ((l ≟ l) ×-dec (d ≟ d))
  (refl , refl)
next-complete (sRequest {n} credit) = checked-target ((l ≟ l) ×-dec ((d ≟ d) ×-dec ((n <ᵇ k) Bool.≟ true)))
  (refl , refl , credit)
next-complete sDone = checked-target ((l ≟ l) ×-dec (d ≟ d))
  (refl , refl)
next-complete sAnnouncement = checked-target ((l ≟ l) ×-dec (d ≟ d))
  (refl , refl)
next-complete sOffer = checked-target ((l ≟ l) ×-dec (d ≟ d))
  (refl , refl)
next-complete sTxsOffer = checked-target ((l ≟ l) ×-dec (d ≟ d))
  (refl , refl)
next-complete sVotes = checked-target ((l ≟ l) ×-dec (d ≟ d))
  (refl , refl)
next-complete (sent {md = md} {m = m}) = checked-target ((l ≟ l) ×-dec ((d ≟ d) ×-dec (packet md m ≟ packet md m)))
  (refl , refl , refl)
next-complete (delivered {m = m}) with tag m ≟ tag m
... | no np = ⊥-elim (np refl)
... | yes refl = checked-target ((l ≟ l) ×-dec ((d ≟ d) ×-dec (_≟_ ⦃ deliveryEq m ⦄ (value m) (value m))))
  (refl , refl , refl)
next-complete noticed = checked-target ((l ≟ l) ×-dec (d ≟ d))
  (refl , refl)

-- The guarded offer map realizes each successful native target lookup.
offered : ∀ {r s t X} {ch : LNPEv X} {a} → next r s (LTS.evLabel X ch a) ≡ just t →
  offers r s (X , ch) a ≡ just (tree r t)
offered {r} {s} {t} {X} {ch} {a} eq rewrite eq = refl

-- Each executable target becomes the corresponding actual visible PTree move.
fire : ∀ {r s e t} → Step r s e t → tree r s LTS.─[ LTS.ev (LTS.evl e) ]─► tree r t
fire {r} {s = s@(head (openN _))} {e = LTS.evLabel X ch a} st =
  LTS.sVis refl (offered {r = r} {s = s} {X = X} {ch = ch} {a = a} (next-complete st))
fire {s = head closed} ()
fire {s = loopBack _} ()
fire {r} {s = s@(sending _ _ _)} {e = LTS.evLabel X ch a} st =
  LTS.sVis refl (offered {r = r} {s = s} {X = X} {ch = ch} {a = a} (next-complete st))
fire {r} {s = s@(delivering _ _)} {e = LTS.evLabel X ch a} st =
  LTS.sVis refl (offered {r = r} {s = s} {X = X} {ch = ch} {a = a} (next-complete st))
fire {r} {s = s@(doneNotice)} {e = LTS.evLabel X ch a} st =
  LTS.sVis refl (offered {r = r} {s = s} {X = X} {ch = ch} {a = a} (next-complete st))

-- Lookup inversion supplies both the original phase step and final tree equality.
lookup-inv : ∀ {r s T X} {ch : LNPEv X} {a} → offers r s (X , ch) a ≡ just T →
  Σ[ t ∈ Phase ] (Step r s (LTS.evLabel X ch a) t × T ≡ tree r t)
lookup-inv {r} {s} {T} {X} {ch} {a} pr with next r s (LTS.evLabel X ch a) in eq
... | nothing with () ← pr
... | just t = t , selected eq , sym (just-injective pr)

-- Actual visible moves introduce no transitions beyond the native phase rules.
visible-inv : ∀ {r s e T} → tree r s LTS.─[ LTS.ev (LTS.evl e) ]─► T →
  Σ[ t ∈ Phase ] (Step r s e t × T ≡ tree r t)
visible-inv {s = head (openN _)} (LTS.sVis refl pr) = lookup-inv pr
visible-inv {s = head closed} (LTS.sVis () _)
visible-inv {s = loopBack _} (LTS.sVis () _)
visible-inv {s = sending _ _ _} (LTS.sVis refl pr) = lookup-inv pr
visible-inv {s = delivering _ _} (LTS.sVis refl pr) = lookup-inv pr
visible-inv {s = doneNotice} (LTS.sVis refl pr) = lookup-inv pr

-- Loop-back is the sole native silent transition.
tau-fire : ∀ {r s t} → Tau s t → tree r s LTS.─[ LTS.τ ]─► tree r t
tau-fire back = LTS.sSil refl

-- Invert silent moves without any extensional equality of coinductive trees.
tau-inv : ∀ {r s T} → tree r s LTS.─[ LTS.τ ]─► T →
  Σ[ t ∈ Phase ] (Tau s t × T ≡ tree r t)
tau-inv {s = loopBack s} (LTS.sSil refl) = head s , back , refl
tau-inv {s = loopBack _} (LTS.sTau () _)
tau-inv {s = head (openN _)} (LTS.sSil ())
tau-inv {s = head (openN _)} (LTS.sTau refl ())
tau-inv {s = head closed} (LTS.sSil ())
tau-inv {s = head closed} (LTS.sTau () _)
tau-inv {s = sending _ _ _} (LTS.sSil ())
tau-inv {s = sending _ _ _} (LTS.sTau refl ())
tau-inv {s = delivering _ _} (LTS.sSil ())
tau-inv {s = delivering _ _} (LTS.sTau refl ())
tau-inv {s = doneNotice} (LTS.sSil ())
tau-inv {s = doneNotice} (LTS.sTau refl ())
