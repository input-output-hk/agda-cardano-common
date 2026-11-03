{-# OPTIONS --guardedness #-}

-- Full step correspondence for the existing server PTree over native LNPEv.
-- Readiness API events are retained; this is not yet the wire-only quotient.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.LeiosNotifyPipeLookahead.ServerBridge (p : Params) where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
import Data.Nat.Properties as Nat
open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; length; lookup; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Level using (lift)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Process_Trees using (PTree; ExtI; AnyTypes; ContinueType; ret; react; fin; base; pair)
open import Cardano_network.Base using (Dir)
open import Cardano_network.Net p using (Link)
open import Cardano_network.LeiosNotifyP p using (LNPEv)
import Cardano_network.LeiosNotifyPipeLookahead p as Native
import Cardano_network.LeiosNotifyPipe p as Payloads
import Cardano_network.LeiosNotifyPipeLookahead.ServerEvents p as Events
import Cardano_network.Replay.LeiosNotifyPipeLookahead.ServerEventsBridge p as Encoding
open Native.Reference
import Cardano_network.LeiosNotifyPipeLookahead.Enumeration Payloads.Notification as Enum
import Cardano_network.LeiosNotifyPipeLookahead.Properties Payloads.Notification as Properties
open import Cardano_network.LeiosNotifyPipeLookahead.Selection using (index-complete)
import Semantics.LTS {E = LNPEv} {I = ExtI LNPEv} as LTS
import Semantics.Deadlock {E = LNPEv} {I = ExtI LNPEv} as Traces

-- A fixed contract and endpoint identify one source server instance.
module For (contract : Contract) (l : Link) (d : Dir) where
  open Native.Machine contract l d
  module Canonical = Encoding.For contract l d

  -- Independent source steps cannot start from closed or failed states.
  step-active : ∀ {s a t} → Step contract s a t → active (reader s) ≡ true
  step-active (receiveRequest atFirst) = refl
  step-active (receiveRequest atNext) = refl
  step-active (receiveQuit atFirst) = refl
  step-active (receiveQuit atNext) = refl
  step-active (choose pr _) = pr
  step-active (send pr) = pr
  step-active finish = refl

  -- Every independent hidden source operation has the same active-source property.
  tau-active : ∀ {s t} → Tau s t → active (reader s) ≡ true
  tau-active admitted = refl
  tau-active excessive = refl
  tau-active registered = refl
  tau-active setQuit = refl
  tau-active (claim pr) = pr
  tau-active (cancel pr) = pr
  tau-active (retire pr) = pr
  tau-active flush = refl
  tau-active drained = refl
  tau-active abort = refl

  -- Active native states expose simultaneous visible and hidden offers.
  force-active : ∀ {s} → active (reader s) ≡ true →
    PTree.force (tree s) ≡ react (offers s) (branches s)
  force-active {state first _ _ _ _} _ = refl
  force-active {state admit _ _ _ _} _ = refl
  force-active {state register _ _ _ _} _ = refl
  force-active {state awaitNext _ _ _ _} _ = refl
  force-active {state signalQuit _ _ _ _} _ = refl
  force-active {state flushing _ _ _ _} _ = refl
  force-active {state doneReady _ _ _ _} _ = refl
  force-active {state raising _ _ _ _} _ = refl
  force-active {state closed _ _ _ _} ()
  force-active {state failed _ _ _ _} ()

  -- Inactive states return success or excessiveRequests rather than performing work.
  inactive-return : ∀ {s} → active (reader s) ≡ false →
    Σ[ r ∈ Native.Result ] PTree.force (tree s) ≡ ret r
  inactive-return {state closed _ _ _ _} _ = Native.success , refl
  inactive-return {state failed _ _ _ _} _ = Native.excessiveRequests , refl
  inactive-return {state first _ _ _ _} ()
  inactive-return {state admit _ _ _ _} ()
  inactive-return {state register _ _ _ _} ()
  inactive-return {state awaitNext _ _ _ _} ()
  inactive-return {state signalQuit _ _ _ _} ()
  inactive-return {state flushing _ _ _ _} ()
  inactive-return {state doneReady _ _ _ _} ()
  inactive-return {state raising _ _ _ _} ()

  -- Decode and the independently certified interpreter realize a visible source rule.
  next-complete : ∀ {s e a t} → decode e ≡ just a → Step contract s a t → next s e ≡ just t
  next-complete dec pr rewrite dec = Native.Execute.next-complete pr

  -- Every successful native lookup reconstructs an exact source action and rule.
  next-sound : ∀ {s e t} → next s e ≡ just t →
    Σ[ a ∈ Action ] (decode e ≡ just a × Step contract s a t)
  next-sound {s} {e} eq with decode e in decoded
  ... | nothing with eq
  ...   | ()
  next-sound {s} {e} eq | just a with Native.Execute.lookup contract s a
  ... | nothing with eq
  ...   | ()
  next-sound {s} {e} eq | just a | just (t , pr) with just-injective eq
  ...   | refl = a , refl , pr

  -- Successful target lookup exposes precisely that continuation tree.
  offer-target : ∀ {s e t} → next s e ≡ just t →
    offers s (LTS.Event.A e , LTS.Event.e e) (LTS.Event.a e) ≡ just (tree t)
  offer-target {s} {LTS.evLabel _ _ _} eq rewrite eq = refl

  -- Every source visible step with a native realization is an actual PTree move.
  visible-intro : ∀ {s e a t} → decode e ≡ just a → Step contract s a t →
    tree s LTS.─[ LTS.ev (LTS.evl e) ]─► tree t
  visible-intro {s} {LTS.evLabel X ch value} dec pr =
    LTS.sVis (force-active (step-active pr))
      (offer-target {s = s} {e = LTS.evLabel X ch value}
        (next-complete {e = LTS.evLabel X ch value} dec pr))

  -- A native finite index enumerates exactly one independently certified hidden target.
  internal-index : ∀ {s} (i : Fin (length (internalMoves s))) →
    internalNext s (_ , fin {n = length (internalMoves s)}) (lift i) ≡
      just (proj₁ (lookup (internalMoves s) i))
  internal-index {s} i with length (internalMoves s) Nat.≟ length (internalMoves s)
  ... | yes refl = refl
  ... | no neq = ⊥-elim (neq refl)

  -- Every successful hidden branch decoder retains its source transition certificate.
  internal-sound : ∀ {s at} {value : proj₁ at} {t} → internalNext s at value ≡ just t → Tau s t
  internal-sound {s} {(_ , fin {n = n})} {lift i} eq with n Nat.≟ length (internalMoves s)
  ... | yes refl with just-injective eq
  ...   | refl = proj₂ (lookup (internalMoves s) i)
  internal-sound {s} {(_ , fin {n = n})} {lift i} eq | no _ with eq
  ...   | ()
  internal-sound {at = (_ , base _)} ()
  internal-sound {at = (_ , pair _ _)} ()

  -- Hidden target computation determines the actual tree continuation.
  branch-target : ∀ {s at} {value : proj₁ at} {t} → internalNext s at value ≡ just t →
    branches s at value ≡ just (tree t)
  branch-target {s} {at} {value} eq rewrite eq = refl

  -- Every independent hidden rule has a concrete finite branch in the native PTree.
  hidden-intro : ∀ {s t} → Tau s t → tree s LTS.─[ LTS.τ ]─► tree t
  hidden-intro {s} pr with index-complete (Enum.target-complete pr)
  ... | i , eq = LTS.sTau {i = (_ , fin {n = length (internalMoves s)})} {a = lift i}
    (force-active (tau-active pr)) (branch-target (trans (internal-index i) (cong just eq)))

  -- Native offers retain an explicit target equality rather than tree injectivity.
  offer-elim : ∀ {s e P} →
    offers s (LTS.Event.A e , LTS.Event.e e) (LTS.Event.a e) ≡ just P →
    Σ[ t ∈ State ] (next s e ≡ just t × P ≡ tree t)
  offer-elim {s} {LTS.evLabel X ch value} eq with next s (LTS.evLabel X ch value) in chosen
  ... | nothing with eq
  ...   | ()
  offer-elim {s} {LTS.evLabel X ch value} eq | just t =
    t , refl , sym (just-injective eq)

  -- Every actual hidden continuation reconstructs an independent Tau rule.
  branch-elim : ∀ {s at} {value : proj₁ at} {P} → branches s at value ≡ just P →
    Σ[ t ∈ State ] (Tau s t × P ≡ tree t)
  branch-elim {s} {at} {value} eq with internalNext s at value in chosen
  ... | nothing with eq
  ...   | ()
  branch-elim {s} {at} {value} eq | just t =
    t , internal-sound {s = s} {at = at} {value = value} chosen , sym (just-injective eq)

  -- Returned success/failure nodes cannot emit a nontermination event.
  no-visible-return : ∀ {s r e P} → PTree.force (tree s) ≡ ret r →
    tree s LTS.─[ LTS.ev (LTS.evl e) ]─► P → ⊥
  no-visible-return result (LTS.sVis eq _) with trans (sym result) eq
  ... | ()

  -- Returned success/failure nodes cannot execute either kind of silent LTS step.
  no-hidden-return : ∀ {s r P} → PTree.force (tree s) ≡ ret r →
    tree s LTS.─[ LTS.τ ]─► P → ⊥
  no-hidden-return result (LTS.sSil eq) with trans (sym result) eq
  ... | ()
  no-hidden-return result (LTS.sTau eq _) with trans (sym result) eq
  ... | ()

  -- Inversion at an active source reconstructs the exact decoded visible action.
  visible-active-elim : ∀ {s e P} → active (reader s) ≡ true →
    tree s LTS.─[ LTS.ev (LTS.evl e) ]─► P →
    Σ[ a ∈ Action ] Σ[ t ∈ State ] (decode e ≡ just a × Step contract s a t × P ≡ tree t)
  visible-active-elim {s} {LTS.evLabel X ch value} live (LTS.sVis eq br)
    with trans (sym (force-active live)) eq
  ... | refl with offer-elim {e = LTS.evLabel X ch value} br
  ...   | t , target , same with next-sound {s = s} {e = LTS.evLabel X ch value} target
  ...     | a , decoded , pr = a , t , decoded , pr , same

  -- Every actual native visible step has an independent source-model rule.
  visible-elim : ∀ {s e P} → tree s LTS.─[ LTS.ev (LTS.evl e) ]─► P →
    Σ[ a ∈ Action ] Σ[ t ∈ State ] (decode e ≡ just a × Step contract s a t × P ≡ tree t)
  visible-elim {s} st with active (reader s) in live
  ... | true = visible-active-elim live st
  ... | false with inactive-return live
  ...   | r , result = ⊥-elim (no-visible-return result st)

  -- Active native trees have no sil node; all hidden moves come from their menu.
  hidden-active-elim : ∀ {s P} → active (reader s) ≡ true → tree s LTS.─[ LTS.τ ]─► P →
    Σ[ t ∈ State ] (Tau s t × P ≡ tree t)
  hidden-active-elim live (LTS.sSil eq) with trans (sym (force-active live)) eq
  ... | ()
  hidden-active-elim live (LTS.sTau {i = i} {a = value} eq br)
    with trans (sym (force-active live)) eq
  ... | refl = branch-elim {at = i} {value = value} br

  -- Every actual native hidden move has an independent source-model rule.
  hidden-elim : ∀ {s P} → tree s LTS.─[ LTS.τ ]─► P →
    Σ[ t ∈ State ] (Tau s t × P ≡ tree t)
  hidden-elim {s} st with active (reader s) in live
  ... | true = hidden-active-elim live st
  ... | false with inactive-return live
  ...   | r , result = ⊥-elim (no-hidden-return result st)

  -- Observation preserves every native event and exact decoded action, including APIs.
  data Matches : List LTS.Event → List Action → Set₁ where
    empty : Matches [] []
    matched : ∀ {e a es as} → decode e ≡ just a → Matches es as → Matches (e ∷ es) (a ∷ as)

  -- Every source run with matching native events is an actual native tree run.
  complete : ∀ {s es as t} → Matches es as → Run contract s as t →
    tree s Traces.⟹∖√⟨ es ⟩ tree t
  complete empty stop = Traces.∖√-refl
  complete matches (internal pr run) = Traces.∖√-τ (hidden-intro pr) (complete matches run)
  complete (matched decoded matches) (visible pr run) =
    Traces.∖√-ev (visible-intro decoded pr) (complete matches run)

  -- Every finite native tree run reconstructs exact events, source rules and endpoint.
  sound : ∀ {s es P} → tree s Traces.⟹∖√⟨ es ⟩ P →
    Σ[ as ∈ List Action ] Σ[ t ∈ State ]
      (Matches es as × Run contract s as t × P ≡ tree t)
  sound Traces.∖√-refl = [] , _ , empty , stop , refl
  sound (Traces.∖√-τ pr run) with hidden-elim pr
  ... | t , sourceStep , refl with sound run
  ...   | as , u , matches , source , same = as , u , matches , internal sourceStep source , same
  sound (Traces.∖√-ev pr run) with visible-elim pr
  ... | a , t , decoded , sourceStep , refl with sound run
  ...   | as , u , matches , source , same =
    a ∷ as , u , matched decoded matches , visible sourceStep source , same

  -- Every source action list has matching native events with exact payloads.
  canonical-matches : (as : List Action) → Matches (map (Events.encode l d) as) as
  canonical-matches [] = empty
  canonical-matches (a ∷ as) = matched (Canonical.decode-encode a) (canonical-matches as)

  -- Every source run has a native execution without an extra event-realizability premise.
  realize : ∀ {s as t} → Run contract s as t →
    tree s Traces.⟹∖√⟨ map (Events.encode l d) as ⟩ tree t
  realize {as = as} source = complete (canonical-matches as) source

  -- Successful and abnormal native returns retain the source reader's terminal phase.
  data Returned : State → Native.Result → Set where
    successful : ∀ {w sender c q} → Returned (state closed w sender c q) Native.success
    excessiveFailure : ∀ {w sender c q} → Returned (state failed w sender c q) Native.excessiveRequests

  -- The separate CSP termination tick cannot confuse admission failure with success.
  return-elim : ∀ {s result P} → tree s LTS.─[ LTS.ev (LTS.√ result) ]─► P → Returned s result
  return-elim {state closed _ _ _ _} (LTS.sRet refl) = successful
  return-elim {state failed _ _ _ _} (LTS.sRet refl) = excessiveFailure
  return-elim {state first _ _ _ _} (LTS.sRet ())
  return-elim {state admit _ _ _ _} (LTS.sRet ())
  return-elim {state register _ _ _ _} (LTS.sRet ())
  return-elim {state awaitNext _ _ _ _} (LTS.sRet ())
  return-elim {state signalQuit _ _ _ _} (LTS.sRet ())
  return-elim {state flushing _ _ _ _} (LTS.sRet ())
  return-elim {state doneReady _ _ _ _} (LTS.sRet ())
  return-elim {state raising _ _ _ _} (LTS.sRet ())

  -- A canonical native event recovers its exact source action without an existential label.
  canonical-step : ∀ {s a P} → tree s LTS.─[ LTS.ev (LTS.evl (Events.encode l d a)) ]─► P →
    Σ[ t ∈ State ] (Step contract s a t × P ≡ tree t)
  canonical-step {a = a} st with visible-elim st
  ... | a′ , t , decoded , pr , same
    with just-injective (trans (sym (Canonical.decode-encode a)) decoded)
  ... | refl = t , pr , same

  -- Reader shutdown forbids a new RequestNext record in the actual native PTree.
  no-request-after-shutdown-native : ∀ {s P} → Properties.stopping (reader s) ≡ true →
    tree s LTS.─[ LTS.ev (LTS.evl (Events.encode l d recvRequest)) ]─► P → ⊥
  no-request-after-shutdown-native stopped st with canonical-step st
  ... | t , pr , same = Properties.no-request-after-quit stopped pr

  -- A native Send preserves the exact payload already stored in its sender state.
  selected-payload-native : ∀ {s reply P} →
    tree s LTS.─[ LTS.ev (LTS.evl (Events.encode l d (sendReply reply))) ]─► P →
    sender s ≡ selected reply
  selected-payload-native st with canonical-step st
  ... | t , pr , same = Properties.selected-payload-retained pr

  -- Native wire Done requires the true flag and no waiting, active or completed work.
  done-only-drained-native : ∀ {s P} →
    tree s LTS.─[ LTS.ev (LTS.evl (Events.encode l d sendDone)) ]─► P →
    s ≡ state doneReady 0 idle 0 true
  done-only-drained-native st with canonical-step st
  ... | t , pr , same = Properties.done-only-drained pr
