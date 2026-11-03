{-# OPTIONS --guardedness #-}

-- Both finite trace directions for the native client with explicit callback erasure.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.LeiosNotifyPipeLookahead.ClientNetworkBridge (p : Params) (Return : Set) where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Process_Trees using (PTree; ret; react)
open import Cardano_network.Base using (Dir)
open import Cardano_network.Net p using (Link)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications p
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification Return as C
import Cardano_network.LeiosNotifyPipeLookahead.ClientTree Notification Return notificationEq as Source
import Cardano_network.LeiosNotifyPipeLookahead.ClientExecution Notification Return notificationEq as Exec
import Cardano_network.LeiosNotifyPipeLookahead.ClientNetwork p Return as N
import Cardano_network.LeiosNotifyPipeLookahead.ClientEvents p Return N.Branches as E
import Cardano_network.Replay.LeiosNotifyPipeLookahead.ClientEventsBridge p Return as Encoding
open N using (module LTS; module Traces)

-- Endpoint-local correspondence retains exact states and the chosen termination value.
module At (l : Link) (d : Dir) where
  open N.At l d
  module Canonical = Encoding.At l d

  -- Live source states unfold to simultaneous visible and internal native offers.
  force-live : ∀ {s} → Source.outcome s ≡ nothing →
    PTree.force (tree s) ≡ react (offers s) (branches s)
  force-live {s} eq rewrite eq = refl

  -- A native return exposes precisely the stored source outcome.
  force-result : ∀ {s value} → Source.outcome s ≡ just value → PTree.force (tree s) ≡ ret value
  force-result {s} eq rewrite eq = refl

  -- Every decoded visible source step is implemented by the native lookup.
  next-complete : ∀ {s e a t} → decode e ≡ just a → C.Step s a t → next s e ≡ just t
  next-complete decoded pr rewrite decoded = Exec.next-complete pr

  -- Successful lookup reconstructs an exact decoded source action and certificate.
  next-sound : ∀ {s e t} → next s e ≡ just t →
    Σ[ a ∈ C.Action ] (decode e ≡ just a × C.Step s a t)
  next-sound {s} {e} eq with decode e
  ... | nothing with eq
  ...   | ()
  next-sound {s} {e} eq | just a with Exec.lookup a s
  ... | nothing with eq
  ...   | ()
  next-sound {s} {e} eq | just a | just (t , pr) with just-injective eq
  ... | refl = a , refl , pr

  -- A native visible lookup determines its exact coinductive continuation.
  offer-target : ∀ {s e t} → next s e ≡ just t →
    offers s (LTS.Event.A e , LTS.Event.e e) (LTS.Event.a e) ≡ just (tree t)
  offer-target {s} {LTS.evLabel _ _ _} eq rewrite eq = refl

  -- Every visible operational rule with a native event becomes a real PTree step.
  visible-intro : ∀ {s e a t} → decode e ≡ just a → C.Step s a t →
    tree s LTS.─[ LTS.ev (LTS.evl e) ]─► tree t
  visible-intro {s} {LTS.evLabel X ch value} decoded pr =
    LTS.sVis (force-live (Source.step-live pr))
      (offer-target {s = s} {e = LTS.evLabel X ch value}
        (next-complete {e = LTS.evLabel X ch value} decoded pr))

  -- A checked scheduler selector determines its exact native continuation.
  branch-target : ∀ {s choice t} {pr : N.Tau s t} → N.hidden s choice ≡ just (t , pr) →
    branches s (_ , N.schedule) choice ≡ just (tree t)
  branch-target {s} {choice} eq rewrite eq = refl

  -- Every source scheduling or declared callback step becomes a real native tau.
  hidden-intro : ∀ {s t} → N.Tau s t → tree s LTS.─[ LTS.τ ]─► tree t
  hidden-intro {s} pr with N.hidden-complete pr
  ... | choice , eq with N.hidden s choice in chosen | eq
  ...   | nothing | ()
  ...   | just (t , _) | refl = LTS.sTau {i = (_ , N.schedule)} {a = choice}
    (force-live (N.tau-live pr)) (branch-target {s = s} {choice = choice} chosen)

  -- Invert a native visible continuation without assuming tree injectivity.
  offer-elim : ∀ {s e P} →
    offers s (LTS.Event.A e , LTS.Event.e e) (LTS.Event.a e) ≡ just P →
    Σ[ t ∈ C.State ] (next s e ≡ just t × P ≡ tree t)
  offer-elim {s} {LTS.evLabel X ch value} eq with next s (LTS.evLabel X ch value)
  ... | nothing with eq
  ...   | ()
  offer-elim {s} {LTS.evLabel X ch value} eq | just t = t , refl , sym (just-injective eq)

  -- Invert a native internal continuation and retain its independent source certificate.
  branch-elim : ∀ {s at} {choice : proj₁ at} {P} → branches s at choice ≡ just P →
    Σ[ t ∈ C.State ] (N.Tau s t × P ≡ tree t)
  branch-elim {s} {(_ , N.schedule)} {choice} eq with N.hidden s choice
  ... | nothing with eq
  ...   | ()
  branch-elim {s} {(_ , N.schedule)} {choice} eq | just (t , pr) =
    t , pr , sym (just-injective eq)

  -- A returned native client cannot emit another network or API event.
  no-visible-return : ∀ {s value e P} → PTree.force (tree s) ≡ ret value →
    tree s LTS.─[ LTS.ev (LTS.evl e) ]─► P → ⊥
  no-visible-return result (LTS.sVis eq _) with trans (sym result) eq
  ... | ()

  -- A returned native client cannot continue driver work or callback selection.
  no-hidden-return : ∀ {s value P} → PTree.force (tree s) ≡ ret value → tree s LTS.─[ LTS.τ ]─► P → ⊥
  no-hidden-return result (LTS.sSil eq) with trans (sym result) eq
  ... | ()
  no-hidden-return result (LTS.sTau eq _) with trans (sym result) eq
  ... | ()

  -- Every actual native visible step reconstructs one exact source action and target.
  visible-elim : ∀ {s e P} → tree s LTS.─[ LTS.ev (LTS.evl e) ]─► P →
    Σ[ a ∈ C.Action ] Σ[ t ∈ C.State ] (decode e ≡ just a × C.Step s a t × P ≡ tree t)
  visible-elim {s} st with Source.outcome s in outcome
  ... | just value = ⊥-elim (no-visible-return (force-result outcome) st)
  ... | nothing with st
  ...   | LTS.sVis {at = (X , ch)} {a = value} eq br with trans (sym (force-live outcome)) eq
  ...     | refl with offer-elim {s = s} {e = LTS.evLabel X ch value} br
  ...       | t , target , same with next-sound {s = s} {e = LTS.evLabel X ch value} target
  ...         | a , decoded , pr = a , t , decoded , pr , same

  -- Every actual native tau reconstructs driver scheduling or a declared erased callback.
  hidden-elim : ∀ {s P} → tree s LTS.─[ LTS.τ ]─► P →
    Σ[ t ∈ C.State ] (N.Tau s t × P ≡ tree t)
  hidden-elim {s} st with Source.outcome s in outcome
  ... | just value = ⊥-elim (no-hidden-return (force-result outcome) st)
  ... | nothing with st
  ...   | LTS.sSil eq with trans (sym (force-live outcome)) eq
  ...     | ()
  hidden-elim {s} st | nothing | LTS.sTau {i = i} {a = choice} eq br
    with trans (sym (force-live outcome)) eq
  ... | refl = branch-elim {at = i} {choice = choice} br

  -- Observation erases only checkDone and successful generic Canceled handler actions.
  data Matches : List LTS.Event → List C.Action → Set₁ where
    empty : Matches [] []
    quiet : ∀ {a es as} → E.Hidden a → Matches es as → Matches es (a ∷ as)
    emitted : ∀ {e a es as} → decode e ≡ just a → Matches es as → Matches (e ∷ es) (a ∷ as)

  -- Every matching source run becomes an actual native network/API execution.
  complete : ∀ {s es as t} → Matches es as → C.Run s as t → tree s Traces.⟹∖√⟨ es ⟩ tree t
  complete empty C.stop = Traces.∖√-refl
  complete matches (C.internal pr run) = Traces.∖√-τ (hidden-intro (N.scheduled pr)) (complete matches run)
  complete (quiet h matches) (C.visible pr run) = Traces.∖√-τ (hidden-intro (N.callback h pr)) (complete matches run)
  complete (emitted decoded matches) (C.visible pr run) = Traces.∖√-ev (visible-intro decoded pr) (complete matches run)

  -- Every finite native trace has an operational witness with explicit erased decisions.
  sound : ∀ {s es P} → tree s Traces.⟹∖√⟨ es ⟩ P →
    Σ[ as ∈ List C.Action ] Σ[ t ∈ C.State ] (Matches es as × C.Run s as t × P ≡ tree t)
  sound Traces.∖√-refl = [] , _ , empty , C.stop , refl
  sound (Traces.∖√-τ pr run) with hidden-elim pr
  ... | t , N.scheduled sourceStep , refl with sound run
  ...   | as , u , matches , source , same = as , u , matches , C.internal sourceStep source , same
  sound (Traces.∖√-τ pr run) | t , N.callback {a = a} h sourceStep , refl with sound run
  ... | as , u , matches , source , same = a ∷ as , u , quiet h matches , C.visible sourceStep source , same
  sound (Traces.∖√-ev pr run) with visible-elim pr
  ... | a , t , decoded , sourceStep , refl with sound run
  ...   | as , u , matches , source , same = a ∷ as , u , emitted decoded matches , C.visible sourceStep source , same

  -- Canonical realization discharges observation premises for every source action list.
  canonical-matches : (as : List C.Action) → Matches (project as) as
  canonical-matches [] = empty
  canonical-matches (a ∷ as) with Canonical.view a
  ... | Canonical.quiet h erased rewrite erased = quiet h (canonical-matches as)
  ... | Canonical.emitted e observed decoded rewrite observed = emitted decoded (canonical-matches as)

  -- Every source run is realizable over LNPEv with precisely the declared callback erasure.
  realize : ∀ {s as t} → C.Run s as t → tree s Traces.⟹∖√⟨ project as ⟩ tree t
  realize {as = as} source = complete (canonical-matches as) source

  -- The separate CSP return tick retains the original exact checkDone return value.
  return-elim : ∀ {s value P} → tree s LTS.─[ LTS.ev (LTS.√ value) ]─► P → Source.outcome s ≡ just value
  return-elim {s} st with Source.outcome s in outcome
  ... | just value with st
  ...   | LTS.sRet eq with trans (sym (force-result outcome)) eq
  ...     | refl = refl
  return-elim {s} st | nothing with st
  ... | LTS.sRet eq with trans (sym (force-live outcome)) eq
  ...   | ()
