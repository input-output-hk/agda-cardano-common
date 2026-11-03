{-# OPTIONS --guardedness #-}

-- Both native paired prefix trace directions for the independent driver product.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverNetworkBridge (p : Params) (Return : Set) where

open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Cardano_network.Base using (Dir)
open import Cardano_network.Net p using (Link)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications p
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification Return as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverExecution Notification Return notificationEq as Exec
import Cardano_network.LeiosNotifyPipeLookahead.DriverNetwork p Return as N
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverEventsBridge p Return as Encoding
open N using (module LTS; module Traces)

-- The callback contract and endpoint coordinates are unchanged throughout each run.
module At (contract : S.Contract) (cl sl : Link) (cd sd : Dir) where
  open N.At contract cl sl cd sd
  module Canonical = Encoding.At contract cl sl cd sd

  -- Every visible paired source step has the same native target after decoding.
  next-complete : ∀ {s e row t} → decode e ≡ just row → D.Step contract s row t → next s e ≡ just t
  next-complete decoded pr rewrite decoded = Exec.next-complete pr

  -- Native visible lookup reconstructs an exact source row and independent certificate.
  next-sound : ∀ {s e t} → next s e ≡ just t →
    Σ[ row ∈ D.Event ] (decode e ≡ just row × D.Step contract s row t)
  next-sound {s} {e} eq with decode e
  ... | nothing with eq
  ...   | ()
  next-sound {s} {e} eq | just row with Exec.lookup contract row s
  ... | nothing with eq
  ...   | ()
  next-sound {s} {e} eq | just row | just (t , pr) with just-injective eq
  ... | refl = row , refl , pr

  -- A visible target equality determines the exact coinductive continuation.
  offer-target : ∀ {s e t} → next s e ≡ just t →
    offers s (LTS.Event.A e , LTS.Event.e e) (LTS.Event.a e) ≡ just (tree t)
  offer-target {s} {LTS.evLabel _ _ _} eq rewrite eq = refl

  -- Every independently specified record emission becomes a real native PTree step.
  visible-intro : ∀ {s e row t} → decode e ≡ just row → D.Step contract s row t →
    tree s LTS.─[ LTS.ev (LTS.evl e) ]─► tree t
  visible-intro {s} {LTS.evLabel X channel value} decoded pr = LTS.sVis refl
    (offer-target {s = s} {e = LTS.evLabel X channel value}
      (next-complete {e = LTS.evLabel X channel value} decoded pr))

  -- A checked hidden selector determines exactly the selected product continuation.
  branch-target : ∀ {s choice t} {pr : D.Tau contract s t} →
    Exec.hidden contract s choice ≡ just (t , pr) →
    branches s (_ , N.schedule) choice ≡ just (tree t)
  branch-target {s} {choice} eq rewrite eq = refl

  -- Commits, decode, callbacks and endpoint scheduling all have native hidden moves.
  hidden-intro : ∀ {s t} → D.Tau contract s t → tree s LTS.─[ LTS.τ ]─► tree t
  hidden-intro {s} pr with Exec.hidden-complete pr
  ... | choice , eq with Exec.hidden contract s choice in chosen | eq
  ...   | nothing | ()
  ...   | just (t , _) | refl = LTS.sTau {i = (_ , N.schedule)} {a = choice} refl
    (branch-target {s = s} {choice = choice} chosen)

  -- Native offers retain source state equality without any tree-injectivity assumption.
  offer-elim : ∀ {s e P} →
    offers s (LTS.Event.A e , LTS.Event.e e) (LTS.Event.a e) ≡ just P →
    Σ[ t ∈ D.State ] (next s e ≡ just t × P ≡ tree t)
  offer-elim {s} {LTS.evLabel X channel value} eq with next s (LTS.evLabel X channel value)
  ... | nothing with eq
  ...   | ()
  offer-elim {s} {LTS.evLabel X channel value} eq | just t = t , refl , sym (just-injective eq)

  -- Every native scheduler branch retains its independent product transition evidence.
  branch-elim : ∀ {s at} {choice : proj₁ at} {P} → branches s at choice ≡ just P →
    Σ[ t ∈ D.State ] (D.Tau contract s t × P ≡ tree t)
  branch-elim {s} {(_ , N.schedule)} {choice} eq with Exec.hidden contract s choice
  ... | nothing with eq
  ...   | ()
  branch-elim {s} {(_ , N.schedule)} {choice} eq | just (t , pr) = t , pr , sym (just-injective eq)

  -- Every actual native record step reconstructs a source row with the same endpoint.
  visible-elim : ∀ {s e P} → tree s LTS.─[ LTS.ev (LTS.evl e) ]─► P →
    Σ[ row ∈ D.Event ] Σ[ t ∈ D.State ] (decode e ≡ just row × D.Step contract s row t × P ≡ tree t)
  visible-elim {s} {LTS.evLabel X channel value} (LTS.sVis refl br)
    with offer-elim {s = s} {e = LTS.evLabel X channel value} br
  ... | t , target , same with next-sound {s = s} {e = LTS.evLabel X channel value} target
  ...   | row , decoded , pr = row , t , decoded , pr , same

  -- The reactive native product has no sil node and invents no hidden transitions.
  hidden-elim : ∀ {s P} → tree s LTS.─[ LTS.τ ]─► P →
    Σ[ t ∈ D.State ] (D.Tau contract s t × P ≡ tree t)
  hidden-elim (LTS.sSil ())
  hidden-elim (LTS.sTau {i = i} {a = choice} refl br) = branch-elim {at = i} {choice = choice} br

  -- Every retained native row has one corresponding source row; nothing is dropped.
  data Matches : List LTS.Event → List D.Event → Set₁ where
    empty : Matches [] []
    matched : ∀ {e row es rows} → decode e ≡ just row → Matches es rows → Matches (e ∷ es) (row ∷ rows)

  -- Every source execution with matching native rows is a real paired PTree execution.
  complete : ∀ {s es rows t} → Matches es rows → D.Run contract s rows t →
    tree s Traces.⟹∖√⟨ es ⟩ tree t
  complete empty D.stop = Traces.∖√-refl
  complete matches (D.internal pr run) = Traces.∖√-τ (hidden-intro pr) (complete matches run)
  complete (matched decoded matches) (D.visible pr run) = Traces.∖√-ev (visible-intro decoded pr) (complete matches run)

  -- Every actual native paired trace reconstructs source records and the exact product state.
  sound : ∀ {s es P} → tree s Traces.⟹∖√⟨ es ⟩ P →
    Σ[ rows ∈ List D.Event ] Σ[ t ∈ D.State ] (Matches es rows × D.Run contract s rows t × P ≡ tree t)
  sound Traces.∖√-refl = [] , _ , empty , D.stop , refl
  sound (Traces.∖√-τ pr run) with hidden-elim pr
  ... | t , sourceStep , refl with sound run
  ...   | rows , u , matches , source , same = rows , u , matches , D.internal sourceStep source , same
  sound (Traces.∖√-ev pr run) with visible-elim pr
  ... | row , t , decoded , sourceStep , refl with sound run
  ...   | rows , u , matches , source , same = row ∷ rows , u , matched decoded matches , D.visible sourceStep source , same

  -- Every exact source record list has a canonical native full-packet realization.
  canonical-matches : ∀ rows → Matches (map encode rows) rows
  canonical-matches [] = empty
  canonical-matches (row ∷ rows) = matched (Canonical.decode-encode row) (canonical-matches rows)

  -- Source runs require no extra native-field realization premise.
  realize : ∀ {s rows t} → D.Run contract s rows t → tree s Traces.⟹∖√⟨ map encode rows ⟩ tree t
  realize {rows = rows} run = complete (canonical-matches rows) run
