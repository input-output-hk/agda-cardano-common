{-# OPTIONS --guardedness #-}

-- Exact two-sided full-policy native correspondence; wire observations alone
-- do not establish the external forecast, governor or application-input facts.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.LeiosNotifyPipeLookahead.NodeDriverNetworkBridge (p : Params) where

open import Data.List using (List; []; _∷_; map; mapMaybe)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁)
open import Data.Unit using (⊤)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Cardano_network.Base using (Dir)
open import Cardano_network.Net p using (Link)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications p using (Notification; notificationEq)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverModel Notification as Node
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverExecution Notification notificationEq as Exec
import Cardano_network.LeiosNotifyPipeLookahead.NodeScheduling Notification as Scheduling
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverNetwork p as N
import Cardano_network.LeiosNotifyPipeLookahead.DriverNetwork p ⊤ as NativeWire
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverEventsBridge p ⊤ as WireEncoding
open N using (module LTS; module Traces)

-- Every theorem fixes the same two endpoint coordinates and the unchanged node policy.
module At (cl sl : Link) (cd sd : Dir) where
  open N.At cl sl cd sd
  module Wire = WireEncoding.At S.nodeNext cl sl cd sd
  module Raw = NativeWire.At S.nodeNext cl sl cd sd

  -- Wrapping an existing wire event changes only the outer policy alphabet tag.
  wire-decode : ∀ event → decode (wireEvent event) ≡ Data.Maybe.map Node.wire (Raw.decode event)
  wire-decode (NativeWire.LTS.evLabel _ _ _) = refl

  -- Canonical encoding retains every policy action and every complete native wire packet.
  decode-encode : ∀ input → decode (encode input) ≡ just input
  decode-encode (Node.wire row)
    rewrite wire-decode (Raw.encode row) | Wire.decode-encode row = refl
  decode-encode (Node.setForecast _) = refl
  decode-encode (Node.setTerminate _) = refl
  decode-encode (Node.eligible _) = refl
  decode-encode (Node.handledNormal _) = refl
  decode-encode Node.rejectedCancel = refl

  -- Each independent full-policy action computes to exactly its original source target.
  next-complete : ∀ {s e input t} → decode e ≡ just input → Node.Step s input t → next s e ≡ just t
  next-complete decoded proof rewrite decoded = Exec.visible-complete proof

  -- Successful next-state selection reconstructs actual source action evidence.
  next-sound : ∀ {s e t} → next s e ≡ just t →
    Σ[ input ∈ Node.Action ] (decode e ≡ just input × Node.Step s input t)
  next-sound {s} {e} same with decode e
  ... | nothing with same
  ...   | ()
  next-sound {s} {e} same | just input with Exec.visible-step s input
  ... | nothing with same
  ...   | ()
  next-sound {s} {e} same | just input | just (t , proof) with just-injective same
  ... | refl = input , refl , proof

  -- Visible continuation equality retains the entire concrete node-policy state.
  offer-target : ∀ {s e t} → next s e ≡ just t →
    offers s (LTS.Event.A e , LTS.Event.e e) (LTS.Event.a e) ≡ just (tree t)
  offer-target {s} {LTS.evLabel _ _ _} same rewrite same = refl

  -- Source action introduction uses the original wire or explicit input event.
  visible-intro : ∀ {s e input t} → decode e ≡ just input → Node.Step s input t →
    tree s LTS.─[ LTS.ev (LTS.evl e) ]─► tree t
  visible-intro {s} {LTS.evLabel A channel value} decoded proof = LTS.sVis refl
    (offer-target {s = s} {e = LTS.evLabel A channel value}
      (next-complete {s = s} {e = LTS.evLabel A channel value} decoded proof))

  -- A concrete scheduling selector carries its certified node transition target.
  branch-target : ∀ {s choice t} {proof : Node.Tau s t} →
    Exec.hidden-step s choice ≡ just (t , proof) →
    branches s (_ , N.schedule) choice ≡ just (tree t)
  branch-target {s} {choice} same rewrite same = refl

  -- Completeness covers every hidden policy rule, not merely generic transport.
  hidden-intro : ∀ {s t} → Node.Tau s t → tree s LTS.─[ LTS.τ ]─► tree t
  hidden-intro {s} proof with Exec.hidden-complete proof
  ... | choice , same with Exec.hidden-step s choice in chosen | same
  ...   | nothing | ()
  ...   | just (t , _) | refl = LTS.sTau {i = (_ , N.schedule)} {a = choice} refl
    (branch-target {s = s} {choice = choice} chosen)

  -- Inverting offers never assumes injectivity of coinductive tree construction.
  offer-elim : ∀ {s e P} →
    offers s (LTS.Event.A e , LTS.Event.e e) (LTS.Event.a e) ≡ just P →
    Σ[ t ∈ Node.State ] (next s e ≡ just t × P ≡ tree t)
  offer-elim {s} {LTS.evLabel A channel value} same with next s (LTS.evLabel A channel value)
  ... | nothing with same
  ...   | ()
  offer-elim {s} {LTS.evLabel A channel value} same | just t = t , refl , sym (just-injective same)

  -- Every actual scheduler branch reconstructs its independent full-policy rule.
  branch-elim : ∀ {s at} {choice : proj₁ at} {P} → branches s at choice ≡ just P →
    Σ[ t ∈ Node.State ] (Node.Tau s t × P ≡ tree t)
  branch-elim {s} {(_ , N.schedule)} {choice} same with Exec.hidden-step s choice
  ... | nothing with same
  ...   | ()
  branch-elim {s} {(_ , N.schedule)} {choice} same | just (t , proof) =
    t , proof , sym (just-injective same)

  -- No actual native visible step can omit its policy action or original target.
  visible-elim : ∀ {s e P} → tree s LTS.─[ LTS.ev (LTS.evl e) ]─► P →
    Σ[ input ∈ Node.Action ] Σ[ t ∈ Node.State ]
      (decode e ≡ just input × Node.Step s input t × P ≡ tree t)
  visible-elim {s} {LTS.evLabel A channel value} (LTS.sVis refl branch)
    with offer-elim {s = s} {e = LTS.evLabel A channel value} branch
  ... | t , nextSame , targetSame with next-sound {s = s} {e = LTS.evLabel A channel value} nextSame
  ...   | input , decoded , proof = input , t , decoded , proof , targetSame

  -- The native policy tree invents neither sil nodes nor new silent source rules.
  hidden-elim : ∀ {s P} → tree s LTS.─[ LTS.τ ]─► P →
    Σ[ t ∈ Node.State ] (Node.Tau s t × P ≡ tree t)
  hidden-elim (LTS.sSil ())
  hidden-elim (LTS.sTau {i = at} {a = choice} refl branch) = branch-elim {at = at} {choice = choice} branch

  -- Source hidden accessibility lifts to actual PTree successors without state/tree injectivity.
  lift-tau-accessible : ∀ {s} → Acc (λ t s → Node.Tau s t) s →
    Acc (λ Q P → P LTS.─[ LTS.τ ]─► Q) (tree s)
  lift-tau-accessible {s} (acc smaller) = acc descend
    where
    -- Inversion recovers the exact source step needed by the existing accessibility witness.
    descend : ∀ {P} → tree s LTS.─[ LTS.τ ]─► P → Acc (λ Q P → P LTS.─[ LTS.τ ]─► Q) P
    descend transition with hidden-elim transition
    ... | t , sourceStep , refl = lift-tau-accessible (smaller sourceStep)

  -- This covers actual native hidden work; hiding visible environment updates is a different relation.
  tau-accessible : ∀ s → Acc (λ Q P → P LTS.─[ LTS.τ ]─► Q) (tree s)
  tau-accessible s = lift-tau-accessible (Scheduling.tau-accessible s)

  -- Exact observation retains one full action for every native visible event.
  data Matches : List LTS.Event → List Node.Action → Set₁ where
    empty : Matches [] []
    matched : ∀ {e input es inputs} → decode e ≡ just input → Matches es inputs →
      Matches (e ∷ es) (input ∷ inputs)

  -- Every independent full-policy run has the same native trace and endpoint state.
  complete : ∀ {s es inputs t} → Matches es inputs → Node.Run s inputs t →
    tree s Traces.⟹∖√⟨ es ⟩ tree t
  complete empty Node.stop = Traces.∖√-refl
  complete matches (Node.internal proof source) = Traces.∖√-τ (hidden-intro proof) (complete matches source)
  complete (matched decoded matches) (Node.visible proof source) =
    Traces.∖√-ev (visible-intro decoded proof) (complete matches source)

  -- Conversely arbitrary native paths recover the full source inputs and actual final tree.
  sound : ∀ {s es P} → tree s Traces.⟹∖√⟨ es ⟩ P →
    Σ[ inputs ∈ List Node.Action ] Σ[ t ∈ Node.State ]
      (Matches es inputs × Node.Run s inputs t × P ≡ tree t)
  sound Traces.∖√-refl = [] , _ , empty , Node.stop , refl
  sound (Traces.∖√-τ proof path) with hidden-elim proof
  ... | t , sourceStep , refl with sound path
  ...   | inputs , u , matches , source , same = inputs , u , matches , Node.internal sourceStep source , same
  sound (Traces.∖√-ev proof path) with visible-elim proof
  ... | input , t , decoded , sourceStep , refl with sound path
  ...   | inputs , u , matches , source , same = input ∷ inputs , u , matched decoded matches , Node.visible sourceStep source , same

  -- Source actions always have inhabited exact full-native observation witnesses.
  canonical-matches : ∀ inputs → Matches (map encode inputs) inputs
  canonical-matches [] = empty
  canonical-matches (input ∷ inputs) = matched (decode-encode input) (canonical-matches inputs)

  -- Wire erasure changes only the observation, never the independently reconstructed action.
  observe-decoded : ∀ {e input} → decode e ≡ just input → observe e ≡ N.wireAction input
  observe-decoded decoded rewrite decoded = refl

  -- Deleting explicit policy inputs preserves every wire record in its original order.
  wire-observation : ∀ {es inputs} → Matches es inputs → mapMaybe observe es ≡ Node.wireRows inputs
  wire-observation empty = refl
  wire-observation (matched {input = Node.wire row} decoded matches)
    rewrite decoded | wire-observation matches = refl
  wire-observation (matched {input = Node.setForecast _} decoded matches)
    rewrite decoded | wire-observation matches = refl
  wire-observation (matched {input = Node.setTerminate _} decoded matches)
    rewrite decoded | wire-observation matches = refl
  wire-observation (matched {input = Node.eligible _} decoded matches)
    rewrite decoded | wire-observation matches = refl
  wire-observation (matched {input = Node.handledNormal _} decoded matches)
    rewrite decoded | wire-observation matches = refl
  wire-observation (matched {input = Node.rejectedCancel} decoded matches)
    rewrite decoded | wire-observation matches = refl

  -- Canonical realization introduces no native-payload or environment-value synthesis assumption.
  realize : ∀ {s inputs t} → Node.Run s inputs t →
    tree s Traces.⟹∖√⟨ map encode inputs ⟩ tree t
  realize {inputs = inputs} source = complete (canonical-matches inputs) source

  -- Independent wire compatibility existentially retains full node inputs and source target.
  SourceWire : Node.State → List D.Event → Set
  SourceWire s rows = Σ[ inputs ∈ List Node.Action ] Σ[ target ∈ Node.State ]
    (Node.Run s inputs target × Node.wireRows inputs ≡ rows)

  -- Native wire compatibility retains an actual full-policy path before hiding its inputs.
  NativeWireTrace : Node.State → List D.Event → Set₁
  NativeWireTrace s rows = Σ[ es ∈ List LTS.Event ] Σ[ P ∈ N.Proc ]
    (tree s Traces.⟹∖√⟨ es ⟩ P × mapMaybe observe es ≡ rows)

  -- Every independent source wire witness has an exact full-policy native realization.
  source-wire-to-native : ∀ {s rows} → SourceWire s rows → NativeWireTrace s rows
  source-wire-to-native (inputs , target , source , observed) =
    map encode inputs , tree target , realize source ,
    trans (wire-observation (canonical-matches inputs)) observed

  -- Every actual native wire witness recovers the original policy run and all erased inputs.
  native-wire-to-source : ∀ {s rows} → NativeWireTrace s rows → SourceWire s rows
  native-wire-to-source (es , P , path , observed) with sound path
  ... | inputs , target , matches , source , same = inputs , target , source ,
    trans (sym (wire-observation matches)) observed

  -- The wire languages coincide for the exact policy tree, without promising a wire-only decision procedure.
  wire-equivalence : ∀ s rows →
    (SourceWire s rows → NativeWireTrace s rows) × (NativeWireTrace s rows → SourceWire s rows)
  wire-equivalence s rows = source-wire-to-native , native-wire-to-source
