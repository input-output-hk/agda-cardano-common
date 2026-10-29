{-# OPTIONS --guardedness #-}

-- Cheap protocol-only prefix lifts, independent of the source-invariant closure.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.MuxDeltaQPrefix (isBearerClosed : ErrorId → Bool) where

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import ConnectionManagement.MuxDeltaQ as Delta
module D = Delta isBearerClosed
module R = D.R
module X = D.X
module W = D.W
module G = D.G
module M = D.M
module P = D.P

-- Lift actual existing protocol-only initialized prefixes. The tag is evidence
-- about every action, not an assumption that arbitrary monitor steps are safe.
wrap : R.State → D.State
wrap r = D.deltaQState r []
rawProtocol : P.Action → R.Action
rawProtocol action = D.wrapMonitor (M.run action)
protocol-step : ∀ action r {r′} → R.step (rawProtocol action) r ≡ just r′ →
  D.step (D.run (rawProtocol action)) (wrap r) ≡ just (wrap r′)
protocol-step action r eq with D.actorP action
... | nothing with R.step (rawProtocol action) r
...   | nothing = case eq of λ ()
...   | just r′ = case just-injective eq of λ { refl → refl }
protocol-step action r eq | just w with R.step (rawProtocol action) r
...   | nothing = case eq of λ ()
...   | just r′ = case just-injective eq of λ { refl → refl }
data ProtocolAction : R.Action → Set where
  protocol : ∀ action → ProtocolAction (rawProtocol action)
data ProtocolActions : List R.Action → Set where
  empty : ProtocolActions []
  tagged : ∀ {action actions} → ProtocolAction action → ProtocolActions actions → ProtocolActions (action ∷ actions)
tag-protocols : ∀ actions → ProtocolActions (map rawProtocol actions)
tag-protocols [] = empty
tag-protocols (a ∷ as) = tagged (protocol a) (tag-protocols as)
lift : ∀ {r actions r′} → R.Executes r actions r′ → ProtocolActions actions →
  D.Executes (wrap r) (map D.run actions) (wrap r′)
lift R.done empty = D.done
lift (R.next {s = r} eq tail) (tagged (protocol action) tags) = D.next
  (protocol-step action r eq) (lift tail tags)
fuse-protocols : ∀ actions →
  map R.run (map X.run (map W.run (map G.run (map M.run actions)))) ≡ map rawProtocol actions
fuse-protocols [] = refl
fuse-protocols (a ∷ as) rewrite fuse-protocols as = refl
tag-nested : ∀ actions → ProtocolActions (map R.run (map X.run (map W.run (map G.run (map M.run actions)))))
tag-nested actions rewrite fuse-protocols actions = tag-protocols actions
append : ∀ {s as t bs u} → D.Executes s as t → D.Executes t bs u → D.Executes s (as ++ bs) u
append D.done tail = tail
append (D.next eq rest) tail = D.next eq (append rest tail)
append-tags : ∀ {as bs} → ProtocolActions as → ProtocolActions bs → ProtocolActions (as ++ bs)
append-tags empty right = right
append-tags (tagged a left) right = tagged a (append-tags left right)
