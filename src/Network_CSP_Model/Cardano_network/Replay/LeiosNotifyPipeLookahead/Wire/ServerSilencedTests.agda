{-# OPTIONS --safe #-}

-- Concrete decisions of the server language with silenced RequestNext and Votes rows.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ServerSilencedTests where

open import Data.Bool using (Bool; true; false)
open import Data.List using ([]; _∷_)
open import Data.Unit using (tt)
open import Relation.Nullary.Decidable using (True; False)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Cardano_network.LeiosNotifyPipeLookahead.Wire.Server Bool
  using (request; quit; done; reply; normal; canceled; genericNext; nodeNext)
open import Cardano_network.LeiosNotifyPipeLookahead.Wire.ServerSilenced Bool (λ b → b)

-- A visible normal reply is accepted although its RequestNext was silenced.
visible-without-request : True (decide-silenced nodeNext (reply (normal false) ∷ []))
visible-without-request = tt

-- Graceful node shutdown: a normal reply, Quit, two cancellations and Done.
graceful : True (decide-silenced nodeNext
  (reply (normal false) ∷ quit ∷ reply canceled ∷ reply canceled ∷ done ∷ []))
graceful = tt

-- The node contract never cancels before Quit, even with silenced requests.
node-canceled-open-rejected : False (decide-silenced nodeNext (reply canceled ∷ []))
node-canceled-open-rejected = tt

-- The generic contract may cancel before Quit.
generic-canceled-open : True (decide-silenced genericNext (reply canceled ∷ []))
generic-canceled-open = tt

-- After a node cancellation only cancellations and Done may follow.
normal-after-cancel-rejected : False (decide-silenced nodeNext
  (quit ∷ reply canceled ∷ reply (normal false) ∷ []))
normal-after-cancel-rejected = tt

-- Done requires a preceding Quit.
done-before-quit-rejected : False (decide-silenced genericNext (done ∷ []))
done-before-quit-rejected = tt

-- Nothing follows Done.
after-done-rejected : False (decide-silenced genericNext (quit ∷ done ∷ quit ∷ []))
after-done-rejected = tt

-- A post-Quit drain may end at EOF as a prefix.
drain-eof-prefix : True (decide-silenced nodeNext (quit ∷ reply (normal false) ∷ []))
drain-eof-prefix = tt

-- A silenced row kind is never part of the erased language.
hidden-row-not-in-language : False (decide genericNext opened (request ∷ []))
hidden-row-not-in-language = tt

-- Requests precede each pre-Quit reply, and Quit is preceded by one per later reply.
fill-example : fill (reply (normal false) ∷ quit ∷ reply canceled ∷ done ∷ [])
  ≡ request ∷ reply (normal false) ∷ request ∷ quit ∷ reply canceled ∷ done ∷ []
fill-example = refl
