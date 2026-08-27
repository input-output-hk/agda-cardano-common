{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — the `{| all api channels |}` synchronisation
-- alphabet, for ANY `Params`.
--
-- This is the api analogue of `NetCommon`'s `ioES`: `apiSet` only asks
-- "is this constructor an api channel?", a question whose answer does
-- not mention `p` at all, so every scenario was re-deriving the very
-- same clause-per-constructor decision function.  Hoisting it here lets
-- a scenario write `open import … ApiAlphabet myParams using (apiES)`
-- instead of ~20 lines of boilerplate.
--
-- WHY A SEPARATE MODULE, NOT A `NetCommon` ADDITION.  `NetCommon` sits
-- underneath the whole `blockLiveness⁺` closure (≈150 modules, ≈48 min
-- from cold), so touching it would rebuild all of it for a definition
-- nothing down there needs.  A new leaf module beside `NetCommon` costs
-- nothing to the existing closure.
--
-- NOT USED BY THE DIAMOND, DELIBERATELY.  `FourNode.FourNodeDiamond`
-- keeps its own copy: `Parametric.DiamondInstance`'s faithfulness gate
-- (`diamond-faithful … = refl`) requires `Parametric.Node` to receive
-- the diamond's OWN `apiES` term, and `chanSet` builds a record — two
-- structurally identical but separately-defined `EventSet`s are not
-- `refl`-equal.  Scenarios with no such gate (the star, the line) use
-- this module instead.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.Params using (Params)

module CSP.Examples.Cardano_network.ApiAlphabet (p : Params) where

open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_,_)
open import Relation.Nullary using (Dec; yes; no)

open import Process_Trees using (AnyTypes)

open import CSP.Examples.Cardano_network.Net p
  using ( Net_Api; Net_Api-≟
        ; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack; done
        ; apiCS; apiBF; apiTS; apiKA; apiLN; apiLF; break )
open import CSP.Examples.Cardano_network.Data p using (Payload)

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using (chanSet; EventSet)

-- membership of the {| all api channels |} sync set (by channel, ignoring payload)
apiSet : AnyTypes (Net_Api Payload) → Set
apiSet (_ , apiCS _ _ _) = ⊤
apiSet (_ , apiBF _ _ _) = ⊤
apiSet (_ , apiKA _ _ _) = ⊤
apiSet (_ , apiTS _ _ _) = ⊤
apiSet (_ , apiLN _ _ _) = ⊤
apiSet (_ , apiLF _ _ _) = ⊤
apiSet (_ , done _ _ _)  = ⊤   -- `done` is api-synced (driven teardown), not node-local
apiSet _                 = ⊥

-- decidability of `apiSet` membership
apiSet-dec : (at : AnyTypes (Net_Api Payload)) → Dec (apiSet at)
apiSet-dec (_ , apiCS  _ _ _) = yes tt
apiSet-dec (_ , apiBF  _ _ _) = yes tt
apiSet-dec (_ , input  _ _ _) = no λ ()
apiSet-dec (_ , output _ _ _) = no λ ()
apiSet-dec (_ , sndmsg _ _ _) = no λ ()
apiSet-dec (_ , rcvmsg _ _ _) = no λ ()
apiSet-dec (_ , tx     _ _ _) = no λ ()
apiSet-dec (_ , sndack _ _ _) = no λ ()
apiSet-dec (_ , rcvack _ _ _) = no λ ()
apiSet-dec (_ , ack    _ _ _) = no λ ()
apiSet-dec (_ , done   _ _ _) = yes tt
apiSet-dec (_ , apiTS  _ _ _) = yes tt
apiSet-dec (_ , apiKA  _ _ _) = yes tt
apiSet-dec (_ , apiLN  _ _ _) = yes tt
apiSet-dec (_ , apiLF  _ _ _) = yes tt
apiSet-dec (_ , break  _)     = no λ ()

-- the {| all api channels |} event set
apiES : EventSet
apiES = chanSet apiSet apiSet-dec
