{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Leios no-livelock, Stage L: THE HEADLINE (spec §3.3).  The SHIPPED
-- three-node Linear-Leios system `leiosSystemL` (= `rawL ∖ ioES`, by
-- `LeiosInstance3.sysL≡ = refl`) has no livelock: hiding every channel
-- except `env` and `break` (`HL`) creates no divergence.
--   * premise (a): the counting bound `BoundL.boundL` on `rawL`, with
--     `FL` monotone;
--   * premise (b): `Tau3.rawL-τ-AccReach`;
--   * the nested hiding `(rawL ∖ ioES) ∖ HL` is bridged generically by
--     `NoLivelockHide.noLivelockT-∖` (`ioES ⊆ᴱ HL`).
-- No module parameters, no hypotheses.
------------------------------------------------------------------------

module Cardano_network.Parametric.Leios.NoLivelock.NoLivelockL where

open import Data.Nat using (_≤_)
open import Data.Nat.Properties using (+-monoˡ-≤; *-monoʳ-≤)
open import Data.Unit.Polymorphic using (tt)
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
open import Process_Trees using (ExtI)
open import Cardano_network.Parametric.Leios.LeiosInstanceP using (pL)
import Cardano_network.Parametric.Leios.LeiosInstanceL as LIL
open import Cardano_network.Parametric.Leios.LeiosInstance3 using (HL)
open import Cardano_network.Net (pL 2 3)
  using (Net_Api; Net_Api-≟; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack; done
        ; apiCS; apiBF; apiTS; apiKA; apiLN; apiLF; apiLP; store; env; break)
open import Cardano_network.Data (pL 2 3) using (Payload)
open import Cardano_network.NetCommon (pL 2 3) using (ioES)
open import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) using (_∖_)
open import Semantics.FailuresDivergences {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using (divergences)
open import CSP.Laws.FD.NoLivelockHide (Net_Api-≟ {Payload}) using (_⊆ᴱ_; noLivelockT-∖)
open import Cardano_network.Parametric.Leios.NoLivelock.BoundL using (boundL; FL; cL; cL₀)
open import Cardano_network.Parametric.Leios.NoLivelock.Tau3 using (rawL-τ-AccReach)

-- every wire event is hidden by `HL` (`input`/`output` are in both; the rest are not in `ioES`)
ioES⊆HL : ioES ⊆ᴱ HL
ioES⊆HL (_ , input  _ _ _) _ _  = tt
ioES⊆HL (_ , output _ _ _) _ _  = tt
ioES⊆HL (_ , sndmsg _ _ _) _ ()
ioES⊆HL (_ , rcvmsg _ _ _) _ ()
ioES⊆HL (_ , tx     _ _ _) _ ()
ioES⊆HL (_ , sndack _ _ _) _ ()
ioES⊆HL (_ , rcvack _ _ _) _ ()
ioES⊆HL (_ , ack    _ _ _) _ ()
ioES⊆HL (_ , done   _ _ _) _ ()
ioES⊆HL (_ , apiCS  _ _ _) _ ()
ioES⊆HL (_ , apiBF  _ _ _) _ ()
ioES⊆HL (_ , apiTS  _ _ _) _ ()
ioES⊆HL (_ , apiKA  _ _ _) _ ()
ioES⊆HL (_ , apiLN  _ _ _) _ ()
ioES⊆HL (_ , apiLF  _ _ _) _ ()
ioES⊆HL (_ , apiLP  _ _ _) _ ()
ioES⊆HL (_ , store  _ _ _) _ ()
ioES⊆HL (_ , env    _ _ _) _ ()
ioES⊆HL (_ , break  _)     _ ()

-- the bound is monotone
FL-mono : ∀ {m n} → m ≤ n → FL m ≤ FL n
FL-mono le = +-monoˡ-≤ cL₀ (*-monoʳ-≤ cL le)

-- THE THEOREM (spec §3.3)
noLivelockL : ∀ s → ¬ divergences (LIL.leiosSystemL ∖ HL) s
noLivelockL s = noLivelockT-∖ ioES HL FL FL-mono ioES⊆HL boundL rawL-τ-AccReach {s}
