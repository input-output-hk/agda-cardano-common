{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — the BlockFetch≻LeiosFetch-PRIORITISED
-- link-indexed medium `NetworkLinkPri` (Task 4 of the praos-over-leios plan).
--
-- This is the integration module: it overlays the channel-level priority
-- operator `Priᶜ` (`CSP.Priority.Channel`) — ordered by `bfOverLf`
-- (`Priority/BfOverLf.agda`, per link BlockFetch's `sndmsg` dominates that
-- link's LeiosFetch `sndmsg`) — onto each link's send queue `Inputsₗ`
-- (`NetworkLink.agda`).  `Priᶜ` requires a finite-branching certificate
-- `FinBr` for the process it wraps; `fbInputsₗ` assembles it from the loop
-- closure `finBr-loop0menu` (Task 1) for each `Input` cell folded through
-- the interleaving closure `finBr-⦀⋆` (Task 2).
--
-- The construction mirrors `NetworkLink.agda` exactly, except that `TxSideₗ`'s
-- send bundle `Inputsₗ l` is replaced by `Priᶜ bfOverLf (Inputsₗ l) (fbInputsₗ l)`.
-- Data is fixed to the shared `Payload` (as `bfOverLf` requires), so the whole
-- module lives over `Net Payload` / `AnyTypes (Net Payload)` — literally the same
-- alphabet `Priᶜ`, `bfOverLf`, and `Inputsₗ` use.  `NetworkLinkPriA` renames the
-- medium into the `Net_Api Payload` alphabet (as `NetworkA` renames `Network`).
--
-- Not `--safe`: the Cardano/priority import chain carries a pre-existing
-- postulate elsewhere in the project; this module itself introduces no
-- `postulate`, no `dne`/`Classical`, no `NON_TERMINATING`, no sized types.
--
-- There is NO property to prove here — the deliverable is the construction
-- typechecking (exit 0).
------------------------------------------------------------------------

open import Level using (0ℓ; _⊔_) renaming (suc to lsuc)
open import Data.Unit.Polymorphic using (⊤)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (just; nothing; Is-just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_; _×_)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees using (PTree; AnyTypes; ExtI)
open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Base using (Dir; IDs)

module CSP.Examples.Cardano_network.Priority.NetworkLinkPri (p : Params) where

open import CSP.Examples.Cardano_network.Data p using (Payload; DecEq-Payload)
open import CSP.Examples.Cardano_network.Net p
  using ( Net; Net-≟; Net_Api; Link
        ; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack )
open Params p using (numLinks; linkConfig)

-- the operator layer over the `Net Payload` alphabet (as in `NetworkLink.agda`)
import CSP.Operators {E = Net Payload} (Net-≟ {Payload}) as Op
open Op using (_∥⇘_⇙_; _⦀_; _∖_; ⦀Fin; chanSet)

-- the plain link-indexed medium's leaves / sides we reuse verbatim
open import CSP.Examples.Cardano_network.Network p Payload
  using ( NetProc; Input; inputMenu; csSR; csSR-dec; csTA; csTA-dec )
open import CSP.Examples.Cardano_network.NetworkLink p Payload
  using ( Inputsₗ; Transmitterₗ; RcvAckₗ; RxSideₗ )

-- the channel-level priority operator + its finite-branching certificates
open import CSP.Priority.Base {0ℓ} {0ℓ} {Net Payload} using (FinBr)
open import CSP.Priority.Channel (Net-≟ {Payload}) using (Priᶜ)
open import CSP.Priority.Closure (Net-≟ {Payload}) using (finBr-prefix₀; finBr-Skip)
open import CSP.Priority.ClosureLoop (Net-≟ {Payload}) using (finBr-loop0menu; finBr-⦀⋆)
open import Semantics.LTS {0ℓ} {0ℓ} {lsuc 0ℓ ⊔ 0ℓ} {Net Payload} {ExtI (Net Payload)}
  using (sRet; sSil; sVis; sTau)

-- the BlockFetch≻LeiosFetch channel order (fixes Data = Payload; same alphabet)
open import CSP.Examples.Cardano_network.Priority.BfOverLf p using (bfOverLf)

-- the `Net Payload ↪ Net_Api Payload` renaming (identity on channel names),
-- reusing `NetCommon`'s injection so `NetworkLinkPriA` matches `NetworkA`
open import CSP.Examples.Cardano_network.NetCommon p using (ιNet; ιNet⁻¹; ιNet-linv)
import CSP.Rename {E₁ = Net Payload} {E₂ = Net_Api Payload} ιNet ιNet⁻¹ ιNet-linv as RenNet

------------------------------------------------------------------------
-- `finBr-Output` — a `FinBr` for the output prefix `Op.Output e val P`
-- (`react (Output-cont e val P) ∅t`, a stable react node offering the single
-- carried value `val` on channel `e`).  Not in `Closure.agda` (which only has
-- `finBr-prefix`/`finBr-prefix₀`), so built here; it mirrors `finBr-prefix`
-- with the extra `val`-match of `Output-cont`.
------------------------------------------------------------------------

-- if the residual `P` is finitary, so is the output prefix `e ! val ⟶ P`.
finBr-Output : {A : Set} ⦃ _ : DecEq A ⦄ {e : Net Payload A} {val : A} {P : NetProc}
             → FinBr P → FinBr (Op.Output e val P)
FinBr.stable?   (finBr-Output fp)                 = yes (λ i a → refl)   -- τc = ∅t ⇒ stable
FinBr.chan-supp (finBr-Output {A = A} {e = e} fp) = (A , e) ∷ []        -- offers exactly (A,e)
FinBr.chan-compl (finBr-Output {A = A} {e = e} fp) refl at a isj with Net-≟ (A , e) at
... | yes refl = here refl
... | no  _    = contradiction isj (λ ())
FinBr.next (finBr-Output fp) (sRet ())        -- react ≢ ret
FinBr.next (finBr-Output fp) (sSil ())        -- react ≢ sil
FinBr.next (finBr-Output fp) (sTau refl ())   -- τc = ∅t ⇒ `nothing ≡ just` absurd
-- a visible step fires channel `(A,e)` at value `val`, landing in `P`.
FinBr.next (finBr-Output {A = A} {e = e} {val = val} {P = P} fp)
           (sVis {at = at} {a = a} refl br) with Net-≟ (A , e) at
... | no  _    = case br of λ ()                        -- other channel ⇒ nothing
... | yes refl with a ≟ val
...   | yes _  = subst FinBr (just-injective br) fp     -- value matches ⇒ target = P
...   | no  _  = case br of λ ()                        -- value mismatch ⇒ nothing

------------------------------------------------------------------------
-- Per-link Inputs certificate `fbInputsₗ`.
--
-- Each `Input l d id = loop0 (pchoice (inputMenu l d id))` is a loop-menu cell:
-- its head offers exactly `input l d id`, whose continuation is the output prefix
-- `Op.Output (sndmsg l d id) x (rcvack l d id ⟶₀ Skip)` (this is where the
-- `sndmsg l d id` channel `bfOverLf` prioritises lives).  `finBr-loop0menu`
-- (Task 1) builds each cell's `FinBr`; `finBr-⦀⋆` (Task 2) folds them across the
-- link's configured `(Dir × IDs)` list into `FinBr (Inputsₗ l)`.
------------------------------------------------------------------------

-- the head offer support of `Input l d id`: just its `input l d id` channel.
inputSupp : (l : Link) (d : Dir) (id : IDs) → List (AnyTypes (Net Payload))
inputSupp l d id = (Payload , input l d id) ∷ []

-- completeness: every actually-offered channel of `inputMenu l d id` is `input l d id`.
inputCompl : (l : Link) (d : Dir) (id : IDs)
           → ∀ at a → Is-just (inputMenu l d id at a) → at ∈ inputSupp l d id
inputCompl l d id (_ , input l′ d′ id′) a isj with l′ ≟ l
... | no _ = contradiction isj (λ ())
inputCompl l d id (_ , input l′ d′ id′) a isj | yes refl with d′ ≟ d
... | no _ = contradiction isj (λ ())
inputCompl l d id (_ , input l′ d′ id′) a isj | yes refl | yes refl with id′ ≟ id
... | no _    = contradiction isj (λ ())
... | yes refl = here refl
inputCompl l d id (_ , output _ _ _) a ()
inputCompl l d id (_ , sndmsg _ _ _) a ()
inputCompl l d id (_ , rcvmsg _ _ _) a ()
inputCompl l d id (_ , tx     _ _ _) a ()
inputCompl l d id (_ , sndack _ _ _) a ()
inputCompl l d id (_ , rcvack _ _ _) a ()
inputCompl l d id (_ , ack    _ _ _) a ()

-- each menu continuation is finitary: the sole `just` case is the `input l d id`
-- offer, whose continuation is `Op.Output (sndmsg l d id) a (rcvack l d id ⟶₀ Skip)`.
inputMenufin : (l : Link) (d : Dir) (id : IDs)
             → ∀ at a t → inputMenu l d id at a ≡ just t → FinBr {R = ⊤ {0ℓ}} t
inputMenufin l d id (_ , input l′ d′ id′) a t eq with l′ ≟ l
... | no _ = case eq of λ ()
inputMenufin l d id (_ , input l′ d′ id′) a t eq | yes refl with d′ ≟ d
... | no _ = case eq of λ ()
inputMenufin l d id (_ , input l′ d′ id′) a t eq | yes refl | yes refl with id′ ≟ id
... | no _    = case eq of λ ()
... | yes refl = subst FinBr (just-injective eq) (finBr-Output (finBr-prefix₀ finBr-Skip))
inputMenufin l d id (_ , output _ _ _) a t ()
inputMenufin l d id (_ , sndmsg _ _ _) a t ()
inputMenufin l d id (_ , rcvmsg _ _ _) a t ()
inputMenufin l d id (_ , tx     _ _ _) a t ()
inputMenufin l d id (_ , sndack _ _ _) a t ()
inputMenufin l d id (_ , rcvack _ _ _) a t ()
inputMenufin l d id (_ , ack    _ _ _) a t ()

-- FinBr for one `Input l d id` loop-menu cell.
fbInputCell : (l : Link) (d : Dir) (id : IDs) → FinBr (Input l d id)
fbInputCell l d id =
  finBr-loop0menu (inputMenu l d id) (inputSupp l d id) (inputCompl l d id) (inputMenufin l d id)

-- the per-element certificate vector for one link's configured Input cells.
allFbInputsₗ : (l : Link) (cfg : List (Dir × IDs))
             → All FinBr (map (λ { (d , id) → Input l d id }) cfg)
allFbInputsₗ l []              = []
allFbInputsₗ l ((d , id) ∷ cfg) = fbInputCell l d id ∷ allFbInputsₗ l cfg

-- FinBr for one link's send-queue bundle `Inputsₗ l = ⦀⋆ (map Input …)`.
fbInputsₗ : (l : Link) → FinBr (Inputsₗ l)
fbInputsₗ l =
  finBr-⦀⋆ (map (λ { (d , id) → Input l d id }) (linkConfig l)) (allFbInputsₗ l (linkConfig l))

------------------------------------------------------------------------
-- The prioritised sides and the full renamed medium (mirrors `NetworkLink.agda`
-- with `Inputsₗ l` replaced by `Priᶜ bfOverLf (Inputsₗ l) (fbInputsₗ l)`).
------------------------------------------------------------------------

-- link l's Tx side with BlockFetch≻LeiosFetch priority overlaid on the send queue.
TxSideₗ-pri : Link → NetProc
TxSideₗ-pri l =
  (Priᶜ bfOverLf (Inputsₗ l) (fbInputsₗ l) ∥⇘ chanSet csSR csSR-dec ⇙ (Transmitterₗ l ⦀ RcvAckₗ l))
    ∖ chanSet csSR csSR-dec

-- the complete small prioritised network for one link.
NetOneLinkPri : Link → NetProc
NetOneLinkPri l =
  (TxSideₗ-pri l ∥⇘ chanSet csTA csTA-dec ⇙ RxSideₗ l) ∖ chanSet csTA csTA-dec

-- the prioritised link-indexed medium: one small prioritised network per link.
NetworkLinkPri : NetProc
NetworkLinkPri = ⦀Fin numLinks NetOneLinkPri

-- the renamed prioritised medium over the `Net_Api Payload` alphabet.
NetworkLinkPriA : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
NetworkLinkPriA = RenNet.renameMap NetworkLinkPri
