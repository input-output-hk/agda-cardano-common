{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — THE LINEAR-LEIOS INSTANCE FAMILY of the
-- no-livelock work (Stage L, L0): `pL k m` is `leiosLParams` with `k`
-- links and `m` voters, `lpF k m` its Leios parameters, `HP k m` the
-- hidden set (every channel except `env` and `break`), and the vote
-- universe predicate `AllV`.  Both shipped instances are members of the
-- family BY DEFINITION: `p2 ≡ pL 1 2`, `leiosLParams ≡ pL 2 3`, … (`refl`).
------------------------------------------------------------------------

module Cardano_network.Parametric.Leios.LeiosInstanceP where

import Data.Unit as U
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Bool.ListAction using (any)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
import Data.Fin.Properties as FinProp
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq)
import Class.DecEq.Instances as DecEqI

open import Process_Trees using (AnyTypes)
open import Cardano_network.Params using (Params)
open import Cardano_network.Base
import Cardano_network.Parametric.Leios.LeiosParams as LeiosP
open import Cardano_network.Parametric.Leios.LeiosInstanceL
  using (leiosLDecEq⊤; leiosLDecEqBool; leiosLDecEqBlock; leiosLCfg)
import Cardano_network.Net as N
import Cardano_network.Data as D
import CSP.Operators as O

-- decidable equality for `m` voters
decVoterF : ∀ m → DecEq (Fin m)
decVoterF m = record { _≟_ = FinProp._≟_ }

-- the vote blob of an `m`-voter line: who voted, and which RB the vote names
VB : ℕ → Set
VB m = Fin m × Maybe Bool

-- decidable equality for the vote blob (component instances passed explicitly)
decVB : ∀ m → DecEq (VB m)
decVB m = DecEqI.DecEq-× ⦃ decVoterF m ⦄ ⦃ leiosLDecEqBlock ⦄

-- `leiosLParams` with `k` links and `m` voters
pL : ℕ → ℕ → Params
pL k m = record
  { Cookie = U.⊤ ; Block = Maybe Bool ; LSlot = U.⊤
  ; VoterId = Fin m ; VoteBlob = VB m
  ; numLinks = k ; linkConfig = λ _ → leiosLCfg
  ; decCookie = leiosLDecEq⊤ ; decBlock = leiosLDecEqBlock
  ; decLSlot = leiosLDecEq⊤ ; decVoterId = decVoterF m
  ; decVoteBlob = decVB m
  ; Time = U.⊤ ; Length = U.⊤ ; time₀ = U.tt ; length₀ = U.tt
  ; decTime = leiosLDecEq⊤ ; decLength = leiosLDecEq⊤
  ; EB = Bool ; EBHash = Bool ; decEB = leiosLDecEqBool ; decEBHash = leiosLDecEqBool
  ; ebHash = λ e → e ; announcedEB = λ b → b
  ; RbHash = Maybe Bool ; decRbHash = leiosLDecEqBlock ; rbHash = λ b → b
  ; Tx = Bool ; TxHash = Bool ; decTx = leiosLDecEqBool ; decTxHash = leiosLDecEqBool
  ; txHash = λ x → x
  ; Size = U.⊤ ; decSize = leiosLDecEq⊤ ; txSize = λ _ → U.tt
  ; slotOf = λ _ → U.tt }

-- the Leios parameters of the family (`leiosLP`'s oracle, body table and certificate attribute)
lpF : ∀ k m → LeiosP.LeiosParams (pL k m)
lpF k m = record
  { mkVoteBlob = λ v r → v , r
  ; blobVoter  = proj₁
  ; blobRb     = proj₂
  ; blobVoter-mk = λ _ _ → refl
  ; blobRb-mk    = λ _ _ → refl
  ; certifies  = λ vs r → any (λ v → ⌊ DecEq._≟_ leiosLDecEqBlock (proj₂ v) r ⌋) vs
  ; ebTxs      = λ h → if h then ((true , U.tt) ∷ []) else []
  ; ebSize     = λ _ → U.tt
  ; rbCert     = λ b → if ⌊ DecEq._≟_ leiosLDecEqBlock b (just false) ⌋
                       then just (just true) else nothing }

-- the vote-universe premise: every blob is in `U` (stated as `memberOf`'s own body, so it
-- is `NodeLogicL.memberOf ⦃ decVoteBlob ⦄ v U ≡ true` by unfolding)
AllV : ∀ m → List (VB m) → Set
AllV m U = ∀ v → any (λ y → ⌊ DecEq._≟_ (decVB m) y v ⌋) U ≡ true

-- membership of the hidden set: every channel except `env` and `break`
hSet : ∀ k m → AnyTypes (N.Net_Api (pL k m) (D.Payload (pL k m))) → Set
hSet k m (_ , N.env _ _ _) = ⊥
hSet k m (_ , N.break _)   = ⊥
hSet k m _                 = ⊤

-- decidability of `hSet`, one clause per `Net_Api` constructor
hSet-dec : ∀ k m → (at : AnyTypes (N.Net_Api (pL k m) (D.Payload (pL k m)))) → Dec (hSet k m at)
hSet-dec k m (_ , N.input  _ _ _) = yes tt
hSet-dec k m (_ , N.output _ _ _) = yes tt
hSet-dec k m (_ , N.sndmsg _ _ _) = yes tt
hSet-dec k m (_ , N.rcvmsg _ _ _) = yes tt
hSet-dec k m (_ , N.tx     _ _ _) = yes tt
hSet-dec k m (_ , N.sndack _ _ _) = yes tt
hSet-dec k m (_ , N.rcvack _ _ _) = yes tt
hSet-dec k m (_ , N.ack    _ _ _) = yes tt
hSet-dec k m (_ , N.done   _ _ _) = yes tt
hSet-dec k m (_ , N.apiCS  _ _ _) = yes tt
hSet-dec k m (_ , N.apiBF  _ _ _) = yes tt
hSet-dec k m (_ , N.apiTS  _ _ _) = yes tt
hSet-dec k m (_ , N.apiKA  _ _ _) = yes tt
hSet-dec k m (_ , N.apiLN  _ _ _) = yes tt
hSet-dec k m (_ , N.apiLF  _ _ _) = yes tt
hSet-dec k m (_ , N.apiLP  _ _ _) = yes tt
hSet-dec k m (_ , N.store  _ _ _) = yes tt
hSet-dec k m (_ , N.env    _ _ _) = no λ ()
hSet-dec k m (_ , N.break  _)     = no λ ()

-- THE HIDDEN SET of the family (H2 at `pL 1 2`, HL at `pL 2 3`)
HP : ∀ k m → O.EventSet (N.Net_Api-≟ (pL k m) {D.Payload (pL k m)})
HP k m = O.chanSet (N.Net_Api-≟ (pL k m) {D.Payload (pL k m)}) (hSet k m) (hSet-dec k m)

-- the six vote blobs of the two-voter line
U6 : List (VB 2)
U6 = (fzero , nothing) ∷ (fzero , just true) ∷ (fzero , just false)
   ∷ (fsuc fzero , nothing) ∷ (fsuc fzero , just true) ∷ (fsuc fzero , just false) ∷ []

-- every two-voter blob is one of them
allV6 : AllV 2 U6
allV6 (fzero , nothing)         = refl
allV6 (fzero , just true)       = refl
allV6 (fzero , just false)      = refl
allV6 (fsuc fzero , nothing)    = refl
allV6 (fsuc fzero , just true)  = refl
allV6 (fsuc fzero , just false) = refl

-- the nine vote blobs of the three-voter line
U9 : List (VB 3)
U9 = (fzero , nothing) ∷ (fzero , just true) ∷ (fzero , just false)
   ∷ (fsuc fzero , nothing) ∷ (fsuc fzero , just true) ∷ (fsuc fzero , just false)
   ∷ (fsuc (fsuc fzero) , nothing) ∷ (fsuc (fsuc fzero) , just true) ∷ (fsuc (fsuc fzero) , just false) ∷ []

-- every three-voter blob is one of them
allV9 : AllV 3 U9
allV9 (fzero , nothing)                = refl
allV9 (fzero , just true)              = refl
allV9 (fzero , just false)             = refl
allV9 (fsuc fzero , nothing)           = refl
allV9 (fsuc fzero , just true)         = refl
allV9 (fsuc fzero , just false)        = refl
allV9 (fsuc (fsuc fzero) , nothing)    = refl
allV9 (fsuc (fsuc fzero) , just true)  = refl
allV9 (fsuc (fsuc fzero) , just false) = refl
