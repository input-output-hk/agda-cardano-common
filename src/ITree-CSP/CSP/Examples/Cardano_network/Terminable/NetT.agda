{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Terminable Cardano network example — the LOCAL self-contained event
-- type `NetT`.
--
-- This isolates ALL terminable work (the `mdone` channel and everything
-- built on it) inside the `Terminable/` subfolder: the parent
-- `Cardano_network` alphabet (`Net`/`Net_Api`) has NO `mdone`.  `NetT`
-- keeps exactly the eight wire channels of the parent `Net`
-- (input/output/sndmsg/rcvmsg/tx carrying `Data`; sndack/rcvack/ack
-- carrying `⊤`) and ADDS a `mdone : (l)(d) → IDs → NetT Data ⊤` channel
-- (the per-instance graceful-termination event).  The api/done channels
-- of `Net_Api` are deliberately omitted — the terminable medium and its
-- minimal demo drive input/output/mdone directly.
--
-- `Link` is reused from the parent `Net p` (`Fin numLinks`, mdone-free);
-- `Dir`/`IDs` from `Base`.  `NetT-≟` is the event identity (constructor +
-- l + d + id), mirroring the parent `Net-≟`.
------------------------------------------------------------------------

open import Data.Unit using (⊤)
open import Data.Product using (_,_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees using (AnyTypes)
open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Base

module CSP.Examples.Cardano_network.Terminable.NetT (p : Params) where

open Params p
open import CSP.Examples.Cardano_network.Net p using (Link)

------------------------------------------------------------------------
-- The local terminable event type: 8 wire channels + `mdone`.
------------------------------------------------------------------------
data NetT (Data : Set) : Set → Set where
  input output sndmsg rcvmsg tx : (l : Link) (d : Dir) → IDs → NetT Data Data
  sndack rcvack ack             : (l : Link) (d : Dir) → IDs → NetT Data ⊤
  mdone                         : (l : Link) (d : Dir) → IDs → NetT Data ⊤

------------------------------------------------------------------------
-- Decidable equality on `AnyTypes (NetT Data)` (constructor + l/d/id).
------------------------------------------------------------------------
NetT-≟ : {Data : Set} → (x y : AnyTypes (NetT Data)) → Dec (x ≡ y)
NetT-≟ {Data} = go
  where
  go : (x y : AnyTypes (NetT Data)) → Dec (x ≡ y)
  go (_ , input l₁ d₁ i₁) (_ , input l₂ d₂ i₂) with l₁ ≟ l₂ | d₁ ≟ d₂ | i₁ ≟ i₂
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ¬l    | _        | _        = no λ { refl → ¬l refl }
  ... | _        | no ¬d    | _        = no λ { refl → ¬d refl }
  ... | _        | _        | no ¬i    = no λ { refl → ¬i refl }
  go (_ , output l₁ d₁ i₁) (_ , output l₂ d₂ i₂) with l₁ ≟ l₂ | d₁ ≟ d₂ | i₁ ≟ i₂
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ¬l    | _        | _        = no λ { refl → ¬l refl }
  ... | _        | no ¬d    | _        = no λ { refl → ¬d refl }
  ... | _        | _        | no ¬i    = no λ { refl → ¬i refl }
  go (_ , sndmsg l₁ d₁ i₁) (_ , sndmsg l₂ d₂ i₂) with l₁ ≟ l₂ | d₁ ≟ d₂ | i₁ ≟ i₂
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ¬l    | _        | _        = no λ { refl → ¬l refl }
  ... | _        | no ¬d    | _        = no λ { refl → ¬d refl }
  ... | _        | _        | no ¬i    = no λ { refl → ¬i refl }
  go (_ , rcvmsg l₁ d₁ i₁) (_ , rcvmsg l₂ d₂ i₂) with l₁ ≟ l₂ | d₁ ≟ d₂ | i₁ ≟ i₂
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ¬l    | _        | _        = no λ { refl → ¬l refl }
  ... | _        | no ¬d    | _        = no λ { refl → ¬d refl }
  ... | _        | _        | no ¬i    = no λ { refl → ¬i refl }
  go (_ , tx l₁ d₁ i₁) (_ , tx l₂ d₂ i₂) with l₁ ≟ l₂ | d₁ ≟ d₂ | i₁ ≟ i₂
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ¬l    | _        | _        = no λ { refl → ¬l refl }
  ... | _        | no ¬d    | _        = no λ { refl → ¬d refl }
  ... | _        | _        | no ¬i    = no λ { refl → ¬i refl }
  go (_ , sndack l₁ d₁ i₁) (_ , sndack l₂ d₂ i₂) with l₁ ≟ l₂ | d₁ ≟ d₂ | i₁ ≟ i₂
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ¬l    | _        | _        = no λ { refl → ¬l refl }
  ... | _        | no ¬d    | _        = no λ { refl → ¬d refl }
  ... | _        | _        | no ¬i    = no λ { refl → ¬i refl }
  go (_ , rcvack l₁ d₁ i₁) (_ , rcvack l₂ d₂ i₂) with l₁ ≟ l₂ | d₁ ≟ d₂ | i₁ ≟ i₂
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ¬l    | _        | _        = no λ { refl → ¬l refl }
  ... | _        | no ¬d    | _        = no λ { refl → ¬d refl }
  ... | _        | _        | no ¬i    = no λ { refl → ¬i refl }
  go (_ , ack l₁ d₁ i₁) (_ , ack l₂ d₂ i₂) with l₁ ≟ l₂ | d₁ ≟ d₂ | i₁ ≟ i₂
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ¬l    | _        | _        = no λ { refl → ¬l refl }
  ... | _        | no ¬d    | _        = no λ { refl → ¬d refl }
  ... | _        | _        | no ¬i    = no λ { refl → ¬i refl }
  go (_ , mdone l₁ d₁ i₁) (_ , mdone l₂ d₂ i₂) with l₁ ≟ l₂ | d₁ ≟ d₂ | i₁ ≟ i₂
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ¬l    | _        | _        = no λ { refl → ¬l refl }
  ... | _        | no ¬d    | _        = no λ { refl → ¬d refl }
  ... | _        | _        | no ¬i    = no λ { refl → ¬i refl }
  go (_ , input _ _ _) (_ , output _ _ _) = no λ ()
  go (_ , input _ _ _) (_ , sndmsg _ _ _) = no λ ()
  go (_ , input _ _ _) (_ , rcvmsg _ _ _) = no λ ()
  go (_ , input _ _ _) (_ , tx _ _ _) = no λ ()
  go (_ , input _ _ _) (_ , sndack _ _ _) = no λ ()
  go (_ , input _ _ _) (_ , rcvack _ _ _) = no λ ()
  go (_ , input _ _ _) (_ , ack _ _ _) = no λ ()
  go (_ , input _ _ _) (_ , mdone _ _ _) = no λ ()
  go (_ , output _ _ _) (_ , input _ _ _) = no λ ()
  go (_ , output _ _ _) (_ , sndmsg _ _ _) = no λ ()
  go (_ , output _ _ _) (_ , rcvmsg _ _ _) = no λ ()
  go (_ , output _ _ _) (_ , tx _ _ _) = no λ ()
  go (_ , output _ _ _) (_ , sndack _ _ _) = no λ ()
  go (_ , output _ _ _) (_ , rcvack _ _ _) = no λ ()
  go (_ , output _ _ _) (_ , ack _ _ _) = no λ ()
  go (_ , output _ _ _) (_ , mdone _ _ _) = no λ ()
  go (_ , sndmsg _ _ _) (_ , input _ _ _) = no λ ()
  go (_ , sndmsg _ _ _) (_ , output _ _ _) = no λ ()
  go (_ , sndmsg _ _ _) (_ , rcvmsg _ _ _) = no λ ()
  go (_ , sndmsg _ _ _) (_ , tx _ _ _) = no λ ()
  go (_ , sndmsg _ _ _) (_ , sndack _ _ _) = no λ ()
  go (_ , sndmsg _ _ _) (_ , rcvack _ _ _) = no λ ()
  go (_ , sndmsg _ _ _) (_ , ack _ _ _) = no λ ()
  go (_ , sndmsg _ _ _) (_ , mdone _ _ _) = no λ ()
  go (_ , rcvmsg _ _ _) (_ , input _ _ _) = no λ ()
  go (_ , rcvmsg _ _ _) (_ , output _ _ _) = no λ ()
  go (_ , rcvmsg _ _ _) (_ , sndmsg _ _ _) = no λ ()
  go (_ , rcvmsg _ _ _) (_ , tx _ _ _) = no λ ()
  go (_ , rcvmsg _ _ _) (_ , sndack _ _ _) = no λ ()
  go (_ , rcvmsg _ _ _) (_ , rcvack _ _ _) = no λ ()
  go (_ , rcvmsg _ _ _) (_ , ack _ _ _) = no λ ()
  go (_ , rcvmsg _ _ _) (_ , mdone _ _ _) = no λ ()
  go (_ , tx _ _ _) (_ , input _ _ _) = no λ ()
  go (_ , tx _ _ _) (_ , output _ _ _) = no λ ()
  go (_ , tx _ _ _) (_ , sndmsg _ _ _) = no λ ()
  go (_ , tx _ _ _) (_ , rcvmsg _ _ _) = no λ ()
  go (_ , tx _ _ _) (_ , sndack _ _ _) = no λ ()
  go (_ , tx _ _ _) (_ , rcvack _ _ _) = no λ ()
  go (_ , tx _ _ _) (_ , ack _ _ _) = no λ ()
  go (_ , tx _ _ _) (_ , mdone _ _ _) = no λ ()
  go (_ , sndack _ _ _) (_ , input _ _ _) = no λ ()
  go (_ , sndack _ _ _) (_ , output _ _ _) = no λ ()
  go (_ , sndack _ _ _) (_ , sndmsg _ _ _) = no λ ()
  go (_ , sndack _ _ _) (_ , rcvmsg _ _ _) = no λ ()
  go (_ , sndack _ _ _) (_ , tx _ _ _) = no λ ()
  go (_ , sndack _ _ _) (_ , rcvack _ _ _) = no λ ()
  go (_ , sndack _ _ _) (_ , ack _ _ _) = no λ ()
  go (_ , sndack _ _ _) (_ , mdone _ _ _) = no λ ()
  go (_ , rcvack _ _ _) (_ , input _ _ _) = no λ ()
  go (_ , rcvack _ _ _) (_ , output _ _ _) = no λ ()
  go (_ , rcvack _ _ _) (_ , sndmsg _ _ _) = no λ ()
  go (_ , rcvack _ _ _) (_ , rcvmsg _ _ _) = no λ ()
  go (_ , rcvack _ _ _) (_ , tx _ _ _) = no λ ()
  go (_ , rcvack _ _ _) (_ , sndack _ _ _) = no λ ()
  go (_ , rcvack _ _ _) (_ , ack _ _ _) = no λ ()
  go (_ , rcvack _ _ _) (_ , mdone _ _ _) = no λ ()
  go (_ , ack _ _ _) (_ , input _ _ _) = no λ ()
  go (_ , ack _ _ _) (_ , output _ _ _) = no λ ()
  go (_ , ack _ _ _) (_ , sndmsg _ _ _) = no λ ()
  go (_ , ack _ _ _) (_ , rcvmsg _ _ _) = no λ ()
  go (_ , ack _ _ _) (_ , tx _ _ _) = no λ ()
  go (_ , ack _ _ _) (_ , sndack _ _ _) = no λ ()
  go (_ , ack _ _ _) (_ , rcvack _ _ _) = no λ ()
  go (_ , ack _ _ _) (_ , mdone _ _ _) = no λ ()
  go (_ , mdone _ _ _) (_ , input _ _ _) = no λ ()
  go (_ , mdone _ _ _) (_ , output _ _ _) = no λ ()
  go (_ , mdone _ _ _) (_ , sndmsg _ _ _) = no λ ()
  go (_ , mdone _ _ _) (_ , rcvmsg _ _ _) = no λ ()
  go (_ , mdone _ _ _) (_ , tx _ _ _) = no λ ()
  go (_ , mdone _ _ _) (_ , sndack _ _ _) = no λ ()
  go (_ , mdone _ _ _) (_ , rcvack _ _ _) = no λ ()
  go (_ , mdone _ _ _) (_ , ack _ _ _) = no λ ()
