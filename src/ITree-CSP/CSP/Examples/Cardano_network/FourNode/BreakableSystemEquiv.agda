{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Four-node diamond over the breakable medium — the SYSTEM-level
-- equivalence
--
--   ∀ blkA → breakableSystemₗ blkA ≈DR breakableSystem blkA
--
-- i.e. the medium equivalence of `MediumEquivA` lifted through the whole
-- `(· ∥⇘ ioES ⇙ nodes) ∖ ioES` composition, the two systems differing ONLY
-- in the medium operand.  The lift is `cong-Par⊤-L` followed by `cong-∖`
-- (the latter unconditional).
--
-- `cong-Par⊤-L`'s two `Sep ioES` obligations are the real work: OUTSIDE the
-- hidden `{| input, output |}` set the medium and the node bundle must never
-- both-offer the same event.  They are discharged by `sep-from-OffersOnly`
-- from
--   · medium side — `OffersOnly-⦀Fin` over `MediumEquivA.linkAlphaA`, i.e.
--     each cell offers only wire events or its own `break`;
--   · node side  — `nodeAlpha` below: the nodes never offer any of the six
--     INTERNAL wire channels (`sndmsg`/`rcvmsg`/`tx`/`sndack`/`rcvack`/`ack`)
--     nor any `break`.
-- The two clash only on `input`/`output`, which are exactly the events the
-- sync set excludes.
--
-- The node-side confinement is cheap because every one of the twelve
-- mini-protocol peers is a `renameMap` from its own small protocol alphabet:
-- `OffersOnly-renameMap-image` (`CSP.Laws.Bisim.RenameOffers`) reads the
-- confinement straight off the renaming's IMAGE — each `ιXX⁻¹` answers
-- `nothing` on the six internal channels and on `break` — with NO source-side
-- reasoning at all.  Only the two node-logic drivers (`produce`/`consume`)
-- need a per-constructor chain, and they are plain `apiCS`/`apiBF`/`done`
-- prefix sequences.
--
-- No postulates, holes, or `NON_TERMINATING`.
------------------------------------------------------------------------

open import Level using (Level; 0ℓ)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Unit using () renaming (⊤ to ⊤₀; tt to tt₀)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([])
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_; _×_; Σ; Σ-syntax; proj₁; proj₂)
open import Function.Base using (case_of_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans)

open import Process_Trees using (PTree; AnyTypes; ExtI)

module CSP.Examples.Cardano_network.FourNode.BreakableSystemEquiv where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( p; Block₃; nodeA; nodeB; nodeC; nodeD; produce; consume; consume-k
        ; apiES; linkAB; linkAC; linkBD; linkCD )
open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamondBreakable
  using (breakableSystem; breakableSystemₗ)
open import CSP.Examples.Cardano_network.Params using (Params)
open Params p using (linkConfig)
-- opened UNQUALIFIED (as `FourNodeDiamond` itself does): the `Output` (`!`) steps of
-- `produce`/`consume` need the per-message `DecEq` instances of `Data p` in scope
open import CSP.Examples.Cardano_network.Base
open import CSP.Examples.Cardano_network.Net p
open import CSP.Examples.Cardano_network.Data p
open import CSP.Examples.Cardano_network.NetCommon p
  using (ioES; CopySpecBreakableA; NetworkLinkBreakableA)
-- the twelve renamed mini-protocol peers, their bundle, and the six renamings
open import CSP.Examples.Cardano_network.NetworkPar p
  using ( miniProtocols
        ; KAclientA; KAserverA; CSclientA; CSserverA; BFclientA; BFserverA
        ; TSclientA; TSserverA; LNclientA; LNserverA; LFclientA; LFserverA
        ; ιKA; ιKA⁻¹; ιKA-linv ; ιBF; ιBF⁻¹; ιBF-linv ; ιCS; ιCS⁻¹; ιCS-linv
        ; ιTS; ιTS⁻¹; ιTS-linv ; ιLN; ιLN⁻¹; ιLN-linv ; ιLF; ιLF⁻¹; ιLF-linv )
open import CSP.Examples.Cardano_network.KeepAlive    p using (KAEv; KAEv-≟)
open import CSP.Examples.Cardano_network.BlockFetch   p using (BFEv; BFEv-≟)
open import CSP.Examples.Cardano_network.ChainSync    p using (CSEv; CSEv-≟)
open import CSP.Examples.Cardano_network.TxSubmission p using (TSEv; TSEv-≟)
open import CSP.Examples.Cardano_network.LeiosNotify  p using (LNEv; LNEv-≟)
open import CSP.Examples.Cardano_network.LeiosFetch   p using (LFEv; LFEv-≟)
-- (A), the medium equivalence, plus its per-cell alphabets and confinements
open import CSP.Examples.Cardano_network.MediumEquivA p
  using ( linkAlphaA; oo-breakableNetLinkA; oo-breakableLinkA; netLinkBreakable≈DR )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using (EventSet; _⦀_)
open EventSet

open import CSP.Laws.Bisim.DRCongruenceRep (Net_Api-≟ {Payload})
  using ( Alpha; OffersOnly; OffersOnly-Ret; OffersOnly-Skip; OffersOnly-Prefix
        ; OffersOnly-Prefix₀; OffersOnly-Output; OffersOnly-Par; OffersOnly-⦀
        ; OffersOnly->>=; OffersOnly-⦀Fin; unionAlpha; sep-from-OffersOnly )
open import CSP.Laws.Bisim.DRCongruence (Net_Api-≟ {Payload})
  using (Sep; cong-∖; cong-Par⊤-L)
open import Semantics.DRBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (_≈DR_)
open import Semantics.FailuresDivergences {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (_≈FD_; _⊑FD_)
open import Semantics.DRImpliesFD {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (drbisim→≈FD)

-- one `RenameOffers` instance per protocol renaming, for the image lemmas below
import CSP.Laws.Bisim.RenameOffers KAEv-≟ (Net_Api-≟ {Payload}) ιKA ιKA⁻¹ ιKA-linv as RKA
import CSP.Laws.Bisim.RenameOffers BFEv-≟ (Net_Api-≟ {Payload}) ιBF ιBF⁻¹ ιBF-linv as RBF
import CSP.Laws.Bisim.RenameOffers CSEv-≟ (Net_Api-≟ {Payload}) ιCS ιCS⁻¹ ιCS-linv as RCS
import CSP.Laws.Bisim.RenameOffers TSEv-≟ (Net_Api-≟ {Payload}) ιTS ιTS⁻¹ ιTS-linv as RTS
import CSP.Laws.Bisim.RenameOffers LNEv-≟ (Net_Api-≟ {Payload}) ιLN ιLN⁻¹ ιLN-linv as RLN
import CSP.Laws.Bisim.RenameOffers LFEv-≟ (Net_Api-≟ {Payload}) ιLF ιLF⁻¹ ιLF-linv as RLF

------------------------------------------------------------------------
-- The node-side alphabet.
------------------------------------------------------------------------

-- `nodeAlpha`: everything EXCEPT the six medium-internal wire channels and the
-- fault-injection channel.  The nodes talk to the medium only through
-- `input`/`output` (in `ioES`) and are otherwise `api*`/`done`/`store`/`env`.
nodeAlpha : Alpha
nodeAlpha (_ , sndmsg _ _ _) _ = ⊥
nodeAlpha (_ , rcvmsg _ _ _) _ = ⊥
nodeAlpha (_ , tx     _ _ _) _ = ⊥
nodeAlpha (_ , sndack _ _ _) _ = ⊥
nodeAlpha (_ , rcvack _ _ _) _ = ⊥
nodeAlpha (_ , ack    _ _ _) _ = ⊥
nodeAlpha (_ , break  _)     _ = ⊥
nodeAlpha _                  _ = ⊤₀

------------------------------------------------------------------------
-- The twelve peers, by IMAGE of their renaming.
--
-- Each `ιXX⁻¹` answers `just` only on `input`/`output` (at its own protocol
-- tag), `apiXX` and `done`, and `nothing` everywhere else — in particular on
-- the six internal wire channels and on `break`, where `nodeAlpha` is `⊥`.
-- So the seven bad constructors are refuted by the preimage equation itself
-- and every other target event lands in `nodeAlpha` trivially.
------------------------------------------------------------------------

-- KeepAlive: the renaming's image avoids the six internal wire channels and `break`
hKA : ∀ bt b at a → RKA.ι-vis-inv bt b ≡ just (at , a) → nodeAlpha bt b
hKA (_ , sndmsg _ _ _) b _ _ ()
hKA (_ , rcvmsg _ _ _) b _ _ ()
hKA (_ , tx     _ _ _) b _ _ ()
hKA (_ , sndack _ _ _) b _ _ ()
hKA (_ , rcvack _ _ _) b _ _ ()
hKA (_ , ack    _ _ _) b _ _ ()
hKA (_ , break  _) b _ _ ()
hKA (_ , input  _ _ _) b _ _ _ = tt₀
hKA (_ , output _ _ _) b _ _ _ = tt₀
hKA (_ , done   _ _ _) b _ _ _ = tt₀
hKA (_ , apiCS  _ _ _) b _ _ _ = tt₀
hKA (_ , apiBF  _ _ _) b _ _ _ = tt₀
hKA (_ , apiTS  _ _ _) b _ _ _ = tt₀
hKA (_ , apiKA  _ _ _) b _ _ _ = tt₀
hKA (_ , apiLN  _ _ _) b _ _ _ = tt₀
hKA (_ , apiLF  _ _ _) b _ _ _ = tt₀
hKA (_ , store  _ _ _) b _ _ _ = tt₀
hKA (_ , env    _ _ _) b _ _ _ = tt₀

-- BlockFetch: the renaming's image avoids the six internal wire channels and `break`
hBF : ∀ bt b at a → RBF.ι-vis-inv bt b ≡ just (at , a) → nodeAlpha bt b
hBF (_ , sndmsg _ _ _) b _ _ ()
hBF (_ , rcvmsg _ _ _) b _ _ ()
hBF (_ , tx     _ _ _) b _ _ ()
hBF (_ , sndack _ _ _) b _ _ ()
hBF (_ , rcvack _ _ _) b _ _ ()
hBF (_ , ack    _ _ _) b _ _ ()
hBF (_ , break  _) b _ _ ()
hBF (_ , input  _ _ _) b _ _ _ = tt₀
hBF (_ , output _ _ _) b _ _ _ = tt₀
hBF (_ , done   _ _ _) b _ _ _ = tt₀
hBF (_ , apiCS  _ _ _) b _ _ _ = tt₀
hBF (_ , apiBF  _ _ _) b _ _ _ = tt₀
hBF (_ , apiTS  _ _ _) b _ _ _ = tt₀
hBF (_ , apiKA  _ _ _) b _ _ _ = tt₀
hBF (_ , apiLN  _ _ _) b _ _ _ = tt₀
hBF (_ , apiLF  _ _ _) b _ _ _ = tt₀
hBF (_ , store  _ _ _) b _ _ _ = tt₀
hBF (_ , env    _ _ _) b _ _ _ = tt₀

-- ChainSync: the renaming's image avoids the six internal wire channels and `break`
hCS : ∀ bt b at a → RCS.ι-vis-inv bt b ≡ just (at , a) → nodeAlpha bt b
hCS (_ , sndmsg _ _ _) b _ _ ()
hCS (_ , rcvmsg _ _ _) b _ _ ()
hCS (_ , tx     _ _ _) b _ _ ()
hCS (_ , sndack _ _ _) b _ _ ()
hCS (_ , rcvack _ _ _) b _ _ ()
hCS (_ , ack    _ _ _) b _ _ ()
hCS (_ , break  _) b _ _ ()
hCS (_ , input  _ _ _) b _ _ _ = tt₀
hCS (_ , output _ _ _) b _ _ _ = tt₀
hCS (_ , done   _ _ _) b _ _ _ = tt₀
hCS (_ , apiCS  _ _ _) b _ _ _ = tt₀
hCS (_ , apiBF  _ _ _) b _ _ _ = tt₀
hCS (_ , apiTS  _ _ _) b _ _ _ = tt₀
hCS (_ , apiKA  _ _ _) b _ _ _ = tt₀
hCS (_ , apiLN  _ _ _) b _ _ _ = tt₀
hCS (_ , apiLF  _ _ _) b _ _ _ = tt₀
hCS (_ , store  _ _ _) b _ _ _ = tt₀
hCS (_ , env    _ _ _) b _ _ _ = tt₀

-- TxSubmission: the renaming's image avoids the six internal wire channels and `break`
hTS : ∀ bt b at a → RTS.ι-vis-inv bt b ≡ just (at , a) → nodeAlpha bt b
hTS (_ , sndmsg _ _ _) b _ _ ()
hTS (_ , rcvmsg _ _ _) b _ _ ()
hTS (_ , tx     _ _ _) b _ _ ()
hTS (_ , sndack _ _ _) b _ _ ()
hTS (_ , rcvack _ _ _) b _ _ ()
hTS (_ , ack    _ _ _) b _ _ ()
hTS (_ , break  _) b _ _ ()
hTS (_ , input  _ _ _) b _ _ _ = tt₀
hTS (_ , output _ _ _) b _ _ _ = tt₀
hTS (_ , done   _ _ _) b _ _ _ = tt₀
hTS (_ , apiCS  _ _ _) b _ _ _ = tt₀
hTS (_ , apiBF  _ _ _) b _ _ _ = tt₀
hTS (_ , apiTS  _ _ _) b _ _ _ = tt₀
hTS (_ , apiKA  _ _ _) b _ _ _ = tt₀
hTS (_ , apiLN  _ _ _) b _ _ _ = tt₀
hTS (_ , apiLF  _ _ _) b _ _ _ = tt₀
hTS (_ , store  _ _ _) b _ _ _ = tt₀
hTS (_ , env    _ _ _) b _ _ _ = tt₀

-- LeiosNotify: the renaming's image avoids the six internal wire channels and `break`
hLN : ∀ bt b at a → RLN.ι-vis-inv bt b ≡ just (at , a) → nodeAlpha bt b
hLN (_ , sndmsg _ _ _) b _ _ ()
hLN (_ , rcvmsg _ _ _) b _ _ ()
hLN (_ , tx     _ _ _) b _ _ ()
hLN (_ , sndack _ _ _) b _ _ ()
hLN (_ , rcvack _ _ _) b _ _ ()
hLN (_ , ack    _ _ _) b _ _ ()
hLN (_ , break  _) b _ _ ()
hLN (_ , input  _ _ _) b _ _ _ = tt₀
hLN (_ , output _ _ _) b _ _ _ = tt₀
hLN (_ , done   _ _ _) b _ _ _ = tt₀
hLN (_ , apiCS  _ _ _) b _ _ _ = tt₀
hLN (_ , apiBF  _ _ _) b _ _ _ = tt₀
hLN (_ , apiTS  _ _ _) b _ _ _ = tt₀
hLN (_ , apiKA  _ _ _) b _ _ _ = tt₀
hLN (_ , apiLN  _ _ _) b _ _ _ = tt₀
hLN (_ , apiLF  _ _ _) b _ _ _ = tt₀
hLN (_ , store  _ _ _) b _ _ _ = tt₀
hLN (_ , env    _ _ _) b _ _ _ = tt₀

-- LeiosFetch: the renaming's image avoids the six internal wire channels and `break`
hLF : ∀ bt b at a → RLF.ι-vis-inv bt b ≡ just (at , a) → nodeAlpha bt b
hLF (_ , sndmsg _ _ _) b _ _ ()
hLF (_ , rcvmsg _ _ _) b _ _ ()
hLF (_ , tx     _ _ _) b _ _ ()
hLF (_ , sndack _ _ _) b _ _ ()
hLF (_ , rcvack _ _ _) b _ _ ()
hLF (_ , ack    _ _ _) b _ _ ()
hLF (_ , break  _) b _ _ ()
hLF (_ , input  _ _ _) b _ _ _ = tt₀
hLF (_ , output _ _ _) b _ _ _ = tt₀
hLF (_ , done   _ _ _) b _ _ _ = tt₀
hLF (_ , apiCS  _ _ _) b _ _ _ = tt₀
hLF (_ , apiBF  _ _ _) b _ _ _ = tt₀
hLF (_ , apiTS  _ _ _) b _ _ _ = tt₀
hLF (_ , apiKA  _ _ _) b _ _ _ = tt₀
hLF (_ , apiLN  _ _ _) b _ _ _ = tt₀
hLF (_ , apiLF  _ _ _) b _ _ _ = tt₀
hLF (_ , store  _ _ _) b _ _ _ = tt₀
hLF (_ , env    _ _ _) b _ _ _ = tt₀

-- any KeepAlive-renamed peer is node-confined
ooKA : ∀ {ℓr} {R : Set ℓr} {P : PTree KAEv (ExtI KAEv) R}
     → OffersOnly nodeAlpha (RKA.renameMap P)
ooKA = RKA.OffersOnly-renameMap-image hKA

-- any BlockFetch-renamed peer is node-confined
ooBF : ∀ {ℓr} {R : Set ℓr} {P : PTree BFEv (ExtI BFEv) R}
     → OffersOnly nodeAlpha (RBF.renameMap P)
ooBF = RBF.OffersOnly-renameMap-image hBF

-- any ChainSync-renamed peer is node-confined
ooCS : ∀ {ℓr} {R : Set ℓr} {P : PTree CSEv (ExtI CSEv) R}
     → OffersOnly nodeAlpha (RCS.renameMap P)
ooCS = RCS.OffersOnly-renameMap-image hCS

-- any TxSubmission-renamed peer is node-confined
ooTS : ∀ {ℓr} {R : Set ℓr} {P : PTree TSEv (ExtI TSEv) R}
     → OffersOnly nodeAlpha (RTS.renameMap P)
ooTS = RTS.OffersOnly-renameMap-image hTS

-- any LeiosNotify-renamed peer is node-confined
ooLN : ∀ {ℓr} {R : Set ℓr} {P : PTree LNEv (ExtI LNEv) R}
     → OffersOnly nodeAlpha (RLN.renameMap P)
ooLN = RLN.OffersOnly-renameMap-image hLN

-- any LeiosFetch-renamed peer is node-confined
ooLF : ∀ {ℓr} {R : Set ℓr} {P : PTree LFEv (ExtI LFEv) R}
     → OffersOnly nodeAlpha (RLF.renameMap P)
ooLF = RLF.OffersOnly-renameMap-image hLF

-- one link's twelve-peer bundle is node-confined
oo-miniProtocols : (l : Link) (cl sv : Dir) → OffersOnly nodeAlpha (miniProtocols l cl sv)
oo-miniProtocols l cl sv =
  OffersOnly-⦀ ooKA (OffersOnly-⦀ ooKA (
  OffersOnly-⦀ ooCS (OffersOnly-⦀ ooCS (
  OffersOnly-⦀ ooBF (OffersOnly-⦀ ooBF (
  OffersOnly-⦀ ooTS (OffersOnly-⦀ ooTS (
  OffersOnly-⦀ ooLN (OffersOnly-⦀ ooLN (
  OffersOnly-⦀ ooLF ooLF))))))))))

------------------------------------------------------------------------
-- The two node-logic drivers.
------------------------------------------------------------------------

-- the produce driver is a plain `apiCS`/`apiBF`/`done` prefix chain
oo-produce : (l : Link) (d : Dir) (blk : Block₃)
           → OffersOnly nodeAlpha (produce l d blk)
oo-produce l d blk =
  OffersOnly-Prefix₀ (λ _ → tt₀)
  (OffersOnly-Prefix₀ (λ _ → tt₀)
  (OffersOnly-Output tt₀
  (OffersOnly-Prefix (λ _ → tt₀) (λ _ →
   OffersOnly-Output tt₀
  (OffersOnly-Output tt₀
  (OffersOnly-Output tt₀
  (OffersOnly-Prefix₀ (λ _ → tt₀)
  (OffersOnly-Prefix₀ (λ _ → tt₀) OffersOnly-Skip))))))))

-- the RollForward tail of the consume driver
oo-consume-k : (l : Link) (d : Dir) (x : Header × _)
             → OffersOnly nodeAlpha (consume-k l d x)
oo-consume-k l d (header b , _) =
  OffersOnly-Output tt₀
  (OffersOnly-Prefix (λ _ → tt₀) (λ _ →
   OffersOnly-Output tt₀
  (OffersOnly-Prefix₀ (λ _ → tt₀) OffersOnly-Ret)))

-- the consume driver is a plain `apiCS`/`apiBF` prefix chain
oo-consume : (l : Link) (d : Dir) → OffersOnly nodeAlpha (consume l d)
oo-consume l d =
  OffersOnly-Prefix₀ (λ _ → tt₀)
  (OffersOnly-Prefix (λ _ → tt₀) (oo-consume-k l d))

------------------------------------------------------------------------
-- The four nodes and their interleaving.
------------------------------------------------------------------------

-- node A: two link bundles synchronised with two produce drivers
oo-nodeA : (blkA : Block₃) → OffersOnly nodeAlpha (nodeA blkA)
oo-nodeA blkA =
  OffersOnly-Par apiES (λ _ _ → tt)
    (OffersOnly-⦀ (oo-miniProtocols linkAB _ _) (oo-miniProtocols linkAC _ _))
    (OffersOnly-⦀ (oo-produce linkAB _ blkA) (oo-produce linkAC _ blkA))

-- node B: consume on AB, then produce on BD
oo-nodeB : OffersOnly nodeAlpha nodeB
oo-nodeB =
  OffersOnly-Par apiES (λ _ _ → tt)
    (OffersOnly-⦀ (oo-miniProtocols linkAB _ _) (oo-miniProtocols linkBD _ _))
    (OffersOnly->>= (oo-consume linkAB _) (λ b → oo-produce linkBD _ b))

-- node C: consume on AC, then produce on CD
oo-nodeC : OffersOnly nodeAlpha nodeC
oo-nodeC =
  OffersOnly-Par apiES (λ _ _ → tt)
    (OffersOnly-⦀ (oo-miniProtocols linkAC _ _) (oo-miniProtocols linkCD _ _))
    (OffersOnly->>= (oo-consume linkAC _) (λ b → oo-produce linkCD _ b))

-- node D: consume on both incoming links
oo-nodeD : OffersOnly nodeAlpha nodeD
oo-nodeD =
  OffersOnly-Par apiES (λ _ _ → tt)
    (OffersOnly-⦀ (oo-miniProtocols linkBD _ _) (oo-miniProtocols linkCD _ _))
    (OffersOnly-⦀ (OffersOnly->>= (oo-consume linkBD _) (λ _ → OffersOnly-Skip))
                  (OffersOnly->>= (oo-consume linkCD _) (λ _ → OffersOnly-Skip)))

-- the four nodes interleaved
oo-nodes : (blkA : Block₃)
         → OffersOnly nodeAlpha (nodeA blkA ⦀ (nodeB ⦀ (nodeC ⦀ nodeD)))
oo-nodes blkA =
  OffersOnly-⦀ (oo-nodeA blkA) (OffersOnly-⦀ oo-nodeB (OffersOnly-⦀ oo-nodeC oo-nodeD))

------------------------------------------------------------------------
-- The medium side, the separation, and the lift.
------------------------------------------------------------------------

-- the concrete breakable medium confines to the union of the per-link alphabets
oo-mediumN : OffersOnly (unionAlpha linkAlphaA) NetworkLinkBreakableA
oo-mediumN = OffersOnly-⦀Fin oo-breakableNetLinkA

-- ditto the copy-spec breakable medium
oo-mediumC : OffersOnly (unionAlpha linkAlphaA) CopySpecBreakableA
oo-mediumC = OffersOnly-⦀Fin oo-breakableLinkA

-- OUTSIDE the hidden io set the medium and the nodes clash on nothing: the medium
-- only ever offers a wire event or a `break`, and of those the nodes offer only
-- `input`/`output` — which are exactly the events `ioES` excludes here.
sepDisj : ∀ {at a} → ¬ ioES .mem at a
        → unionAlpha linkAlphaA at a → nodeAlpha at a → ⊥
sepDisj {_ , input  _ _ _} nm _ _ = nm tt
sepDisj {_ , output _ _ _} nm _ _ = nm tt
sepDisj {_ , sndmsg _ _ _} nm _ ()
sepDisj {_ , rcvmsg _ _ _} nm _ ()
sepDisj {_ , tx     _ _ _} nm _ ()
sepDisj {_ , sndack _ _ _} nm _ ()
sepDisj {_ , rcvack _ _ _} nm _ ()
sepDisj {_ , ack    _ _ _} nm _ ()
sepDisj {_ , break  _}     nm _ ()
sepDisj {_ , done   _ _ _} nm (i , k , ()) _
sepDisj {_ , apiCS  _ _ _} nm (i , k , ()) _
sepDisj {_ , apiBF  _ _ _} nm (i , k , ()) _
sepDisj {_ , apiTS  _ _ _} nm (i , k , ()) _
sepDisj {_ , apiKA  _ _ _} nm (i , k , ()) _
sepDisj {_ , apiLN  _ _ _} nm (i , k , ()) _
sepDisj {_ , apiLF  _ _ _} nm (i , k , ()) _
sepDisj {_ , store  _ _ _} nm (i , k , ()) _
sepDisj {_ , env    _ _ _} nm (i , k , ()) _

-- the two `Sep ioES` witnesses `cong-Par⊤-L` demands (impl pair and spec pair)
sepN : (blkA : Block₃)
     → Sep ioES NetworkLinkBreakableA (nodeA blkA ⦀ (nodeB ⦀ (nodeC ⦀ nodeD)))
sepN blkA = sep-from-OffersOnly {α = unionAlpha linkAlphaA} {β = nodeAlpha}
              ioES (λ {at} {a} → sepDisj {at} {a}) oo-mediumN (oo-nodes blkA)

sepC : (blkA : Block₃)
     → Sep ioES CopySpecBreakableA (nodeA blkA ⦀ (nodeB ⦀ (nodeC ⦀ nodeD)))
sepC blkA = sep-from-OffersOnly {α = unionAlpha linkAlphaA} {β = nodeAlpha}
              ioES (λ {at} {a} → sepDisj {at} {a}) oo-mediumC (oo-nodes blkA)

-- (B) THE SYSTEM EQUIVALENCE: swap the medium operand under `∥⇘ ioES ⇙` and `∖ ioES`
breakableSystem≈DR : (∀ l → linkConfig l ≢ [] × Unique (linkConfig l))
                   → (blkA : Block₃) → breakableSystemₗ blkA ≈DR breakableSystem blkA
breakableSystem≈DR hyp blkA =
  cong-∖ ioES (cong-Par⊤-L ioES (sepN blkA) (sepC blkA) (netLinkBreakable≈DR hyp))

-- the failures-divergences equivalence (FDR's [FD= both ways)
breakableSystem≈FD : (∀ l → linkConfig l ≢ [] × Unique (linkConfig l))
                   → (blkA : Block₃) → breakableSystemₗ blkA ≈FD breakableSystem blkA
breakableSystem≈FD hyp blkA = drbisim→≈FD (breakableSystem≈DR hyp blkA)

-- the two refinement directions separately
breakableSystem⊑FD : (∀ l → linkConfig l ≢ [] × Unique (linkConfig l))
                   → (blkA : Block₃) → breakableSystemₗ blkA ⊑FD breakableSystem blkA
breakableSystem⊑FD hyp blkA = proj₁ (breakableSystem≈FD hyp blkA)

breakableSystemSpec⊑FD : (∀ l → linkConfig l ≢ [] × Unique (linkConfig l))
                       → (blkA : Block₃) → breakableSystem blkA ⊑FD breakableSystemₗ blkA
breakableSystemSpec⊑FD hyp blkA = proj₂ (breakableSystem≈FD hyp blkA)
