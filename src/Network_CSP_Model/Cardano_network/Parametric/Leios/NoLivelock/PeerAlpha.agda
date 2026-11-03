{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Leios no-livelock, Stage C, Task 9b, HOP 1: the peer facts the assembly
-- reads through each renaming, lifted to a node's whole bundle.
--   * the relay GROUPS: each pairs the reports one peer owns (`rep g`, a
--     far-driven thread's trigger), the wire messages behind them on the
--     group's own protocol cells (`ww g`, a cell-keyed `WireW`) and the
--     commands that pay for those messages on the far side (`cmd g`)
--   * per peer side and group, `gc g ≤ gd g`: reports plus wire inputs are
--     at most wire outputs plus commands.  An owner pays its reports with
--     outputs (its relay), a sender its inputs with commands (its relay); a
--     peer of another protocol contributes nothing (its renaming alone: its
--     wire labels sit on its own cells, its api labels in its own family);
--     a same-family non-owner contributes nothing by its `-noRep`
--   * the base fact: H-labels and wire inputs are paid by api labels
--     (P1 and the renaming)
-- `bundleG`/`bundleB` lift both to `nodeBundleP` (its twelve instances).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.List using (List)
open import Cardano_network.Parametric.Topology using (Topology; module Topology)
open import Cardano_network.Parametric.Leios.LeiosInstanceP using (pL; lpF; VB; AllV; HP)

module Cardano_network.Parametric.Leios.NoLivelock.PeerAlpha
  (k m : ℕ) (tP : Topology (pL k m)) (vo : Topology.Node tP → Fin m) (U : List (VB m)) (allV : AllV m U) where

-- the family member this module is about
pP = pL k m
-- its Leios parameters
lpP = lpF k m
-- the hidden set of this family member
HK = HP k m
open Topology tP using (Node)


open import Data.Bool using (Bool; true; false; if_then_else_; T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s; _≤ᵇ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; +-mono-≤; +-identityʳ; m≤m+n; m≤n+m; ≤ᵇ⇒≤; +-assoc; m+n≡0⇒m≡0; m+n≡0⇒n≡0)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Level using (0ℓ)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Class.DecEq using (_≟_)

open import Process_Trees using (ExtI; PTree)
open import Cardano_network.Base
open import Cardano_network.Net pP
open import Cardano_network.Data pP
open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using (Event; evLabel)
open import Semantics.Failures {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using (_⟹⟨_⟩_)
open import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) using (_⦀_; Skip; ∅ES)
open import CSP.Laws.DivFree.Count (Net_Api-≟ {Payload}) using (Σc; labels; AllL; []; _∷_; AllL-map)
open import CSP.Laws.DivFree.CountMore (Net_Api-≟ {Payload}) using (Σc-⦀; χ; ≤-≡; +-inter)
open import CSP.Laws.Traces.TraceLawsParallelTrace (Net_Api-≟ {Payload}) using (Par-trace-elim)
open import Cardano_network.Parametric.Leios.PeersP pP using (Proc; clientPeerP; serverPeerP; nodeBundleP)
open import Cardano_network.Parametric.Leios.NoLivelock.Weights pP
open import Cardano_network.Parametric.Leios.NoLivelock.MediumRelay pP using (WireW; wO; wI)
open import Cardano_network.Parametric.Leios.NoLivelock.StoresProv k m tP vo U allV using (Σc-+; Σc-0)
open import Cardano_network.Parametric.Leios.NoLivelock.Threads k m tP vo using (Σc-≤; RetL)
open import Cardano_network.NetworkPar pP
  using (ιKA; ιKA⁻¹; ιKA-linv; ιBF; ιBF⁻¹; ιBF-linv; ιCS; ιCS⁻¹; ιCS-linv; ιTS; ιTS⁻¹; ιTS-linv
        ; KAclientA; KAserverA; BFclientA; BFserverA; CSclientA; CSserverA; TSclientA)
open import Cardano_network.Parametric.Leios.PeersP pP
  using (ιLNP; ιLNP⁻¹; ιLNP-linv; ιLFP; ιLFP⁻¹; ιLFP-linv; LNPclientA; LNPserverA; LFPclientA; LFPserverA)
open import Cardano_network.Parametric.Leios.PeersR pP using (TSserverRA)
import Cardano_network.KeepAlive pP as KAm
import Cardano_network.BlockFetch pP as BFm
import Cardano_network.ChainSync pP as CSm
import Cardano_network.TxSubmission pP as TSm
import Cardano_network.LeiosNotifyP pP as LNm
import Cardano_network.LeiosFetchP pP as LFm
import CSP.Rename {E₁ = KAm.KAEv} {E₂ = Net_Api Payload} ιKA ιKA⁻¹ ιKA-linv as RKA
import CSP.Rename {E₁ = BFm.BFEv} {E₂ = Net_Api Payload} ιBF ιBF⁻¹ ιBF-linv as RBF
import CSP.Rename {E₁ = CSm.CSEv} {E₂ = Net_Api Payload} ιCS ιCS⁻¹ ιCS-linv as RCS
import CSP.Rename {E₁ = TSm.TSEv} {E₂ = Net_Api Payload} ιTS ιTS⁻¹ ιTS-linv as RTS
import CSP.Rename {E₁ = LNm.LNPEv} {E₂ = Net_Api Payload} ιLNP ιLNP⁻¹ ιLNP-linv as RLN
import CSP.Rename {E₁ = LFm.LFPEv} {E₂ = Net_Api Payload} ιLFP ιLFP⁻¹ ιLFP-linv as RLF
import Semantics.LTS {E = KAm.KAEv} {I = ExtI KAm.KAEv} as LKA
import Semantics.LTS {E = BFm.BFEv} {I = ExtI BFm.BFEv} as LBF
import Semantics.LTS {E = CSm.CSEv} {I = ExtI CSm.CSEv} as LCS
import Semantics.LTS {E = TSm.TSEv} {I = ExtI TSm.TSEv} as LTS
import Semantics.LTS {E = LNm.LNPEv} {I = ExtI LNm.LNPEv} as LLN
import Semantics.LTS {E = LFm.LFPEv} {I = ExtI LFm.LFPEv} as LLF
open import Cardano_network.Parametric.Leios.NoLivelock.PeerKA pP using (ιKA-rinv; kaClientA-P1; kaServerA-P1)
open import Cardano_network.Parametric.Leios.NoLivelock.ProvBF pP using (ιBF-rinv)
open import Cardano_network.Parametric.Leios.NoLivelock.PeerBF pP using (bfClientA-P1; bfServerA-P1)
open import Cardano_network.Parametric.Leios.NoLivelock.PeerCS pP
  using (ιCS-rinv; csClientA-P1; csServerA-P1; csClientA-rep; csClientA-noRF; csServerA-RF; csServerA-noRep)
open import Cardano_network.Parametric.Leios.NoLivelock.PeerTS pP
  using (ιTS-rinv; tsClientA-P1; tsServerA-P1; tsClientA-ids; tsClientA-txs; tsServerA-ids; tsServerA-txs
        ; tsServerA-noIds; tsServerA-noTxs; tsClientA-noRep)
open import Cardano_network.Parametric.Leios.NoLivelock.PeerLNP pP
  using (cCmdN; cRepN; ιLNP-rinv; lnpClientA-P1; lnpServerA-P1; lnpClientA-rep; lnpClientA-votes; lnpClientA-noN
        ; lnpServerA-notif; lnpServerA-votes; lnpClientA-votesN; lnpClientA-noV; lnpClientA-noRep
        ; lnpServerA-votesN; lnpServerA-noRep)
open import Cardano_network.Parametric.Leios.NoLivelock.PeerLFP pP
  using (ιLFP-rinv; lfpClientA-P1; lfpServerA-P1; lfpClientA-bq; lfpClientA-tq; lfpClientA-bm; lfpClientA-es
        ; lfpClientA-noBT; lfpServerA-bq; lfpServerA-tq; lfpServerA-bm; lfpServerA-noBQ; lfpServerA-noTQ
        ; lfpServerA-es; lfpClientA-noRep; lfpServerA-noRep)
open import CSP.Laws.DivFree.RenAlpha ιKA ιKA⁻¹ ιKA-linv ιKA-rinv KAm.KAEv-≟ (Net_Api-≟ {Payload}) using () renaming (AllL-ren to renKA)
open import CSP.Laws.DivFree.RenAlpha ιBF ιBF⁻¹ ιBF-linv ιBF-rinv BFm.BFEv-≟ (Net_Api-≟ {Payload}) using () renaming (AllL-ren to renBF)
open import CSP.Laws.DivFree.RenAlpha ιCS ιCS⁻¹ ιCS-linv ιCS-rinv CSm.CSEv-≟ (Net_Api-≟ {Payload}) using () renaming (AllL-ren to renCS)
open import CSP.Laws.DivFree.RenAlpha ιTS ιTS⁻¹ ιTS-linv ιTS-rinv TSm.TSEv-≟ (Net_Api-≟ {Payload}) using () renaming (AllL-ren to renTS)
open import CSP.Laws.DivFree.RenAlpha ιLNP ιLNP⁻¹ ιLNP-linv ιLNP-rinv LNm.LNPEv-≟ (Net_Api-≟ {Payload}) using () renaming (AllL-ren to renLN)
open import CSP.Laws.DivFree.RenAlpha ιLFP ιLFP⁻¹ ιLFP-linv ιLFP-rinv LFm.LFPEv-≟ (Net_Api-≟ {Payload}) using () renaming (AllL-ren to renLF)

------------------------------------------------------------------------
-- the relay groups
------------------------------------------------------------------------

-- the message a payload carries
msg : Payload → Messages
msg (_ , _ , _ , m) = m

-- `f` of the message, on the cells of protocol `i` only
cw : IDs → (Messages → ℕ) → WireW
cw i f l d id pl = if ⌊ id ≟ i ⌋ then f (msg pl) else 0

-- one on every wire label
one : WireW
one _ _ _ _ = 1

-- the relay groups (one reporting peer side each)
data Gr : Set where
  gRF gTS gLN gTQ gBT gBQ : Gr

-- a group's protocol
gid : Gr → IDs
gid gRF = N2N_ChainSync
gid gTS = N2N_TxSubmission
gid gLN = N2N_LeiosNotify
gid gTQ = N2N_LeiosFetch
gid gBT = N2N_LeiosFetch
gid gBQ = N2N_LeiosFetch

-- a group's message weight
gf : Gr → Messages → ℕ
gf gRF m = isK RF m
gf gTS m = isK ReplyTxIds m + ℓK ReplyTxs m
gf gLN m = isK notif m + (isK votes m + ℓK votes m)
gf gTQ m = isK TxsReq m + ℓK TxsReq m
gf gBT m = ℓK BlockTxs m
gf gBQ m = isK BlockReq m

-- a group's cell-keyed wire weight
ww : Gr → WireW
ww g = cw (gid g) (gf g)

-- a group's reports (the trigger of a far-driven thread)
rep : Gr → Event → ℕ
rep gRF   = cRep recvCSRollforward
rep gTS   = repTS
rep gLN   = repLNP
rep gTQ e = cRep lfpReqBlockTxsRequest e + ℓRep lfpReqBlockTxsRequest e
rep gBT   = repLFc
rep gBQ   = cRep lfpReqBlockRequest

-- a group's commands (what pays its wire messages)
cmd : Gr → Event → ℕ
cmd gRF   = cCmd sendCSRollForward
cmd gTS e = cCmd sendTSReplyTxIds e + ℓCmd sendTSReplyTxs e
cmd gLN e = cCmdN e + (cCmd lnpSendVotes e + ℓCmd lnpSendVotes e)
cmd gTQ e = cCmd lfpSendBlockTxsRequest e + ℓCmd lfpSendBlockTxsRequest e
cmd gBT   = ℓCmd lfpSendBlockTxs
cmd gBQ   = cCmd lfpSendBlockRequest

-- a group's cost at a peer: reports plus wire inputs
gc : Gr → Event → ℕ
gc g e = rep g e + wI (ww g) e

-- a group's credit at a peer: wire outputs plus commands
gd : Gr → Event → ℕ
gd g e = wO (ww g) e + cmd g e

-- every run of `P` costs at most its credit plus `k`
Rl : (Event → ℕ) → (Event → ℕ) → ℕ → Proc → Set₁
Rl c d k P = ∀ {s W} → P ⟹⟨ s ⟩ W → Σc c (labels s) ≤ Σc d (labels s) + k

------------------------------------------------------------------------
-- generic helpers
------------------------------------------------------------------------

-- zero, as a type (a concrete obligation is then solved by eta)
IsZ : ℕ → Set
IsZ zero    = ⊤
IsZ (suc _) = ⊥

-- … is zero
isZ≡ : ∀ {n} → IsZ n → n ≡ 0
isZ≡ {zero} _ = refl

-- a fact of every label
allL : ∀ {P : Event → Set} → (∀ e → P e) → ∀ ls → AllL P ls
allL f []       = []
allL f (e ∷ ls) = f e ∷ allL f ls

-- two facts of every label
zipL : ∀ {P Q : Event → Set} {ls} → AllL P ls → AllL Q ls → AllL (λ e → P e × Q e) ls
zipL []       []       = []
zipL (p ∷ ps) (q ∷ qs) = (p , q) ∷ zipL ps qs

-- a zero sum is zero on every label
Σ0→ : ∀ {c : Event → ℕ} ls → Σc c ls ≡ 0 → AllL (λ e → c e ≡ 0) ls
Σ0→ []       _ = []
Σ0→ {c} (e ∷ ls) h = m+n≡0⇒m≡0 (c e) h ∷ Σ0→ ls (m+n≡0⇒n≡0 (c e) h)

-- a weight below a zero-sum weight sums to zero
zsub : ∀ {c d : Event → ℕ} {ls} → Σc d ls ≡ 0 → (∀ {e} → d e ≡ 0 → c e ≡ 0) → Σc c ls ≡ 0
zsub {c} {ls = ls} h f = Σc-0 c (AllL-map f (Σ0→ ls h))

-- equal weights sum equally
Σc-cong : ∀ {c d : Event → ℕ} {ls} → AllL (λ e → c e ≡ d e) ls → Σc c ls ≡ Σc d ls
Σc-cong []      = refl
Σc-cong (p ∷ a) = cong₂ _+_ p (Σc-cong a)

-- a zero sum is below anything
≤0 : ∀ {c d : Event → ℕ} {ls} → Σc c ls ≡ 0 → Σc c ls ≤ Σc d ls
≤0 h = subst (_≤ _) (sym h) z≤n

-- two bounds add up, weight by weight
two≤ : ∀ {a a′ b b′ : Event → ℕ} {ls} → Σc a ls ≤ Σc a′ ls → Σc b ls ≤ Σc b′ ls
     → Σc (λ e → a e + b e) ls ≤ Σc (λ e → a′ e + b′ e) ls
two≤ {a} {a′} {b} {b′} {ls} p q =
  subst₂ _≤_ (sym (Σc-+ a b ls)) (sym (Σc-+ a′ b′ ls)) (+-mono-≤ p q)

------------------------------------------------------------------------
-- process bounds and the bundle
------------------------------------------------------------------------

-- interleaving adds the slacks
rl-⦀ : ∀ {c d k₁ k₂} {P Q : Proc} → Rl c d k₁ P → Rl c d k₂ Q → Rl c d (k₁ + k₂) (P ⦀ Q)
rl-⦀ {c} {d} {k₁} {k₂} {P} {Q} p q tr with Par-trace-elim ∅ES _ P Q tr
... | sP , sQ , _ , _ , tP , tQ , pi =
  subst₂ (λ x y → x ≤ y + (k₁ + k₂)) (sym (Σc-⦀ c pi)) (sym (Σc-⦀ d pi))
    (≤-trans (+-mono-≤ (p tP) (q tQ)) (≤-≡ (+-inter (Σc d (labels sP)) k₁ (Σc d (labels sQ)) k₂)))

-- `Skip` costs nothing
rl-Skip : ∀ {c d k} → Rl c d k Skip
rl-Skip tr rewrite RetL tr = z≤n

-- a conditional
rl-if : ∀ {c d k} {P Q : Proc} b → Rl c d k P → Rl c d k Q → Rl c d k (if b then P else Q)
rl-if true  p q = p
rl-if false p q = q

-- the bundle, from every client and server instance (twelve, as `TauAssembly.bundle-R`)
bundle-Rl : ∀ {c d k} → (∀ l d₀ id → Rl c d k (clientPeerP l d₀ id)) → (∀ l d₀ id → Rl c d k (serverPeerP l d₀ id))
          → ∀ l cl sv → Rl c d (12 * k) (nodeBundleP l cl sv)
bundle-Rl {c} {d} {k} pc ps l cl sv =
  rl-⦀ (pk lo N2N_KeepAlive)    (rl-⦀ (pk hi N2N_KeepAlive)
  (rl-⦀ (pk lo N2N_ChainSync)   (rl-⦀ (pk hi N2N_ChainSync)
  (rl-⦀ (pk lo N2N_BlockFetch)  (rl-⦀ (pk hi N2N_BlockFetch)
  (rl-⦀ (pk lo N2N_TxSubmission) (rl-⦀ (pk hi N2N_TxSubmission)
  (rl-⦀ (pk lo N2N_LeiosNotify) (rl-⦀ (pk hi N2N_LeiosNotify)
  (rl-⦀ (pk lo N2N_LeiosFetch)  (rl-⦀ (pk hi N2N_LeiosFetch) rl-Skip)))))))))))
  where
    -- one configured instance, dispatched by direction
    pk : ∀ d₀ id → Rl c d k (if ⌊ d₀ ≟ cl ⌋ then clientPeerP l d₀ id else if ⌊ d₀ ≟ sv ⌋ then serverPeerP l d₀ id else Skip)
    pk d₀ id = rl-if ⌊ d₀ ≟ cl ⌋ (pc l d₀ id) (rl-if ⌊ d₀ ≟ sv ⌋ (ps l d₀ id) rl-Skip)

------------------------------------------------------------------------
-- the renaming facts, per protocol
------------------------------------------------------------------------

-- the base facts of a peer label: an H-label is a wire or api label; a wire input is an input
PB : Event → Set
PB e = T (χ HK e ≤ᵇ cIn e + (wO one e + cApi e)) × T (wI one e ≤ᵇ cIn e)

-- how a group vanishes on a protocol's labels: entirely, on the wire only, or not at all
data Zk : Set where
  full wire none : Zk

-- the vanishing of one group
comp : Zk → Gr → Event → Set
comp full g e = IsZ (gc g e)
comp wire g e = IsZ (wI (ww g) e)
comp none g e = ⊤

-- the vanishing of every group, by a mask
ZG : (Gr → Zk) → Event → Set
ZG m e = comp (m gRF) gRF e × (comp (m gTS) gTS e × (comp (m gLN) gLN e
       × (comp (m gTQ) gTQ e × (comp (m gBT) gBT e × comp (m gBQ) gBQ e))))

-- … read for one group
sel : ∀ m g {e} → ZG m e → comp (m g) g e
sel m gRF z = proj₁ z
sel m gTS z = proj₁ (proj₂ z)
sel m gLN z = proj₁ (proj₂ (proj₂ z))
sel m gTQ z = proj₁ (proj₂ (proj₂ (proj₂ z)))
sel m gBT z = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ z))))
sel m gBQ z = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ z))))

-- a protocol's label facts: base, own-group conversions `Cv`, vanishing by mask (a record,
-- so that `Cv` and the mask are recovered by unification)
record Pt (Cv : Event → Set) (m : Gr → Zk) (e : Event) : Set where
  constructor pt
  field
    pb : PB e
    cv : Cv e
    zg : ZG m e

-- KeepAlive and BlockFetch own no group
mKB : Gr → Zk
mKB _ = full

-- ChainSync owns RollForward
mCS : Gr → Zk
mCS gRF = none
mCS _   = full

-- TxSubmission owns the tx replies
mTS : Gr → Zk
mTS gTS = none
mTS _   = full

-- LeiosNotify owns the notifications; the LeiosFetch groups share its api family
mLN : Gr → Zk
mLN gRF = full
mLN gTS = full
mLN gLN = none
mLN _   = wire

-- LeiosFetch owns its three groups; LeiosNotify's shares its api family
mLF : Gr → Zk
mLF gRF = full
mLF gTS = full
mLF gLN = wire
mLF _   = none

-- no conversion
Cv0 : Event → Set
Cv0 _ = ⊤

-- ChainSync: its group's wire weight is the RollForward weight
CvCS : Event → Set
CvCS e = (wI (ww gRF) e ≡ wIn RF e) × (wO (ww gRF) e ≡ wOut RF e)

-- TxSubmission: its group's wire weight, and the reply-list lengths vanish with the replies
CvTS : Event → Set
CvTS e = (wI (ww gTS) e ≡ wIn ReplyTxIds e + ℓIn ReplyTxs e) × (wO (ww gTS) e ≡ wOut ReplyTxIds e + ℓOut ReplyTxs e)
       × (wIn ReplyTxs e ≡ 0 → ℓIn ReplyTxs e ≡ 0)

-- LeiosNotify: likewise for notifications and votes
CvLN : Event → Set
CvLN e = (wI (ww gLN) e ≡ wIn notif e + (wIn votes e + ℓIn votes e))
       × (wO (ww gLN) e ≡ wOut notif e + (wOut votes e + ℓOut votes e))
       × (wIn votes e ≡ 0 → ℓIn votes e ≡ 0)

-- LeiosFetch: likewise for its three groups
CvLF : Event → Set
CvLF e = ((wI (ww gTQ) e ≡ wIn TxsReq e + ℓIn TxsReq e) × (wO (ww gTQ) e ≡ wOut TxsReq e + ℓOut TxsReq e))
       × ((wI (ww gBT) e ≡ ℓIn BlockTxs e) × (wO (ww gBT) e ≡ ℓOut BlockTxs e))
       × ((wI (ww gBQ) e ≡ wIn BlockReq e) × (wO (ww gBQ) e ≡ wOut BlockReq e))
       × (wIn TxsReq e ≡ 0 → ℓIn TxsReq e ≡ 0) × (wIn BlockTxs e ≡ 0 → ℓIn BlockTxs e ≡ 0)

-- vote lists come only with votes messages
ℓ0v : ∀ m → isK votes m ≡ 0 → ℓK votes m ≡ 0
ℓ0v (keepAlive _)    _ = refl
ℓ0v (blockFetch _)   _ = refl
ℓ0v (chainSync _)    _ = refl
ℓ0v (txSubmission _) _ = refl
ℓ0v (leiosNotify _)  _ = refl
ℓ0v (leiosFetch _)   _ = refl
ℓ0v (leiosFetchP _)  _ = refl
ℓ0v (leiosNotifyP MsgLNPRequestNext)            _ = refl
ℓ0v (leiosNotifyP (MsgLNPBlockAnnouncement _))  _ = refl
ℓ0v (leiosNotifyP (MsgLNPBlockOffer _ _))       _ = refl
ℓ0v (leiosNotifyP (MsgLNPBlockTxsOffer _))      _ = refl
ℓ0v (leiosNotifyP (MsgLNPVotes _))              ()
ℓ0v (leiosNotifyP MsgLNPDone)                   _ = refl
ℓ0v (leiosNotifyP MsgLNPQuit)                   _ = refl
ℓ0v (leiosNotifyP MsgLNPCanceled)               _ = refl

-- bitmaps come only with closure requests
ℓ0q : ∀ m → isK TxsReq m ≡ 0 → ℓK TxsReq m ≡ 0
ℓ0q (keepAlive _)    _ = refl
ℓ0q (blockFetch _)   _ = refl
ℓ0q (chainSync _)    _ = refl
ℓ0q (txSubmission _) _ = refl
ℓ0q (leiosNotify _)  _ = refl
ℓ0q (leiosFetch _)   _ = refl
ℓ0q (leiosNotifyP _) _ = refl
ℓ0q (leiosFetchP (MsgLFPBlockRequest _))      _ = refl
ℓ0q (leiosFetchP (MsgLFPBlock _))             _ = refl
ℓ0q (leiosFetchP (MsgLFPBlockTxsRequest _ _)) ()
ℓ0q (leiosFetchP (MsgLFPBlockTxs _ _))        _ = refl
ℓ0q (leiosFetchP MsgLFPDone)                  _ = refl

-- closure entries come only with closure replies
ℓ0b : ∀ m → isK BlockTxs m ≡ 0 → ℓK BlockTxs m ≡ 0
ℓ0b (keepAlive _)    _ = refl
ℓ0b (blockFetch _)   _ = refl
ℓ0b (chainSync _)    _ = refl
ℓ0b (txSubmission _) _ = refl
ℓ0b (leiosNotify _)  _ = refl
ℓ0b (leiosFetch _)   _ = refl
ℓ0b (leiosNotifyP _) _ = refl
ℓ0b (leiosFetchP (MsgLFPBlockRequest _))      _ = refl
ℓ0b (leiosFetchP (MsgLFPBlock _))             _ = refl
ℓ0b (leiosFetchP (MsgLFPBlockTxsRequest _ _)) _ = refl
ℓ0b (leiosFetchP (MsgLFPBlockTxs _ _))        ()
ℓ0b (leiosFetchP MsgLFPDone)                  _ = refl

-- tx lists come only with tx replies
ℓ0r : ∀ m → isK ReplyTxs m ≡ 0 → ℓK ReplyTxs m ≡ 0
ℓ0r (keepAlive _)    _ = refl
ℓ0r (blockFetch _)   _ = refl
ℓ0r (chainSync _)    _ = refl
ℓ0r (leiosNotify _)  _ = refl
ℓ0r (leiosFetch _)   _ = refl
ℓ0r (leiosNotifyP _) _ = refl
ℓ0r (leiosFetchP _)  _ = refl
ℓ0r (txSubmission MsgTSInit)                 _ = refl
ℓ0r (txSubmission (MsgTSRequestTxIds _ _ _)) _ = refl
ℓ0r (txSubmission (MsgTSReplyTxIds _))       _ = refl
ℓ0r (txSubmission (MsgTSRequestTxs _))       _ = refl
ℓ0r (txSubmission (MsgTSReplyTxs _))         ()
ℓ0r (txSubmission MsgTSDone)                 _ = refl

-- every KeepAlive peer label
ptKA : ∀ {ℓr} {R : Set ℓr} {P : PTree KAm.KAEv (ExtI KAm.KAEv) R} {s W} → RKA.renameMap P ⟹⟨ s ⟩ W → AllL (Pt Cv0 mKB) (labels s)
ptKA = renKA λ
  { (LKA.evLabel _ (KAm.sendKA _ _) _)    → _
  ; (LKA.evLabel _ (KAm.receiveKA _ _) _) → _
  ; (LKA.evLabel _ (KAm.apiKAev _ _ _) _) → _
  ; (LKA.evLabel _ (KAm.doneKA _ _) _)    → _ }

-- every BlockFetch peer label
ptBF : ∀ {ℓr} {R : Set ℓr} {P : PTree BFm.BFEv (ExtI BFm.BFEv) R} {s W} → RBF.renameMap P ⟹⟨ s ⟩ W → AllL (Pt Cv0 mKB) (labels s)
ptBF = renBF λ
  { (LBF.evLabel _ (BFm.sendBF _ _) _)    → _
  ; (LBF.evLabel _ (BFm.receiveBF _ _) _) → _
  ; (LBF.evLabel _ (BFm.apiBFev _ _ _) _) → _
  ; (LBF.evLabel _ (BFm.doneBF _ _) _)    → _ }

-- every ChainSync peer label
ptCS : ∀ {ℓr} {R : Set ℓr} {P : PTree CSm.CSEv (ExtI CSm.CSEv) R} {s W} → RCS.renameMap P ⟹⟨ s ⟩ W → AllL (Pt CvCS mCS) (labels s)
ptCS = renCS λ
  { (LCS.evLabel _ (CSm.sendCS _ _) _)    → pt _ (refl , refl) _
  ; (LCS.evLabel _ (CSm.receiveCS _ _) _) → pt _ (refl , refl) _
  ; (LCS.evLabel _ (CSm.apiCSev _ _ _) _) → pt _ (refl , refl) _
  ; (LCS.evLabel _ (CSm.doneCS _ _) _)    → pt _ (refl , refl) _ }

-- every TxSubmission peer label
ptTS : ∀ {ℓr} {R : Set ℓr} {P : PTree TSm.TSEv (ExtI TSm.TSEv) R} {s W} → RTS.renameMap P ⟹⟨ s ⟩ W → AllL (Pt CvTS mTS) (labels s)
ptTS = renTS λ
  { (LTS.evLabel _ (TSm.sendTS _ _) x)    → pt _ (refl , refl , ℓ0r (msg x)) _
  ; (LTS.evLabel _ (TSm.receiveTS _ _) _) → pt _ (refl , refl , λ _ → refl) _
  ; (LTS.evLabel _ (TSm.apiTSev _ _ _) _) → pt _ (refl , refl , λ _ → refl) _
  ; (LTS.evLabel _ (TSm.doneTS _ _) _)    → pt _ (refl , refl , λ _ → refl) _ }

-- every LeiosNotify peer label
ptLN : ∀ {ℓr} {R : Set ℓr} {P : PTree LNm.LNPEv (ExtI LNm.LNPEv) R} {s W} → RLN.renameMap P ⟹⟨ s ⟩ W → AllL (Pt CvLN mLN) (labels s)
ptLN = renLN λ
  { (LLN.evLabel _ (LNm.sendLNP _ _) x)    → pt _ (refl , refl , ℓ0v (msg x)) _
  ; (LLN.evLabel _ (LNm.receiveLNP _ _) _) → pt _ (refl , refl , λ _ → refl) _
  ; (LLN.evLabel _ (LNm.apiLPev _ _ _) _)  → pt _ (refl , refl , λ _ → refl) _
  ; (LLN.evLabel _ (LNm.doneLNP _ _) _)    → pt _ (refl , refl , λ _ → refl) _ }

-- every LeiosFetch peer label
ptLF : ∀ {ℓr} {R : Set ℓr} {P : PTree LFm.LFPEv (ExtI LFm.LFPEv) R} {s W} → RLF.renameMap P ⟹⟨ s ⟩ W → AllL (Pt CvLF mLF) (labels s)
ptLF = renLF λ
  { (LLF.evLabel _ (LFm.sendLFP _ _) x)    → pt _ ((refl , refl) , (refl , refl) , (refl , refl) , ℓ0q (msg x) , ℓ0b (msg x)) _
  ; (LLF.evLabel _ (LFm.receiveLFP _ _) _) → pt _ ((refl , refl) , (refl , refl) , (refl , refl) , (λ _ → refl) , (λ _ → refl)) _
  ; (LLF.evLabel _ (LFm.apiLPev _ _ _) _)  → pt _ ((refl , refl) , (refl , refl) , (refl , refl) , (λ _ → refl) , (λ _ → refl)) _
  ; (LLF.evLabel _ (LFm.doneLFP _ _) _)    → pt _ ((refl , refl) , (refl , refl) , (refl , refl) , (λ _ → refl) , (λ _ → refl)) _ }
------------------------------------------------------------------------
-- per side: the group facts and the base fact
------------------------------------------------------------------------

-- a group fact from its two halves
mkG : ∀ g {ls} → Σc (rep g) ls ≤ Σc (wO (ww g)) ls → Σc (wI (ww g)) ls ≤ Σc (cmd g) ls
    → Σc (gc g) ls ≤ Σc (gd g) ls + 0
mkG g {ls} r w =
  subst₂ _≤_ (sym (Σc-+ (rep g) (wI (ww g)) ls)) (sym (trans (+-identityʳ _) (Σc-+ (wO (ww g)) (cmd g) ls)))
    (+-mono-≤ r w)

-- a group that vanishes on a protocol's labels
zF : ∀ g {Cv m ls} → m g ≡ full → AllL (Pt Cv m) ls → Σc (gc g) ls ≤ Σc (gd g) ls + 0
zF g {m = m} {ls} eq a =
  subst (_≤ Σc (gd g) ls + 0) (sym (Σc-0 (gc g) (AllL-map (λ {e} z → isZ≡ (subst (λ k → comp k g e) eq (sel m g (Pt.zg z)))) a))) z≤n

-- a group whose wire weight vanishes on a protocol's labels
zW : ∀ g {Cv m ls} → m g ≡ wire → AllL (Pt Cv m) ls → Σc (wI (ww g)) ls ≡ 0
zW g {m = m} eq a = Σc-0 (wI (ww g)) (AllL-map (λ {e} z → isZ≡ (subst (λ k → comp k g e) eq (sel m g (Pt.zg z)))) a)

-- the conversions of a protocol's labels
cvs : ∀ {Cv m ls} → AllL (Pt Cv m) ls → AllL Cv ls
cvs = AllL-map Pt.cv

-- apply label-wise implications
appL : ∀ {P Q : Event → Set} {ls} → AllL (λ e → P e → Q e) ls → AllL P ls → AllL Q ls
appL []       []       = []
appL (f ∷ fs) (p ∷ ps) = f p ∷ appL fs ps

-- two weights vanishing label-wise: their sum sums to zero
sum0 : ∀ {a b : Event → ℕ} {ls} → AllL (λ e → a e ≡ 0) ls → AllL (λ e → b e ≡ 0) ls → Σc (λ e → a e + b e) ls ≡ 0
sum0 {a} {b} p q = Σc-0 (λ e → a e + b e) (AllL-map (λ { (x , y) → cong₂ _+_ x y }) (zipL p q))

-- THE BASE FACT of one peer: P1 and the renaming
baseF : ∀ {Cv m ls} → Σc cIn ls ≤ Σc cApi ls + 1 → AllL (Pt Cv m) ls
      → Σc (λ e → χ HK e + wI one e) ls ≤ Σc (λ e → cApi e + (cApi e + (cApi e + wO one e))) ls + 2
baseF {ls = ls} p1 a =
  subst₂ _≤_ (sym (Σc-+ (χ HK) (wI one) ls))
    (sym (cong (_+ 2) (trans (Σc-+ cApi _ ls) (cong (A +_) (trans (Σc-+ cApi _ ls) (cong (A +_) (Σc-+ cApi (wO one) ls)))))))
    (≤-trans (+-mono-≤ hX hW)
      (≤-trans (+-mono-≤ (+-monoˡ-≤′ (O + A) p1) p1) (≤-≡ (solve 2 (λ A O → ((A :+ con 1) :+ (O :+ A)) :+ (A :+ con 1)
                                                                        := (A :+ (A :+ (A :+ O))) :+ con 2) refl A O))))
  where
    open +-*-Solver
    -- the api, output and input totals
    A = Σc cApi ls
    O = Σc (wO one) ls
    I = Σc cIn ls
    -- adding on the right is monotone
    +-monoˡ-≤′ : ∀ n {x y} → x ≤ y → x + n ≤ y + n
    +-monoˡ-≤′ n h = +-mono-≤ h (≤-refl {n})
    -- an H-label is a wire or api label
    hX : Σc (χ HK) ls ≤ I + (O + A)
    hX = ≤-trans (Σc-≤ (AllL-map (λ z → ≤ᵇ⇒≤ _ _ (proj₁ (Pt.pb z))) a))
                 (≤-≡ (trans (Σc-+ cIn _ ls) (cong (I +_) (Σc-+ (wO one) cApi ls))))
    -- a wire input is an input
    hW : Σc (wI one) ls ≤ I
    hW = Σc-≤ (AllL-map (λ z → ≤ᵇ⇒≤ _ _ (proj₂ (Pt.pb z))) a)

-- the Notify reports split into the notifications, the vote count and the vote lengths
lnSplit : ∀ e → repLNP e ≡ cRepN e + (cRep lnpRecvVotes e + ℓRep lnpRecvVotes e)
lnSplit e = solve 5 (λ a b c d v → a :+ (b :+ (c :+ (d :+ v))) := ((a :+ b) :+ c) :+ (d :+ v)) refl
              (cRep lnpRecvBlockAnnouncement e) (cRep lnpRecvBlockOffer e) (cRep lnpRecvBlockTxsOffer e)
              (cRep lnpRecvVotes e) (ℓRep lnpRecvVotes e)
  where open +-*-Solver

-- ChainSync client: owns the RollForward reports, receives (never sends) RollForwards
csCG : ∀ g l d → Rl (gc g) (gd g) 0 (CSclientA l d)
csCG gRF l d {s} tr = mkG gRF {labels s} (≤-trans (csClientA-rep l d tr) (≤-≡ (sym (Σc-cong (AllL-map proj₂ (cvs (ptCS tr)))))))
                    (≤0 {ls = labels s} (trans (Σc-cong (AllL-map proj₁ (cvs (ptCS tr)))) (csClientA-noRF l d tr)))
csCG gTS l d {s} tr = zF gTS refl (ptCS tr)
csCG gLN l d {s} tr = zF gLN refl (ptCS tr)
csCG gTQ l d {s} tr = zF gTQ refl (ptCS tr)
csCG gBT l d {s} tr = zF gBT refl (ptCS tr)
csCG gBQ l d {s} tr = zF gBQ refl (ptCS tr)

-- ChainSync server: sends the commanded RollForwards, reports none
csSG : ∀ g l d → Rl (gc g) (gd g) 0 (CSserverA l d)
csSG gRF l d {s} tr = mkG gRF {labels s} (≤0 {ls = labels s} (csServerA-noRep l d tr))
                    (≤-trans (≤-≡ (Σc-cong (AllL-map proj₁ (cvs (ptCS tr))))) (csServerA-RF l d tr))
csSG gTS l d {s} tr = zF gTS refl (ptCS tr)
csSG gLN l d {s} tr = zF gLN refl (ptCS tr)
csSG gTQ l d {s} tr = zF gTQ refl (ptCS tr)
csSG gBT l d {s} tr = zF gBT refl (ptCS tr)
csSG gBQ l d {s} tr = zF gBQ refl (ptCS tr)

-- TxSubmission submitter: sends the commanded replies, reports none
tsCG : ∀ g l d → Rl (gc g) (gd g) 0 (TSclientA l d)
tsCG gTS l d {s} tr = mkG gTS {labels s} (≤0 {ls = labels s} (tsClientA-noRep l d tr))
                    (≤-trans (≤-≡ (Σc-cong (AllL-map proj₁ (cvs (ptTS tr))))) (two≤ {ls = labels s} (tsClientA-ids l d tr) (tsClientA-txs l d tr)))
tsCG gRF l d {s} tr = zF gRF refl (ptTS tr)
tsCG gLN l d {s} tr = zF gLN refl (ptTS tr)
tsCG gTQ l d {s} tr = zF gTQ refl (ptTS tr)
tsCG gBT l d {s} tr = zF gBT refl (ptTS tr)
tsCG gBQ l d {s} tr = zF gBQ refl (ptTS tr)

-- TxSubmission requester: owns the reply reports, receives (never sends) replies
tsSG : ∀ g l d → Rl (gc g) (gd g) 0 (TSserverRA l d)
tsSG gTS l d {s} tr = mkG gTS {labels s} (≤-trans (two≤ {ls = labels s} (tsServerA-ids l d tr) (tsServerA-txs l d tr)) (≤-≡ (sym (Σc-cong (AllL-map (λ z → proj₁ (proj₂ z)) cv)))))
                        (≤0 {ls = labels s} (trans (Σc-cong (AllL-map proj₁ cv))
                               (sum0 {ls = labels s} (Σ0→ (labels s) (tsServerA-noIds l d tr))
                                     (appL (AllL-map (λ z → proj₂ (proj₂ z)) cv) (Σ0→ (labels s) (tsServerA-noTxs l d tr))))))
  where
    -- the conversions of its labels
    cv = cvs (ptTS tr)
tsSG gRF l d {s} tr = zF gRF refl (ptTS tr)
tsSG gLN l d {s} tr = zF gLN refl (ptTS tr)
tsSG gTQ l d {s} tr = zF gTQ refl (ptTS tr)
tsSG gBT l d {s} tr = zF gBT refl (ptTS tr)
tsSG gBQ l d {s} tr = zF gBQ refl (ptTS tr)

-- LeiosNotify client: owns the Notify reports, receives (never sends) notifications and votes
lnCG : ∀ g l d → Rl (gc g) (gd g) 0 (LNPclientA l d)
lnCG gLN l d {s} tr =
  mkG gLN {labels s} (≤-trans (≤-≡ (Σc-cong (allL lnSplit (labels s))))
             (≤-trans (two≤ {ls = labels s} (lnpClientA-rep l d tr) (two≤ {ls = labels s} (lnpClientA-votesN l d tr) (lnpClientA-votes l d tr)))
               (≤-≡ (sym (Σc-cong (AllL-map (λ z → proj₁ (proj₂ z)) cv))))))
          (≤0 {ls = labels s} (trans (Σc-cong (AllL-map proj₁ cv))
                 (sum0 {ls = labels s} (Σ0→ (labels s) (lnpClientA-noN l d tr))
                   (AllL-map (λ { (x , y) → cong₂ _+_ x y })
                     (zipL (Σ0→ (labels s) (lnpClientA-noV l d tr))
                           (appL (AllL-map (λ z → proj₂ (proj₂ z)) cv) (Σ0→ (labels s) (lnpClientA-noV l d tr))))))))
  where
    -- the conversions of its labels
    cv = cvs (ptLN tr)
lnCG gRF l d {s} tr = zF gRF refl (ptLN tr)
lnCG gTS l d {s} tr = zF gTS refl (ptLN tr)
lnCG gTQ l d {s} tr = mkG gTQ {labels s} (≤0 {ls = labels s} (zsub {ls = labels s} (lnpClientA-noRep l d tr) (λ {e} h → m+n≡0⇒n≡0 (rep gBQ e) (m+n≡0⇒n≡0 (repLFc e) h)))) (≤0 {ls = labels s} (zW gTQ refl (ptLN tr)))
lnCG gBT l d {s} tr = mkG gBT {labels s} (≤0 {ls = labels s} (zsub {ls = labels s} (lnpClientA-noRep l d tr) (λ {e} h → m+n≡0⇒m≡0 (repLFc e) h))) (≤0 {ls = labels s} (zW gBT refl (ptLN tr)))
lnCG gBQ l d {s} tr = mkG gBQ {labels s} (≤0 {ls = labels s} (zsub {ls = labels s} (lnpClientA-noRep l d tr) (λ {e} h → m+n≡0⇒m≡0 (rep gBQ e) (m+n≡0⇒n≡0 (repLFc e) h)))) (≤0 {ls = labels s} (zW gBQ refl (ptLN tr)))

-- LeiosNotify server: sends the commanded notifications and votes, reports none
lnSG : ∀ g l d → Rl (gc g) (gd g) 0 (LNPserverA l d)
lnSG gLN l d {s} tr = mkG gLN {labels s} (≤0 {ls = labels s} (zsub {ls = labels s} (lnpServerA-noRep l d tr) (λ {e} h → m+n≡0⇒m≡0 (repLNP e) h)))
                    (≤-trans (≤-≡ (Σc-cong (AllL-map proj₁ (cvs (ptLN tr))))) (two≤ {ls = labels s} (lnpServerA-notif l d tr) (two≤ {ls = labels s} (lnpServerA-votesN l d tr) (lnpServerA-votes l d tr))))
lnSG gRF l d {s} tr = zF gRF refl (ptLN tr)
lnSG gTS l d {s} tr = zF gTS refl (ptLN tr)
lnSG gTQ l d {s} tr = mkG gTQ {labels s} (≤0 {ls = labels s} (zsub {ls = labels s} (lnpServerA-noRep l d tr) (λ {e} h → m+n≡0⇒n≡0 (rep gBQ e) (m+n≡0⇒n≡0 (repLFc e) (m+n≡0⇒n≡0 (repLNP e) h)))))
                    (≤0 {ls = labels s} (zW gTQ refl (ptLN tr)))
lnSG gBT l d {s} tr = mkG gBT {labels s} (≤0 {ls = labels s} (zsub {ls = labels s} (lnpServerA-noRep l d tr) (λ {e} h → m+n≡0⇒m≡0 (repLFc e) (m+n≡0⇒n≡0 (repLNP e) h)))) (≤0 {ls = labels s} (zW gBT refl (ptLN tr)))
lnSG gBQ l d {s} tr = mkG gBQ {labels s} (≤0 {ls = labels s} (zsub {ls = labels s} (lnpServerA-noRep l d tr) (λ {e} h → m+n≡0⇒m≡0 (rep gBQ e) (m+n≡0⇒n≡0 (repLFc e) (m+n≡0⇒n≡0 (repLNP e) h)))))
                    (≤0 {ls = labels s} (zW gBQ refl (ptLN tr)))

-- LeiosFetch client: owns the closure-entry reports; sends the commanded requests
lfCG : ∀ g l d → Rl (gc g) (gd g) 0 (LFPclientA l d)
lfCG gBT l d {s} tr =
  mkG gBT {labels s} (≤-trans (lfpClientA-es l d tr) (≤-≡ (sym (Σc-cong (AllL-map (λ z → proj₂ (proj₁ (proj₂ z))) cv)))))
          (≤0 {ls = labels s} (trans (Σc-cong (AllL-map (λ z → proj₁ (proj₁ (proj₂ z))) cv))
                 (Σc-0 _ (appL (AllL-map (λ z → proj₂ (proj₂ (proj₂ (proj₂ z)))) cv) (Σ0→ (labels s) (lfpClientA-noBT l d tr))))))
  where
    -- the conversions of its labels
    cv = cvs (ptLF tr)
lfCG gTQ l d {s} tr = mkG gTQ {labels s} (≤0 {ls = labels s} (zsub {ls = labels s} (lfpClientA-noRep l d tr) (λ {e} h → m+n≡0⇒n≡0 (rep gBQ e) (m+n≡0⇒n≡0 (repLNP e) h))))
                    (≤-trans (≤-≡ (Σc-cong (AllL-map (λ z → proj₁ (proj₁ z)) (cvs (ptLF tr))))) (two≤ {ls = labels s} (lfpClientA-tq l d tr) (lfpClientA-bm l d tr)))
lfCG gBQ l d {s} tr = mkG gBQ {labels s} (≤0 {ls = labels s} (zsub {ls = labels s} (lfpClientA-noRep l d tr) (λ {e} h → m+n≡0⇒m≡0 (rep gBQ e) (m+n≡0⇒n≡0 (repLNP e) h))))
                    (≤-trans (≤-≡ (Σc-cong (AllL-map (λ z → proj₁ (proj₁ (proj₂ (proj₂ z)))) (cvs (ptLF tr))))) (lfpClientA-bq l d tr))
lfCG gLN l d {s} tr = mkG gLN {labels s} (≤0 {ls = labels s} (zsub {ls = labels s} (lfpClientA-noRep l d tr) (λ {e} h → m+n≡0⇒m≡0 (repLNP e) h))) (≤0 {ls = labels s} (zW gLN refl (ptLF tr)))
lfCG gRF l d {s} tr = zF gRF refl (ptLF tr)
lfCG gTS l d {s} tr = zF gTS refl (ptLF tr)

-- LeiosFetch server: owns the request reports; sends the commanded closure entries
lfSG : ∀ g l d → Rl (gc g) (gd g) 0 (LFPserverA l d)
lfSG gTQ l d {s} tr =
  mkG gTQ {labels s} (≤-trans (two≤ {ls = labels s} (lfpServerA-tq l d tr) (lfpServerA-bm l d tr)) (≤-≡ (sym (Σc-cong (AllL-map (λ z → proj₂ (proj₁ z)) cv)))))
          (≤0 {ls = labels s} (trans (Σc-cong (AllL-map (λ z → proj₁ (proj₁ z)) cv))
                 (sum0 {ls = labels s} (Σ0→ (labels s) (lfpServerA-noTQ l d tr))
                       (appL (AllL-map (λ z → proj₁ (proj₂ (proj₂ (proj₂ z)))) cv) (Σ0→ (labels s) (lfpServerA-noTQ l d tr))))))
  where
    -- the conversions of its labels
    cv = cvs (ptLF tr)
lfSG gBQ l d {s} tr =
  mkG gBQ {labels s} (≤-trans (lfpServerA-bq l d tr) (≤-≡ (sym (Σc-cong (AllL-map (λ z → proj₂ (proj₁ (proj₂ (proj₂ z)))) cv)))))
          (≤0 {ls = labels s} (trans (Σc-cong (AllL-map (λ z → proj₁ (proj₁ (proj₂ (proj₂ z)))) cv)) (lfpServerA-noBQ l d tr)))
  where
    -- the conversions of its labels
    cv = cvs (ptLF tr)
lfSG gBT l d {s} tr = mkG gBT {labels s} (≤0 {ls = labels s} (zsub {ls = labels s} (lfpServerA-noRep l d tr) (λ {e} h → m+n≡0⇒n≡0 (repLNP e) h)))
                    (≤-trans (≤-≡ (Σc-cong (AllL-map (λ z → proj₁ (proj₁ (proj₂ z))) (cvs (ptLF tr))))) (lfpServerA-es l d tr))
lfSG gLN l d {s} tr = mkG gLN {labels s} (≤0 {ls = labels s} (zsub {ls = labels s} (lfpServerA-noRep l d tr) (λ {e} h → m+n≡0⇒m≡0 (repLNP e) h))) (≤0 {ls = labels s} (zW gLN refl (ptLF tr)))
lfSG gRF l d {s} tr = zF gRF refl (ptLF tr)
lfSG gTS l d {s} tr = zF gTS refl (ptLF tr)

-- every client instance, by protocol id
pcG : ∀ g l d id → Rl (gc g) (gd g) 0 (clientPeerP l d id)
pcG g l d N2N_KeepAlive    tr = zF g refl (ptKA tr)
pcG g l d N2N_ChainSync    tr = csCG g l d tr
pcG g l d N2N_BlockFetch   tr = zF g refl (ptBF tr)
pcG g l d N2N_TxSubmission tr = tsCG g l d tr
pcG g l d N2N_LeiosNotify  tr = lnCG g l d tr
pcG g l d N2N_LeiosFetch   tr = lfCG g l d tr

-- every server instance, by protocol id
psG : ∀ g l d id → Rl (gc g) (gd g) 0 (serverPeerP l d id)
psG g l d N2N_KeepAlive    tr = zF g refl (ptKA tr)
psG g l d N2N_ChainSync    tr = csSG g l d tr
psG g l d N2N_BlockFetch   tr = zF g refl (ptBF tr)
psG g l d N2N_TxSubmission tr = tsSG g l d tr
psG g l d N2N_LeiosNotify  tr = lnSG g l d tr
psG g l d N2N_LeiosFetch   tr = lfSG g l d tr

-- the base fact of every client instance
pcB : ∀ l d id → Rl (λ e → χ HK e + wI one e) (λ e → cApi e + (cApi e + (cApi e + wO one e))) 2 (clientPeerP l d id)
pcB l d N2N_KeepAlive    tr = baseF (kaClientA-P1 l d tr) (ptKA tr)
pcB l d N2N_ChainSync    tr = baseF (csClientA-P1 l d tr) (ptCS tr)
pcB l d N2N_BlockFetch   tr = baseF (bfClientA-P1 l d tr) (ptBF tr)
pcB l d N2N_TxSubmission tr = baseF (tsClientA-P1 l d tr) (ptTS tr)
pcB l d N2N_LeiosNotify  tr = baseF (lnpClientA-P1 l d tr) (ptLN tr)
pcB l d N2N_LeiosFetch   tr = baseF (lfpClientA-P1 l d tr) (ptLF tr)

-- the base fact of every server instance
psB : ∀ l d id → Rl (λ e → χ HK e + wI one e) (λ e → cApi e + (cApi e + (cApi e + wO one e))) 2 (serverPeerP l d id)
psB l d N2N_KeepAlive    tr = baseF (kaServerA-P1 l d tr) (ptKA tr)
psB l d N2N_ChainSync    tr = baseF (csServerA-P1 l d tr) (ptCS tr)
psB l d N2N_BlockFetch   tr = baseF (bfServerA-P1 l d tr) (ptBF tr)
psB l d N2N_TxSubmission tr = baseF (tsServerA-P1 l d tr) (ptTS tr)
psB l d N2N_LeiosNotify  tr = baseF (lnpServerA-P1 l d tr) (ptLN tr)
psB l d N2N_LeiosFetch   tr = baseF (lfpServerA-P1 l d tr) (ptLF tr)

------------------------------------------------------------------------
-- THE BUNDLE FACTS
------------------------------------------------------------------------

-- THE GROUP FACT: a node's bundle pays every group's reports and wire inputs
bundleG : ∀ g l cl sv → Rl (gc g) (gd g) 0 (nodeBundleP l cl sv)
bundleG g = bundle-Rl (pcG g) (psG g)

-- THE BASE FACT: a node's bundle pays its H-labels and wire inputs with api labels
bundleB : ∀ l cl sv → Rl (λ e → χ HK e + wI one e) (λ e → cApi e + (cApi e + (cApi e + wO one e))) 24
                         (nodeBundleP l cl sv)
bundleB = bundle-Rl pcB psB
