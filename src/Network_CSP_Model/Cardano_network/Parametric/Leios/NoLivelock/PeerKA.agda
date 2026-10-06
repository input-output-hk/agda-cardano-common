{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Leios no-livelock, Stage C: the KeepAlive PEERS.
--   * VIEWS of the client's two menu states and the server's receive menu
--   * premise (b): `kaClientA-τ` (from the views), `kaServerA-τ` (the
--     smoke-tested `PeerTauAccSmoke.server-τ-AccReach`, renamed)
--   * P1 for both sides on the peer's own renamed trace (the server's
--     response is owed across a round: potential 1 in `stServer`)
--   * provenance: chain-free by renaming alone (`kaA-PA`)
-- KeepAlive is inert in `rawSys2` (no thread offers `apiKA`); the summaries
-- hold for every trace of the peer alone.
------------------------------------------------------------------------

open import Cardano_network.Params using (Params)

module Cardano_network.Parametric.Leios.NoLivelock.PeerKA (p : Params) where

open import Data.Empty using (⊥)
open import Data.Maybe using (just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; _≤_; _+_)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Class.DecEq using (_≟_)

open import Process_Trees using (ExtI; PTree)
open import Cardano_network.Base
open import Cardano_network.Net p
open import Cardano_network.KeepAlive p
open Params p using (time₀; length₀; Time; Length; Cookie; decCookie)
open import Cardano_network.NetworkPar p using (ιKA; ιKA⁻¹; ιKA-linv; KAclientA; KAserverA)
import CSP.Rename {E₁ = KAEv} {E₂ = Net_Api Payload} ιKA ιKA⁻¹ ιKA-linv as RenKA
open import CSP.Operators KAEv-≟ using (∅ES; Ret; Output; Prefix; Prefix₀)
open import Semantics.LTS {E = KAEv} {I = ExtI KAEv} using (_─[_]─►_; ev; evl; sVis)
import Semantics.LTS {E = KAEv} {I = ExtI KAEv} as K
import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} as L
open import Semantics.DivergenceFree {E = KAEv} {I = ExtI KAEv} using (τ-AccReach)
import Semantics.DivergenceFree {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} as DF
open import CSP.Laws.DivFree.ModAcc KAEv-≟ using (MAccR; MAccR→τ-AccReach)
open import CSP.Laws.DivFree.Reach KAEv-≟ using (MAccR-Ret)
open import CSP.Laws.DivFree.Loop KAEv-≟
  using (NoRetBy; Looping; NoRetBy-mono; NoRetBy-Ret; Guarded-react; MAccR-react; MAccR-Output; MAccR-iter)
open import CSP.Laws.DivFree.ReachRename {E₁ = KAEv} {E₂ = Net_Api Payload} ιKA ιKA⁻¹ ιKA-linv using (τ-AccReach-renameMap)
open import Cardano_network.NetworkVerification.PeerTauAccSmoke p using (server-τ-AccReach)
open import Semantics.Failures {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using (_⟹⟨_⟩_)
import CSP.Laws.DivFree.Count KAEv-≟ as S
open import CSP.Laws.DivFree.Count (Net_Api-≟ {Payload}) using (Σc; labels)
open import CSP.Laws.DivFree.CountMore KAEv-≟ using (RoundPot; StepPot; rp-pch; rp-done; rp-Out; sp-Ret; sp-Out; sp-⟶; potIter)
open import CSP.Laws.DivFree.Prov KAEv-≟ using (pa)
open import CSP.Laws.DivFree.ProvMore KAEv-≟ using (Prov-free)
import CSP.Laws.DivFree.Prov (Net_Api-≟ {Payload}) as PL
open import Cardano_network.Parametric.Leios.NoLivelock.Weights p using (cIn; cApi)
open import Cardano_network.Parametric.Leios.NoLivelock.ProvBF p using (ChS; InP)

------------------------------------------------------------------------
-- the renaming pulls back exactly its images (`CountRename`'s `ι-rinv`)
------------------------------------------------------------------------

-- ιKA⁻¹ pulls back only ιKA-images
ιKA-rinv : ∀ {A} {e₂ : Net_Api Payload A} {e : KAEv A} → ιKA⁻¹ e₂ ≡ just e → e₂ ≡ ιKA e
ιKA-rinv {e₂ = input  _ _ N2N_KeepAlive} refl = refl
ιKA-rinv {e₂ = output _ _ N2N_KeepAlive} refl = refl
ιKA-rinv {e₂ = apiKA  _ _ _}             refl = refl
ιKA-rinv {e₂ = done   _ _ N2N_KeepAlive} refl = refl
ιKA-rinv {e₂ = input  _ _ N2N_ChainSync} ()
ιKA-rinv {e₂ = input  _ _ N2N_BlockFetch} ()
ιKA-rinv {e₂ = input  _ _ N2N_TxSubmission} ()
ιKA-rinv {e₂ = input  _ _ N2N_LeiosNotify} ()
ιKA-rinv {e₂ = input  _ _ N2N_LeiosFetch} ()
ιKA-rinv {e₂ = output _ _ N2N_ChainSync} ()
ιKA-rinv {e₂ = output _ _ N2N_BlockFetch} ()
ιKA-rinv {e₂ = output _ _ N2N_TxSubmission} ()
ιKA-rinv {e₂ = output _ _ N2N_LeiosNotify} ()
ιKA-rinv {e₂ = output _ _ N2N_LeiosFetch} ()
ιKA-rinv {e₂ = done   _ _ N2N_ChainSync} ()
ιKA-rinv {e₂ = done   _ _ N2N_BlockFetch} ()
ιKA-rinv {e₂ = done   _ _ N2N_TxSubmission} ()
ιKA-rinv {e₂ = done   _ _ N2N_LeiosNotify} ()
ιKA-rinv {e₂ = done   _ _ N2N_LeiosFetch} ()
ιKA-rinv {e₂ = sndmsg _ _ _} ()
ιKA-rinv {e₂ = rcvmsg _ _ _} ()
ιKA-rinv {e₂ = tx     _ _ _} ()
ιKA-rinv {e₂ = sndack _ _ _} ()
ιKA-rinv {e₂ = rcvack _ _ _} ()
ιKA-rinv {e₂ = ack    _ _ _} ()
ιKA-rinv {e₂ = apiCS  _ _ _} ()
ιKA-rinv {e₂ = apiBF  _ _ _} ()
ιKA-rinv {e₂ = apiTS  _ _ _} ()
ιKA-rinv {e₂ = apiLN  _ _ _} ()
ιKA-rinv {e₂ = apiLF  _ _ _} ()
ιKA-rinv {e₂ = apiLP  _ _ _} ()
ιKA-rinv {e₂ = store  _ _ _} ()
ιKA-rinv {e₂ = env    _ _ _} ()
ιKA-rinv {e₂ = break  _} ()

open import CSP.Laws.DivFree.CountRename ιKA ιKA⁻¹ ιKA-linv ιKA-rinv KAEv-≟ (Net_Api-≟ {Payload})
  using (renE; Σc≤-ren; PA-ren)

-- a `Net_Api` weight pulled back to `KAEv`
_ʳ : (L.Event → ℕ) → K.Event → ℕ
(c ʳ) e = c (renE e)

-- a KeepAlive round tree
Rd : Set₁
Rd = PTree KAEv (ExtI KAEv) (KAState ⊎ Rr)

------------------------------------------------------------------------
-- views
------------------------------------------------------------------------

-- the client's request `msg`, then on to `st`
kSend : Link → Dir → MessageKeepAlive → KAState → Rd
kSend l d msg st = sendKA l d ! (time₀ , FromInitiator , length₀ , keepAlive msg) ⟶ Ret (inj₁ st)

-- client stClient: the api menu (a keepalive with its cookie / done), each a single send
data KCliV (l : Link) (d : Dir) : K.Event → Rd → Set₁ where
  kcMsg  : ∀ c → KCliV l d (K.evLabel _ (apiKAev l d sendKAMsg) c) (kSend l d (MsgKeepAlive c) (stServer c))
  kcDone : ∀ u → KCliV l d (K.evLabel _ (apiKAev l d sendKADone) u) (kSend l d MsgKADone stDone)

-- the client stClient inversion
kCliV : ∀ {l d x t′} → clientStep l d stClient ─[ ev (evl x) ]─► t′ → KCliV l d x t′
kCliV {l} {d} (sVis {at = _ , apiKAev l′ d′ sendKAMsg} {a = c} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (KCliV l d _) (just-injective br) (kcMsg c)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
kCliV {l} {d} (sVis {at = _ , apiKAev l′ d′ sendKADone} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (KCliV l d _) (just-injective br) (kcDone _)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
kCliV (sVis {at = _ , apiKAev _ _ errCookie}    refl ())
kCliV (sVis {at = _ , apiKAev _ _ recvKACookie} refl ())
kCliV (sVis {at = _ , sendKA _ _}    refl ())
kCliV (sVis {at = _ , receiveKA _ _} refl ())
kCliV (sVis {at = _ , doneKA _ _}    refl ())

-- a received KeepAlive message on the peer's own cell
rcvK : Link → Dir → Time → Mode → Length → MessageKeepAlive → K.Event
rcvK l d tm md ln msg = K.evLabel _ (receiveKA l d) (tm , md , ln , keepAlive msg)

-- client stServer c: the response (cookie match: back to stClient; mismatch: report and stop)
data KSrvV (l : Link) (d : Dir) (c : Cookie) : K.Event → Rd → Set₁ where
  ksOk  : ∀ {tm md ln}    → KSrvV l d c (rcvK l d tm md ln (MsgKeepAliveResponse c)) (Ret (inj₁ stClient))
  ksBad : ∀ {tm md ln} c′ → KSrvV l d c (rcvK l d tm md ln (MsgKeepAliveResponse c′))
                                        (apiKAev l d errCookie ! (c , c′) ⟶ Ret (inj₂ tt))

-- the client stServer inversion
kSrvV : ∀ {l d c x t′} → clientStep l d (stServer c) ─[ ev (evl x) ]─► t′ → KSrvV l d c x t′
kSrvV {l} {d} {c} (sVis {at = _ , receiveKA l′ d′} {a = _ , _ , _ , keepAlive (MsgKeepAliveResponse c′)} refl br)
  with l′ ≟ l | d′ ≟ d
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
... | yes refl | yes refl with c ≟ c′
...   | yes refl = subst (KSrvV l d c _) (just-injective br) ksOk
...   | no _     = subst (KSrvV l d c _) (just-injective br) (ksBad c′)
kSrvV (sVis {at = _ , receiveKA _ _} {a = _ , _ , _ , keepAlive (MsgKeepAlive _)} refl ())
kSrvV (sVis {at = _ , receiveKA _ _} {a = _ , _ , _ , keepAlive MsgKADone}        refl ())
kSrvV (sVis {at = _ , receiveKA _ _} {a = _ , _ , _ , blockFetch _}   refl ())
kSrvV (sVis {at = _ , receiveKA _ _} {a = _ , _ , _ , chainSync _}    refl ())
kSrvV (sVis {at = _ , receiveKA _ _} {a = _ , _ , _ , txSubmission _} refl ())
kSrvV (sVis {at = _ , receiveKA _ _} {a = _ , _ , _ , leiosNotify _}  refl ())
kSrvV (sVis {at = _ , receiveKA _ _} {a = _ , _ , _ , leiosFetch _}   refl ())
kSrvV (sVis {at = _ , receiveKA _ _} {a = _ , _ , _ , leiosNotifyP _} refl ())
kSrvV (sVis {at = _ , receiveKA _ _} {a = _ , _ , _ , leiosFetchP _}  refl ())
kSrvV (sVis {at = _ , sendKA _ _}    refl ())
kSrvV (sVis {at = _ , apiKAev _ _ _} refl ())
kSrvV (sVis {at = _ , doneKA _ _}    refl ())

-- server stClient: the receive menu (a keepalive: report its cookie; done)
data KReqV (l : Link) (d : Dir) : K.Event → Rd → Set₁ where
  krMsg  : ∀ {tm md ln} c → KReqV l d (rcvK l d tm md ln (MsgKeepAlive c))
                                      (apiKAev l d recvKACookie ! c ⟶ Ret (inj₁ (stServer c)))
  krDone : ∀ {tm md ln}   → KReqV l d (rcvK l d tm md ln MsgKADone) (doneKA l d ⟶₀ Ret (inj₁ stDone))

-- the server stClient inversion
kReqV : ∀ {l d x t′} → serverStep l d stClient ─[ ev (evl x) ]─► t′ → KReqV l d x t′
kReqV {l} {d} (sVis {at = _ , receiveKA l′ d′} {a = _ , _ , _ , keepAlive (MsgKeepAlive c)} refl br)
  with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (KReqV l d _) (just-injective br) (krMsg c)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
kReqV {l} {d} (sVis {at = _ , receiveKA l′ d′} {a = _ , _ , _ , keepAlive MsgKADone} refl br)
  with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (KReqV l d _) (just-injective br) krDone
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
kReqV (sVis {at = _ , receiveKA _ _} {a = _ , _ , _ , keepAlive (MsgKeepAliveResponse _)} refl ())
kReqV (sVis {at = _ , receiveKA _ _} {a = _ , _ , _ , blockFetch _}   refl ())
kReqV (sVis {at = _ , receiveKA _ _} {a = _ , _ , _ , chainSync _}    refl ())
kReqV (sVis {at = _ , receiveKA _ _} {a = _ , _ , _ , txSubmission _} refl ())
kReqV (sVis {at = _ , receiveKA _ _} {a = _ , _ , _ , leiosNotify _}  refl ())
kReqV (sVis {at = _ , receiveKA _ _} {a = _ , _ , _ , leiosFetch _}   refl ())
kReqV (sVis {at = _ , receiveKA _ _} {a = _ , _ , _ , leiosNotifyP _} refl ())
kReqV (sVis {at = _ , receiveKA _ _} {a = _ , _ , _ , leiosFetchP _}  refl ())
kReqV (sVis {at = _ , sendKA _ _}    refl ())
kReqV (sVis {at = _ , apiKAev _ _ _} refl ())
kReqV (sVis {at = _ , doneKA _ _}    refl ())

------------------------------------------------------------------------
-- premise (b)
------------------------------------------------------------------------

-- what each client stClient view leaves behind is accessible
kCliR : ∀ {l d x t′} → KCliV l d x t′ → MAccR ∅ES t′
kCliR (kcMsg _)  = MAccR-Output _ _ (MAccR-Ret _)
kCliR (kcDone _) = MAccR-Output _ _ (MAccR-Ret _)

-- (stServer)
kSrvR : ∀ {l d c x t′} → KSrvV l d c x t′ → MAccR ∅ES t′
kSrvR ksOk      = MAccR-Ret _
kSrvR (ksBad _) = MAccR-Output _ _ (MAccR-Ret _)

-- every client body state is accessible at every reachable state
cbodyR : ∀ {l d} st → MAccR ∅ES (clientStep l d st)
cbodyR {l} {d} stClient     = MAccR-react refl λ {at} {a} eq → kCliR (kCliV {l} {d} (sVis {at = at} {a = a} refl eq))
cbodyR {l} {d} (stServer c) = MAccR-react refl λ {at} {a} eq → kSrvR (kSrvV {l} {d} {c} (sVis {at = at} {a = a} refl eq))
cbodyR stDone               = MAccR-Ret _

-- every client round starts with a visible event
cbodyG : ∀ {l d} st → NoRetBy Looping ∅ES (clientStep l d st)
cbodyG stClient     = NoRetBy-mono (λ _ _ → tt) (Guarded-react refl λ ())
cbodyG (stServer _) = NoRetBy-mono (λ _ _ → tt) (Guarded-react refl λ ())
cbodyG stDone       = NoRetBy-Ret λ ()

-- THE CLIENT LEAF, at the source alphabet …
kaClient-τ : ∀ l d → τ-AccReach (KAclientStClient l d)
kaClient-τ l d = MAccR→τ-AccReach (MAccR-iter {k = clientStep l d} cbodyG cbodyR stClient)

-- … and renamed onto `Net_Api`
kaClientA-τ : ∀ l d → DF.τ-AccReach (KAclientA l d)
kaClientA-τ l d = τ-AccReach-renameMap (kaClient-τ l d)

-- THE SERVER LEAF (the smoke-tested source leaf, renamed)
kaServerA-τ : ∀ l d → DF.τ-AccReach (KAserverA l d)
kaServerA-τ l d = τ-AccReach-renameMap (server-τ-AccReach l d)

------------------------------------------------------------------------
-- P1 (wire inputs ≤ api labels + 1)
------------------------------------------------------------------------

-- the client's potential (none)
Φc : KAState → ℕ
Φc _ = 0

-- the server's potential: a keepalive received, its response still owed
Φs : KAState → ℕ
Φs (stServer _) = 1
Φs _            = 0

-- the client's P1, per view (stClient)
p1-kCli : ∀ {l d x t′} → KCliV l d x t′ → StepPot {Rx = Rr} {Φ = Φc} {cIn ʳ} {cApi ʳ} {1} stClient x t′
p1-kCli (kcMsg _)  = sp-Out
p1-kCli (kcDone _) = sp-Out

-- (stServer)
p1-kSrv : ∀ {l d c x t′} → KSrvV l d c x t′ → StepPot {Rx = Rr} {Φ = Φc} {cIn ʳ} {cApi ʳ} {1} (stServer c) x t′
p1-kSrv ksOk      = sp-Ret
p1-kSrv (ksBad _) = sp-Out

-- the client's P1 rounds
p1-c : ∀ {l d} st → RoundPot {Rx = Rr} {Φ = Φc} {cIn ʳ} {cApi ʳ} {1} st (clientStep l d st)
p1-c stClient     = rp-pch λ st → p1-kCli (kCliV st)
p1-c (stServer _) = rp-pch λ st → p1-kSrv (kSrvV st)
p1-c stDone       = rp-done

-- the server's P1, per view (stClient)
p1-kReq : ∀ {l d x t′} → KReqV l d x t′ → StepPot {Rx = Rr} {Φ = Φs} {cIn ʳ} {cApi ʳ} {1} stClient x t′
p1-kReq (krMsg _) = sp-Out
p1-kReq krDone    = sp-⟶

-- the server's P1 rounds (stServer is a single response)
p1-s : ∀ {l d} st → RoundPot {Rx = Rr} {Φ = Φs} {cIn ʳ} {cApi ʳ} {1} st (serverStep l d st)
p1-s stClient     = rp-pch λ st → p1-kReq (kReqV st)
p1-s (stServer _) = rp-Out
p1-s stDone       = rp-done

-- P1 (KeepAlive client)
kaClientA-P1 : ∀ l d {s W} → KAclientA l d ⟹⟨ s ⟩ W → Σc cIn (labels s) ≤ Σc cApi (labels s) + 1
kaClientA-P1 l d = Σc≤-ren cIn cApi 1 (potIter Φc (cIn ʳ) (cApi ʳ) 1 (p1-c {l} {d}) stClient)

-- P1 (KeepAlive server)
kaServerA-P1 : ∀ l d {s W} → KAserverA l d ⟹⟨ s ⟩ W → Σc cIn (labels s) ≤ Σc cApi (labels s) + 1
kaServerA-P1 l d = Σc≤-ren cIn cApi 1 (potIter Φs (cIn ʳ) (cApi ʳ) 1 (p1-s {l} {d}) stClient)

------------------------------------------------------------------------
-- provenance (D1-b): KeepAlive never touches the block chain — by its
-- renaming alone (`ChS` has no clause for a KeepAlive cell, `apiKA`, `done`)
------------------------------------------------------------------------

-- no KeepAlive label is a chain label
noChain : ∀ {e : K.Event} {y} → ChS (renE e) y → ⊥
noChain {K.evLabel _ (sendKA _ _) _}    ()
noChain {K.evLabel _ (receiveKA _ _) _} ()
noChain {K.evLabel _ (apiKAev _ _ _) _} ()
noChain {K.evLabel _ (doneKA _ _) _}    ()

-- every renamed KeepAlive process is chain-free
kaA-PA : ∀ {ℓr} {R : Set ℓr} {P : PTree KAEv (ExtI KAEv) R} → PL.PA ChS ChS InP (RenKA.renameMap P)
kaA-PA = PA-ren (pa λ {_} {s} _ → Prov-free noChain (S.labels s))

-- (the client)
kaClientA-PA : ∀ l d → PL.PA ChS ChS InP (KAclientA l d)
kaClientA-PA l d = kaA-PA

-- (the server)
kaServerA-PA : ∀ l d → PL.PA ChS ChS InP (KAserverA l d)
kaServerA-PA l d = kaA-PA
