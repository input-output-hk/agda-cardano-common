{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Leios no-livelock, Stage C: the BlockFetch PEERS — premise (b) and P1.
-- The menu inversions are `ProvBF`'s views (client `IdleV`/`BusyV`/`StrV`,
-- server `SIdleV`/`SBusyV`/`SStrV`), not written again here.
------------------------------------------------------------------------

open import Cardano_network.Params using (Params)

module Cardano_network.Parametric.Leios.NoLivelock.PeerBF (p : Params) where

open import Data.Nat using (ℕ; _≤_; _+_)
open import Data.Unit.Polymorphic using (tt)
open import Relation.Binary.PropositionalEquality using (refl)

open import Process_Trees using (ExtI)
open import Cardano_network.Base
open import Cardano_network.Net p
open import Cardano_network.Data p
open import Cardano_network.BlockFetch p
open import Cardano_network.NetworkPar p using (ιBF; ιBF⁻¹; ιBF-linv; BFclientA; BFserverA)
open import CSP.Operators BFEv-≟ using (∅ES)
open import Semantics.LTS {E = BFEv} {I = ExtI BFEv} using (sVis)
import Semantics.LTS {E = BFEv} {I = ExtI BFEv} as B
import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} as L
open import Semantics.DivergenceFree {E = BFEv} {I = ExtI BFEv} using (τ-AccReach)
import Semantics.DivergenceFree {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} as DF
open import CSP.Laws.DivFree.ModAcc BFEv-≟ using (MAccR; MAccR→τ-AccReach)
open import CSP.Laws.DivFree.Reach BFEv-≟ using (MAccR-Ret)
open import CSP.Laws.DivFree.Loop BFEv-≟
  using (NoRetBy; Looping; NoRetBy-mono; NoRetBy-Ret; Guarded-react; MAccR-react; MAccR-Output; MAccR-⟶₀; MAccR-iter)
open import CSP.Laws.DivFree.ReachRename {E₁ = BFEv} {E₂ = Net_Api Payload} ιBF ιBF⁻¹ ιBF-linv using (τ-AccReach-renameMap)
open import Semantics.Failures {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using (_⟹⟨_⟩_)
open import CSP.Laws.DivFree.Count (Net_Api-≟ {Payload}) using (Σc; labels)
open import CSP.Laws.DivFree.CountMore BFEv-≟ using (RoundPot; StepPot; rp-pch; rp-done; sp-Ret; sp-Out; sp-⟶; potIter)
open import Cardano_network.Parametric.Leios.NoLivelock.Weights p using (cIn; cApi)
open import Cardano_network.Parametric.Leios.NoLivelock.ProvBF p
  using (IdleV; iRange; iDone; idleV; BusyV; bStart; bNone; busyV; StrV; sBlock; sDone; strV;
         SIdleV; siRange; siDone; sIdleV; SBusyV; sbStart; sbNone; sBusyV; SStrV; ssBlock; ssDone; sStrV; ιBF-rinv)
open import CSP.Laws.DivFree.CountRename ιBF ιBF⁻¹ ιBF-linv ιBF-rinv BFEv-≟ (Net_Api-≟ {Payload}) using (renE; Σc≤-ren)

-- a `Net_Api` weight pulled back to `BFEv`
_ʳ : (L.Event → ℕ) → B.Event → ℕ
(c ʳ) e = c (renE e)

------------------------------------------------------------------------
-- premise (b), read off `ProvBF`'s views
------------------------------------------------------------------------

-- what each client view leaves behind is accessible (Idle)
idleR : ∀ {l d x t′} → IdleV l d x t′ → MAccR ∅ES t′
idleR (iRange _) = MAccR-Output _ _ (MAccR-Ret _)
idleR (iDone _)  = MAccR-Output _ _ (MAccR-Ret _)

-- (Busy)
busyR : ∀ {l d x t′} → BusyV l d x t′ → MAccR ∅ES t′
busyR bStart = MAccR-Ret _
busyR bNone  = MAccR-Ret _

-- (Streaming)
strR : ∀ {l d x t′} → StrV l d x t′ → MAccR ∅ES t′
strR (sBlock _) = MAccR-Output _ _ (MAccR-Ret _)
strR sDone      = MAccR-Ret _

-- what each server view leaves behind is accessible (Idle)
sIdleR : ∀ {l d x t′} → SIdleV l d x t′ → MAccR ∅ES t′
sIdleR (siRange _) = MAccR-Output _ _ (MAccR-Ret _)
sIdleR siDone      = MAccR-⟶₀ _ (MAccR-Ret _)

-- (Busy)
sBusyR : ∀ {l d x t′} → SBusyV l d x t′ → MAccR ∅ES t′
sBusyR (sbStart _) = MAccR-Output _ _ (MAccR-Ret _)
sBusyR (sbNone _)  = MAccR-Output _ _ (MAccR-Ret _)

-- (Streaming)
sStrR : ∀ {l d x t′} → SStrV l d x t′ → MAccR ∅ES t′
sStrR (ssBlock _) = MAccR-Output _ _ (MAccR-Ret _)
sStrR (ssDone _)  = MAccR-Output _ _ (MAccR-Ret _)

-- every client body state is accessible at every reachable state
cbodyR : ∀ {l d} st → MAccR ∅ES (clientStep l d st)
cbodyR {l} {d} stIdle      = MAccR-react refl λ {at} {a} eq → idleR (idleV {l} {d} (sVis {at = at} {a = a} refl eq))
cbodyR {l} {d} stBusy      = MAccR-react refl λ {at} {a} eq → busyR (busyV {l} {d} (sVis {at = at} {a = a} refl eq))
cbodyR {l} {d} stStreaming = MAccR-react refl λ {at} {a} eq → strR (strV {l} {d} (sVis {at = at} {a = a} refl eq))
cbodyR stDone              = MAccR-Ret _

-- every server body state is accessible at every reachable state
sbodyR : ∀ {l d} st → MAccR ∅ES (serverStep l d st)
sbodyR {l} {d} stIdle      = MAccR-react refl λ {at} {a} eq → sIdleR (sIdleV {l} {d} (sVis {at = at} {a = a} refl eq))
sbodyR {l} {d} stBusy      = MAccR-react refl λ {at} {a} eq → sBusyR (sBusyV {l} {d} (sVis {at = at} {a = a} refl eq))
sbodyR {l} {d} stStreaming = MAccR-react refl λ {at} {a} eq → sStrR (sStrV {l} {d} (sVis {at = at} {a = a} refl eq))
sbodyR stDone              = MAccR-Ret _

-- every client round starts with a visible event (`stDone` returns `inj₂`)
cbodyG : ∀ {l d} st → NoRetBy Looping ∅ES (clientStep l d st)
cbodyG stIdle      = NoRetBy-mono (λ _ _ → tt) (Guarded-react refl λ ())
cbodyG stBusy      = NoRetBy-mono (λ _ _ → tt) (Guarded-react refl λ ())
cbodyG stStreaming = NoRetBy-mono (λ _ _ → tt) (Guarded-react refl λ ())
cbodyG stDone      = NoRetBy-Ret λ ()

-- every server round starts with a visible event
sbodyG : ∀ {l d} st → NoRetBy Looping ∅ES (serverStep l d st)
sbodyG stIdle      = NoRetBy-mono (λ _ _ → tt) (Guarded-react refl λ ())
sbodyG stBusy      = NoRetBy-mono (λ _ _ → tt) (Guarded-react refl λ ())
sbodyG stStreaming = NoRetBy-mono (λ _ _ → tt) (Guarded-react refl λ ())
sbodyG stDone      = NoRetBy-Ret λ ()

-- THE CLIENT LEAF (renamed onto `Net_Api`)
bfClientA-τ : ∀ l d → DF.τ-AccReach (BFclientA l d)
bfClientA-τ l d = τ-AccReach-renameMap (MAccR→τ-AccReach (MAccR-iter {k = clientStep l d} cbodyG cbodyR stIdle))

-- THE SERVER LEAF (renamed onto `Net_Api`)
bfServerA-τ : ∀ l d → DF.τ-AccReach (BFserverA l d)
bfServerA-τ l d = τ-AccReach-renameMap (MAccR→τ-AccReach (MAccR-iter {k = serverStep l d} sbodyG sbodyR stIdle))

------------------------------------------------------------------------
-- P1 (wire inputs ≤ api labels + 1), per view
------------------------------------------------------------------------

-- the zero potential
Φ0 : BFState → ℕ
Φ0 _ = 0

-- P1 obligations
P1 : BFState → B.Event → _ → Set₁
P1 = StepPot {Rx = Rr} {Φ = Φ0} {cIn ʳ} {cApi ʳ} {1}

-- client Idle
p1-idle : ∀ {l d x t′} → IdleV l d x t′ → P1 stIdle x t′
p1-idle (iRange _) = sp-Out
p1-idle (iDone _)  = sp-Out

-- client Busy
p1-busy : ∀ {l d x t′} → BusyV l d x t′ → P1 stBusy x t′
p1-busy bStart = sp-Ret
p1-busy bNone  = sp-Ret

-- client Streaming
p1-str : ∀ {l d x t′} → StrV l d x t′ → P1 stStreaming x t′
p1-str (sBlock _) = sp-Out
p1-str sDone      = sp-Ret

-- server Idle
p1-sIdle : ∀ {l d x t′} → SIdleV l d x t′ → P1 stIdle x t′
p1-sIdle (siRange _) = sp-Out
p1-sIdle siDone      = sp-⟶

-- server Busy
p1-sBusy : ∀ {l d x t′} → SBusyV l d x t′ → P1 stBusy x t′
p1-sBusy (sbStart _) = sp-Out
p1-sBusy (sbNone _)  = sp-Out

-- server Streaming
p1-sStr : ∀ {l d x t′} → SStrV l d x t′ → P1 stStreaming x t′
p1-sStr (ssBlock _) = sp-Out
p1-sStr (ssDone _)  = sp-Out

-- the client's P1 rounds
p1-c : ∀ {l d} st → RoundPot {Rx = Rr} {Φ = Φ0} {cIn ʳ} {cApi ʳ} {1} st (clientStep l d st)
p1-c stIdle      = rp-pch λ st → p1-idle (idleV st)
p1-c stBusy      = rp-pch λ st → p1-busy (busyV st)
p1-c stStreaming = rp-pch λ st → p1-str (strV st)
p1-c stDone      = rp-done

-- the server's P1 rounds
p1-s : ∀ {l d} st → RoundPot {Rx = Rr} {Φ = Φ0} {cIn ʳ} {cApi ʳ} {1} st (serverStep l d st)
p1-s stIdle      = rp-pch λ st → p1-sIdle (sIdleV st)
p1-s stBusy      = rp-pch λ st → p1-sBusy (sBusyV st)
p1-s stStreaming = rp-pch λ st → p1-sStr (sStrV st)
p1-s stDone      = rp-done

-- P1 (BlockFetch client)
bfClientA-P1 : ∀ l d {s W} → BFclientA l d ⟹⟨ s ⟩ W → Σc cIn (labels s) ≤ Σc cApi (labels s) + 1
bfClientA-P1 l d = Σc≤-ren cIn cApi 1 (potIter Φ0 (cIn ʳ) (cApi ʳ) 1 (p1-c {l} {d}) stIdle)

-- P1 (BlockFetch server)
bfServerA-P1 : ∀ l d {s W} → BFserverA l d ⟹⟨ s ⟩ W → Σc cIn (labels s) ≤ Σc cApi (labels s) + 1
bfServerA-P1 l d = Σc≤-ren cIn cApi 1 (potIter Φ0 (cIn ʳ) (cApi ʳ) 1 (p1-s {l} {d}) stIdle)
