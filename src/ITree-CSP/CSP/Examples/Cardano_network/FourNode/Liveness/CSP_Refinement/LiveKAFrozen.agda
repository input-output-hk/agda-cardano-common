{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — THE FROZEN KA CLIENT (`Praos.LiveKAFrozen`), the peer
-- (P5) `noRetA` is refuted by, and the ONE bundle inversion that reports its
-- freeze (owner grant #6's consumer side).
--
-- WHY THIS MODULE EXISTS.  `LiveRetFree` shows that ONE permanently non-`Fin`
-- peer refutes a `ret` of the whole abstract decode, and names the peer: node B's
-- link-AB KA CLIENT at its loop head.  Carrying that as an invariant means every
-- step class must preserve it, and TWO classes can touch an `InertPos` — the io
-- class (`LiveLegIoCone`) and, through the `done` labels, the api class
-- (`LiveLegApiCone`).  Both need the same two things, so both take them from
-- here:
--   · `KAcAtHead` — the freeze itself, on an `InertPos`;
--   · `kaFire`    — the KA-channel bundle inversion WITH the freeze fact.
--
-- WHY `kaFire` AND NOT `SIL6.absBundleKA-ev-prod`.  The frozen client's fire can
-- only be refuted FROM ITS OWN STEP (its table is what has no row for a wire or
-- `done` label), and SIL6's inversion reports WHICH KA peer moved (`bkacEB` /
-- `bkasEB`) but DROPS that peer's step.  A second, independent peel would not
-- correlate with the first — the two `with`s split independently and neither
-- `Par` nor any decode is injective (session-30's measured negative) — so the
-- successor and the fact have to come out of ONE inversion.  `kaFire` is SIL6's
-- own KA material transcribed with the fact riding beside the successor it builds.
--
-- *** KEEP IN SYNC WITH `R2_Bisim/SysIoLink6:644-760`, PART BY PART. ***  All four
-- anchors below were re-derived by grep; the span deliberately stops at `:760`,
-- because `:762-764` is the unrelated "PART 2d — abstract TS bundle inversion"
-- banner.
--
--   · `:644-656`  `data BundleKAEvR-abs` — RESTRUCTURED here as `KAFire`;
--   · `:658-697`  `finishKAc-ev-abs` / `finishKAs-ev-abs` — their BODIES are
--                 transcribed into `kaFire`'s two firing arms;
--   · `:699-714`  `absBundleKA-ev-prod`'s first TWO rungs (client, server) and
--                 their `evSync`/`evBoth` arms — transcribed, including the
--                 eleven-peer tail refutation at `:709`;
--   · `:715-760`  SIL6's ten-peer RUNG-BY-RUNG continuation — deliberately NOT
--                 transcribed.  It is COLLAPSED into `kaTail-abs-noKA` below,
--                 which is `:714`'s single `⦀-noOffer` chain hoisted verbatim and
--                 used for BOTH of the split's non-KA arms.
--
-- TWO DELIBERATE DEVIATIONS, beyond the trailing fact — record them here because
-- "transcription" would otherwise invite reuse of `kaFire` in SIL6's place:
--   (1) the PREMISE IS STRENGTHENED.  `kaFire` demands `IsKAoff e₁`, where
--       `absBundleKA-ev-prod` (`:700-704`) accepts any `e₁ : KA.KAEv X`.  So
--       `kaFire` is NOT a drop-in replacement — it does not cover `apiKAev`, and
--       it must not: at `kcClient` the client's table really does have the two
--       `apiKA` rows, so the freeze refutation `kcFrz-no-io` would be FALSE there.
--       The premise is exactly what reaches that refutation.
--   (2) the CONCLUSION IS WEAKENED.  SIL6's two constructors pin the moved peer
--       (`:648` `record ip { kac = kac′ }`, `:653` `record ip { kas = kas′ }`);
--       `KAFire`'s single `kaFireF` binds an UNCONSTRAINED `ip′`, so it no longer
--       reports WHICH peer moved.  Nothing here needs that — the trailing fact is
--       what the callers consume — and collapsing the two constructors is what
--       lets the KA-client arm answer by refutation and the server arm by
--       identity.
-- Both deviations are in the safe direction (less general input, less informative
-- output); a re-sync must preserve them, not "restore" SIL6's shapes.
--
-- A THIRD, SMALLER SYNC SURFACE (M2): `kcHead-no-io` hand-builds the KA-client
-- table as `record { isFin = NS.kaCfin ; nxt = NS.kaCnxt l cl }`, which is exactly
-- `SysIoLink5:3725-3726`'s `Tkac l d`, and passes `NS.kcClient` where SIL6 passes
-- `coarsenKAc kacp` (justified by `SysStep:612`, `:618`, `:643-644`:
-- `coarsenKAc (kcHead stClient) = kcClient` and `absKAc l d q = tableSpec (Tkac l
-- d) (coarsenKAc q)`).  *** KEEP IN SYNC with `Tkac` and `absKAc` too: if either
-- changes shape, these three `with` lines rot silently. ***
--
-- No postulate, hole, meta, `NON_TERMINATING` or `mutual`.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveKAFrozen
  (blkA : Block₃) where

open import Level using ( 0ℓ )
open import Data.Unit.Polymorphic using ( ⊤; tt )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Product using ( _,_ )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; _≢_; refl; sym; trans; cong; subst )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; Net_Api-≟; Link )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.Base using ( Dir )
import CSP.Examples.Cardano_network.KeepAlive p as KA

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _⦀_ )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; evl; evLabel )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _═[_]═►_ )
import CSP.Laws.Traces.TraceLawsParallelElim (Net_Api-≟ {Payload}) as PEA
open import CSP.Examples.Cardano_network.NetworkPar p using ( ιKA )

import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA as SStep
open SStep using ( NetProc; absBundleG; absKAc; absKAs; absCSc; absCSs; absBFc; absBFs
                 ; absTSc; absTSs; absLNc; absLNs; absLFc; absLFs
                 ; coarsenKAc; ⦀-noOffer )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN
open SN using ( BFcPos; BFsPos )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; nB; initial )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.NodeSpecs blkA as NS
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_NodeTauEv blkA
  using ( tableSpec-ev-inv; nothing-absurd )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink6 blkA as SIL6
open SIL6 using ( ⦀-wev-L; ⦀-wev-R; absKAc-ev-dir; absKAs-ev-dir )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink5 blkA
  using ( decKAc-ev-prod-abs; decKAs-ev-prod-abs )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_RouteLnLf blkA
  using ( noOffer→viewV
        ; kaTail-kas-noOffer; kaTail-csc-noOffer; decKAc-dir-noOffer
        ; absCSc-noKA; absCSs-noKA; absBFc-noKA; absBFs-noKA
        ; absTSc-noKA; absTSs-noKA; absLNc-noKA; absLNs-noKA; absLFc-noKA; absLFs-noKA
        ; absKAs-dir-noBoth )

-- the frozen KA-client position: the campaign's one permanently non-terminal peer
KAcAtHead : SN.InertPos → Set
KAcAtHead ip = SN.kac ip ≡ SN.kcHead KA.stClient

-- THE THREE KA labels the FROZEN client has no table row for: the two wire ones
-- (`sendKA`/`receiveKA`) and `doneKA`.  `kaCnxt l d kcClient` has rows ONLY for the
-- two `apiKA` requests (`NodeSpecs:193-198`); every other label — including
-- `doneKA` — falls to the `:223` catch-all `nothing`, which is what `kcHead-no-io`
-- turns into `⊥`.
-- *** `apiKAev` is the ONE KA label deliberately NOT covered here ***, and it must
-- not be: `kcClient` genuinely DOES offer it.  What kills an `apiKA` label is the
-- node-level `apiES` synchronisation with a driver that never offers it
-- (`SysRoute.absnodes-no-nonCSBF`, applied at `LiveLegAssembly:1027-1034`) — not
-- the peer's own table.  (`apiKAev` is the KA-level constructor,
-- `KeepAlive.agda:85`; `apiKA` is the `Net_Api`-level name.)
data IsKAoff : {X : Set 0ℓ} → KA.KAEv X → Set where
  kaW-send : {l′ : Link} {d′ : Dir} → IsKAoff (KA.sendKA l′ d′)
  kaW-recv : {l′ : Link} {d′ : Dir} → IsKAoff (KA.receiveKA l′ d′)
  kaW-done : {l′ : Link} {d′ : Dir} → IsKAoff (KA.doneKA l′ d′)

-- the KA client AT ITS LOOP HEAD fires nothing on the wire: `kaCnxt l d kcClient`
-- has only the two `apiKA` request rows (`NodeSpecs:193-198`) and every other
-- label falls to the catch-all `nothing` (`NodeSpecs:223`)
kcHead-no-io : (l : Link) (cl : Dir) {X : Set 0ℓ} {e₁ : KA.KAEv X} {a : X} {P′ : NetProc}
  → IsKAoff e₁
  → absKAc l cl (SN.kcHead KA.stClient) ─[ ev (evl (evLabel X (ιKA e₁) a)) ]─► P′ → ⊥
kcHead-no-io l cl kaW-send step
  with tableSpec-ev-inv (record { isFin = NS.kaCfin ; nxt = NS.kaCnxt l cl }) NS.kcClient step
... | q′ , ceq , _ = nothing-absurd ceq
kcHead-no-io l cl kaW-recv step
  with tableSpec-ev-inv (record { isFin = NS.kaCfin ; nxt = NS.kaCnxt l cl }) NS.kcClient step
... | q′ , ceq , _ = nothing-absurd ceq
kcHead-no-io l cl kaW-done step
  with tableSpec-ev-inv (record { isFin = NS.kaCfin ; nxt = NS.kaCnxt l cl }) NS.kcClient step
... | q′ , ceq , _ = nothing-absurd ceq

-- … at the FROZEN slot of an arbitrary `InertPos` (the shape the split applies)
kcFrz-no-io : (l : Link) (cl : Dir) (ip : SN.InertPos)
    {X : Set 0ℓ} {e₁ : KA.KAEv X} {a : X} {P′ : NetProc}
  → IsKAoff e₁ → KAcAtHead ip
  → absKAc l cl (SN.kac ip) ─[ ev (evl (evLabel X (ιKA e₁) a)) ]─► P′ → ⊥
kcFrz-no-io l cl ip {X} {e₁} {a} {P′} wire h step =
  kcHead-no-io l cl wire
    (subst (λ q → absKAc l cl q ─[ ev (evl (evLabel X (ιKA e₁) a)) ]─► P′) h step)

-- the KA-channel bundle io inversion WITH the freeze fact: one successor
-- `InertPos`, the abstract landing equation, the concrete weak run, and the
-- preservation of the KA-client freeze
data KAFire (l : Link) (cl sv : Dir)
            (csc : SN.CScPos) (css : SN.CSsPos) (bfc : BFcPos) (bfs : BFsPos)
            (ip : SN.InertPos)
            {X : Set 0ℓ} (e₁ : KA.KAEv X) (a : X) (Bd′ : NetProc) : Set₁ where
  kaFireF : (ip′ : SN.InertPos)
          → Bd′ ≡ absBundleG l cl sv csc css bfc bfs ip′
          → SN.bundleG l cl sv csc css bfc bfs ip
              ═[ ev (evl (evLabel X (ιKA e₁) a)) ]═► SN.bundleG l cl sv csc css bfc bfs ip′
          → (KAcAtHead ip → KAcAtHead ip′)
          → KAFire l cl sv csc css bfc bfs ip e₁ a Bd′

-- the ABSTRACT ten-peer tail (CS c/s, BF c/s, TS c/s, LN c/s, LF c/s) offers no
-- KA-image event — the shared refutation of the split's two non-KA arms
-- (`SysIoLink6:714`'s chain, hoisted VERBATIM so both arms name it once; it is
-- what stands in for SIL6's ten-peer rung-by-rung continuation `:715-760`)
kaTail-abs-noKA : (l : Link) (cl sv : Dir)
    (csc : SN.CScPos) (css : SN.CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : SN.InertPos)
    {X : Set 0ℓ} (e₁ : KA.KAEv X) {a : X}
  → SStep.IoOffers (absCSc l cl csc ⦀ (absCSs l sv css ⦀ (absBFc l cl bfc ⦀ (absBFs l sv bfs
       ⦀ (absTSc l cl (SN.tsc ip) ⦀ (absTSs l sv (SN.tss ip)
       ⦀ (absLNc l cl (SN.lnc ip) ⦀ (absLNs l sv (SN.lns ip)
       ⦀ (absLFc l cl (SN.lfc ip) ⦀ absLFs l sv (SN.lfs ip)))))))))) (ιKA e₁) a → ⊥
kaTail-abs-noKA l cl sv csc css bfc bfs ip e₁ =
  ⦀-noOffer (absCSc l cl csc) _ (absCSc-noKA l cl csc e₁)
    (⦀-noOffer (absCSs l sv css) _ (absCSs-noKA l sv css e₁)
      (⦀-noOffer (absBFc l cl bfc) _ (absBFc-noKA l cl bfc e₁)
        (⦀-noOffer (absBFs l sv bfs) _ (absBFs-noKA l sv bfs e₁)
          (⦀-noOffer (absTSc l cl (SN.tsc ip)) _ (absTSc-noKA l cl (SN.tsc ip) e₁)
            (⦀-noOffer (absTSs l sv (SN.tss ip)) _ (absTSs-noKA l sv (SN.tss ip) e₁)
              (⦀-noOffer (absLNc l cl (SN.lnc ip)) _ (absLNc-noKA l cl (SN.lnc ip) e₁)
                (⦀-noOffer (absLNs l sv (SN.lns ip)) _ (absLNs-noKA l sv (SN.lns ip) e₁)
                  (⦀-noOffer (absLFc l cl (SN.lfc ip)) (absLFs l sv (SN.lfs ip))
                    (absLFc-noKA l cl (SN.lfc ip) e₁)
                    (absLFs-noKA l sv (SN.lfs ip) e₁)))))))))

-- THE SPLIT (transcription of `SysIoLink6:644-760` — the datatype `:644-656`, the
-- finisher BODIES `:658-697` and the peel's first two rungs `:699-714`, with
-- `:715-760` collapsed into `kaTail-abs-noKA` — plus the fact, and at the two
-- deviations the header records: `IsKAoff` strengthens the premise, `KAFire`'s
-- unpinned `ip′` weakens the conclusion)
kaFire : (l : Link) (cl sv : Dir) → cl ≢ sv
       → (csc : SN.CScPos) (css : SN.CSsPos) (bfc : BFcPos) (bfs : BFsPos)
         (ip : SN.InertPos)
       → {X : Set 0ℓ} {e₁ : KA.KAEv X} {a : X} {Bd′ : NetProc}
       → IsKAoff e₁
       → absBundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X (ιKA e₁) a)) ]─► Bd′
       → KAFire l cl sv csc css bfc bfs ip e₁ a Bd′
kaFire l cl sv cl≢sv csc css bfc bfs ip {X} {e₁} {a} wire step
  with PEA.Par-ev-elim Op.∅ES (λ _ _ → tt) (absKAc l cl (SN.kac ip)) _ step
... | PEA.evSync () _ _
... | PEA.evBoth _ sM sTail =
      ⊥-elim (⦀-noOffer (absKAs l sv (SN.kas ip)) _
                (absKAs-dir-noBoth l sv (SN.kas ip) e₁
                   (λ q → cl≢sv (trans (sym (absKAc-ev-dir l cl (SN.kac ip) sM)) q)))
                (kaTail-abs-noKA l cl sv csc css bfc bfs ip e₁) (_ , sTail))
-- THE CLIENT FIRED — the one arm the freeze refutes (`kcFrz-no-io`)
... | PEA.evL _ sM with decKAc-ev-prod-abs l cl (SN.kac ip) sM
...   | kac′ , run , Meq =
        kaFireF (record ip { kac = kac′ })
          (cong (λ z → z ⦀ (absKAs l sv (SN.kas ip) ⦀ (absCSc l cl csc ⦀ (absCSs l sv css
                 ⦀ (absBFc l cl bfc ⦀ (absBFs l sv bfs
                 ⦀ (absTSc l cl (SN.tsc ip) ⦀ (absTSs l sv (SN.tss ip)
                 ⦀ (absLNc l cl (SN.lnc ip) ⦀ (absLNs l sv (SN.lns ip)
                 ⦀ (absLFc l cl (SN.lfc ip) ⦀ absLFs l sv (SN.lfs ip)))))))))))) Meq)
          (⦀-wev-L (SN.decKAc l cl (SN.kac ip)) _
            (noOffer→viewV _
              (kaTail-kas-noOffer l cl sv csc css bfc bfs ip e₁
                (λ q → cl≢sv (trans (sym (absKAc-ev-dir l cl (SN.kac ip) sM)) q))))
            run)
          (λ h → ⊥-elim (kcFrz-no-io l cl ip wire h sM))
-- the KA SERVER fired (or the tail did, which is refuted): `kac` is untouched
kaFire l cl sv cl≢sv csc css bfc bfs ip {X} {e₁} {a} wire step | PEA.evR _ q1
    with PEA.Par-ev-elim Op.∅ES (λ _ _ → tt) (absKAs l sv (SN.kas ip)) _ q1
... | PEA.evSync () _ _
... | PEA.evL _ sM with decKAs-ev-prod-abs l sv (SN.kas ip) sM
...   | kas′ , run , Meq =
        kaFireF (record ip { kas = kas′ })
          (cong (λ z → absKAc l cl (SN.kac ip) ⦀ (z ⦀ (absCSc l cl csc ⦀ (absCSs l sv css
                 ⦀ (absBFc l cl bfc ⦀ (absBFs l sv bfs
                 ⦀ (absTSc l cl (SN.tsc ip) ⦀ (absTSs l sv (SN.tss ip)
                 ⦀ (absLNc l cl (SN.lnc ip) ⦀ (absLNs l sv (SN.lns ip)
                 ⦀ (absLFc l cl (SN.lfc ip) ⦀ absLFs l sv (SN.lfs ip)))))))))))) Meq)
          (⦀-wev-R (SN.decKAc l cl (SN.kac ip)) _
            (noOffer→viewV (SN.decKAc l cl (SN.kac ip))
              (decKAc-dir-noOffer l cl (SN.kac ip) e₁
                (λ q → cl≢sv (trans (sym q) (absKAs-ev-dir l sv (SN.kas ip) sM)))))
            (⦀-wev-L (SN.decKAs l sv (SN.kas ip)) _
              (noOffer→viewV _ (kaTail-csc-noOffer l cl sv csc css bfc bfs ip e₁))
              run))
          (λ h → h)
kaFire l cl sv cl≢sv csc css bfc bfs ip {X} {e₁} {a} wire step | PEA.evR _ q1 | PEA.evBoth _ sM sTail =
      ⊥-elim (kaTail-abs-noKA l cl sv csc css bfc bfs ip e₁ (_ , sTail))
kaFire l cl sv cl≢sv csc css bfc bfs ip {X} {e₁} {a} wire step | PEA.evR _ q1 | PEA.evR _ q2 =
      ⊥-elim (kaTail-abs-noKA l cl sv csc css bfc bfs ip e₁ (_ , q2))

------------------------------------------------------------------------
-- THE CONJUNCT, AT A WHOLE CONFIG — what `LiveLegAssembly.LegJoint⁺` carries.
--
-- It lives HERE, beside the position it is about and beside the inversion that
-- preserves it, for two reasons: the three cannot drift apart, and
-- `LiveLegAssembly` then depends on this module alone — which leaves
-- `LiveRetFree` free to name the assembly's `LegJointB` (the literal shape of the
-- premise (P5) once was) without a cycle.
------------------------------------------------------------------------

-- (P5)'s invariant conjunct: node B's link-AB bundle KA CLIENT is at its loop head
KAcFrz : SysState → Set
KAcFrz s = KAcAtHead (SN.NodeStateB.inert-AB (nB s))

-- THE SEED: `initial`'s eight inert slots are `initInert`, whose `kac` IS the
-- frozen head (`SysNode:780-781`) — the base case of the carried invariant
KAcFrz-init : KAcFrz initial
KAcFrz-init = refl
