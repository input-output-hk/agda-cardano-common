{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — the bridge between the two node-bundle
-- builders of `NetworkPar`:
--
--   * `nodeBundle l cl sv` — CONFIG-DRIVEN: `⦀⋆`-folds one peer per
--     `(direction, protocol)` entry of `linkConfig l`, playing CLIENT on
--     direction `cl` and SERVER on direction `sv`;
--   * `miniProtocols l cl sv` — UNIFORM: hard-wires all twelve peers
--     (KA/CS/BF/TS/LN/LF, client on `cl`, server on `sv`).
--
-- They agree only on a link whose config lists exactly those twelve
-- instances, in `miniProtocols`' own order — that is `FullConfig` below.
-- The hypothesis is a propositional equality with the *literal* list, so
-- a scenario that configures anything less (e.g. the CS+BF-only diamond
-- of `FourNode/FourNodeDiamondCfg`) simply cannot apply the bridge.
--
-- Even under `FullConfig` the two are NOT `≡`: `⦀⋆` pads its fold with a
-- trailing `Skip`, and `⦀` is not unital up to `≡`.  Hence `∼`.
--
-- BOTH endpoints are proved, but at DIFFERENT strengths:
--
--   * `cl ≡ lo` (§4) at `∼`.  The config order already matches
--     `miniProtocols`, so the trailing `Skip` is the only difference and
--     the unconditional strong-bisimulation congruence closes it.
--
--   * `cl ≡ hi` (§6) at `≈FD` — and NOT at `∼`.  At this endpoint every
--     entry's role inverts (`linkConfig` is ordered by DIRECTION,
--     `miniProtocols` by ROLE), so `nodeBundle l hi lo` emits each protocol
--     SERVER-then-CLIENT where `miniProtocols l hi lo` emits it
--     CLIENT-then-SERVER: six disjoint adjacent transpositions.  Each one
--     is the EXCHANGE law `P ⦀ (Q ⦀ R) ≈FD Q ⦀ (P ⦀ R)`
--     (`CSP.Laws.FD.ParallelExchange.⦀-exchange-FD`), which is FALSE at
--     `∼`: with `P = a ⟶ Stop`, `Q = a ⟶ b ⟶ Stop`, `R = a ⟶ c ⟶ Stop`
--     a three-way offer of `a` makes `par-pVis` build nested `par-brBoth`
--     ⊓-nodes, so after `a` the left side can τ-commit to `Stop ⦀ (Q ⦀ R)`
--     while the right side's only τ-successors are `(b ⟶ Stop) ⦀ (P ⦀ R)`
--     (which offers `b` at once) and `Q ⦀ brBoth(P,R)` (τ-unstable);
--     neither matches, and `∼` is τ-sensitive.  The same three-way
--     collision refutes `⦀` ASSOCIATIVITY at `∼`, which is why the repo
--     proves associativity only at `≈FD` too.
--
-- The `hi` branch needs NO separation side condition anywhere: exchange
-- reassociates with the unconditional `⦀-assoc-FD` and swaps with the
-- unconditional `∼`-congruence (commutativity holds at `∼`), and the
-- depth-wise rewriting rides `⦀-cong-FD`, which is the FACT-SHAPED
-- `⦀-mono-⊑FD` read in both directions — also unconditional.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.Params using (Params)

module CSP.Examples.Cardano_network.BundleBridge (p : Params) where

open import Level using (0ℓ)
open import Data.Unit.Polymorphic using (⊤)
open import Data.Bool using (if_then_else_)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Class.DecEq using (_≟_)

open import Process_Trees using (PTree; AnyTypes; ExtI)

open import CSP.Examples.Cardano_network.Base
  using (Dir; lo; hi; IDs; N2N_KeepAlive; N2N_ChainSync; N2N_BlockFetch;
         N2N_TxSubmission; N2N_LeiosNotify; N2N_LeiosFetch)
open Params p using (linkConfig)
open import CSP.Examples.Cardano_network.Net p using (Link; Net_Api; Net_Api-≟)
open import CSP.Examples.Cardano_network.Data p using (Payload; DecEq-Payload)
open import CSP.Examples.Cardano_network.NetworkPar p
  using (nodeBundle; miniProtocols; clientPeer; serverPeer; LFserverA; LFclientA)

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using (_⦀_; ⦀⋆; Skip; ∅ES)

open import Semantics.Bisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (_∼_; sbisim-refl; sbisim-trans)
open import Semantics.DRBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (_≈DR_)
open import Semantics.FailuresDivergences {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (_≈FD_; ≈FD-trans)
open import Semantics.StrongImpliesDR {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (sbisim→drbisim)
open import Semantics.DRImpliesFD {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (drbisim→≈FD)
open import CSP.Laws.Bisim.ParallelCong (Net_Api-≟ {Payload}) using (cong-⦀-∼)
open import CSP.Laws.FD.ParallelComm    (Net_Api-≟ {Payload}) using (Par-comm)
open import CSP.Laws.FD.ParallelUnit    (Net_Api-≟ {Payload}) using (Par-ret-unit)
open import CSP.Laws.FD.ParallelExchange (Net_Api-≟ {Payload})
  using (∼→≈FD; ⦀-tail-FD; ⦀-comm-FD; ⦀-exchange-FD)

-- the node-bundle carrier: a ⊤-returning process tree over `Net_Api Payload`
Peer : Set₁
Peer = PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})

------------------------------------------------------------------------
-- §1  The full-config hypothesis
------------------------------------------------------------------------

-- the config under which `nodeBundle` reproduces `miniProtocols`: both
-- directions of every protocol, in `miniProtocols`' own order (KA, CS, BF,
-- TS, LN, LF), `lo` before `hi` inside each pair
fullCfg : List (Dir × IDs)
fullCfg = (lo , N2N_KeepAlive)    ∷ (hi , N2N_KeepAlive)
        ∷ (lo , N2N_ChainSync)    ∷ (hi , N2N_ChainSync)
        ∷ (lo , N2N_BlockFetch)   ∷ (hi , N2N_BlockFetch)
        ∷ (lo , N2N_TxSubmission) ∷ (hi , N2N_TxSubmission)
        ∷ (lo , N2N_LeiosNotify)  ∷ (hi , N2N_LeiosNotify)
        ∷ (lo , N2N_LeiosFetch)   ∷ (hi , N2N_LeiosFetch) ∷ []

-- link `l` carries every instance, so its bundle is the uniform one.  This
-- is deliberately an equality with the LITERAL list, not a membership or
-- length condition: a partially-configured link cannot satisfy it.
FullConfig : Link → Set
FullConfig l = linkConfig l ≡ fullCfg

------------------------------------------------------------------------
-- §2  `nodeBundle` as a function of the config list
------------------------------------------------------------------------

-- the map body of `nodeBundle`: client on `cl`, server on `sv`, `Skip` on
-- any other direction (named so that the config can be substituted under it)
peerOf : Link → Dir → Dir → Dir × IDs → Peer
peerOf l cl sv (d , id) = if ⌊ d ≟ cl ⌋ then clientPeer l d id
                          else if ⌊ d ≟ sv ⌋ then serverPeer l d id
                          else Skip

-- the config-driven bundle, with the config list as an explicit argument
bundleFrom : Link → Dir → Dir → List (Dir × IDs) → Peer
bundleFrom l cl sv cfg = ⦀⋆ (map (peerOf l cl sv) cfg)

-- `nodeBundle` IS `bundleFrom` at the link's own config (definitional)
nodeBundle-is-bundleFrom : (l : Link) (cl sv : Dir)
                         → nodeBundle l cl sv ≡ bundleFrom l cl sv (linkConfig l)
nodeBundle-is-bundleFrom l cl sv = refl

------------------------------------------------------------------------
-- §3  `Skip` is a right unit of `⦀` up to `∼`
------------------------------------------------------------------------

-- `⦀⋆` pads with a trailing `Skip`; strip it by commuting and using the
-- library's LEFT unit `Par-ret-unit`
⦀-SkipR : (P : Peer) → (P ⦀ Skip) ∼ P
⦀-SkipR P = sbisim-trans (Par-comm ∅ES P Skip) (Par-ret-unit P)

-- rewrite the TAIL of one `⦀` level, leaving the head alone (the unconditional
-- strong-bisimulation congruence of Task 1, specialised to a fixed head)
⦀-tail : (P : Peer) {Q Q′ : Peer} → Q ∼ Q′ → (P ⦀ Q) ∼ (P ⦀ Q′)
⦀-tail P q∼ = cong-⦀-∼ (sbisim-refl P) q∼

------------------------------------------------------------------------
-- §4  The bridge at the `lo` endpoint
------------------------------------------------------------------------

-- under `fullCfg` the `cl = lo` bundle is `miniProtocols l lo hi` with one
-- extra trailing `Skip`: thread `⦀-SkipR` up through the eleven `⦀` levels
-- with the (unconditional) strong-bisimulation congruence `cong-⦀-∼`
bundleFrom-lo∼mini : (l : Link)
                   → bundleFrom l lo hi fullCfg ∼ miniProtocols l lo hi
bundleFrom-lo∼mini l =
  ⦀-tail _ (⦀-tail _ (⦀-tail _ (⦀-tail _ (⦀-tail _ (⦀-tail _
  (⦀-tail _ (⦀-tail _ (⦀-tail _ (⦀-tail _ (⦀-tail _
  (⦀-SkipR (LFserverA l hi))))))))))))

-- THE BRIDGE (lo endpoint): on a fully-configured link the config-driven
-- bundle and the uniform one are STRONGLY bisimilar.  Not `≡`: they differ
-- by `⦀⋆`'s trailing `Skip`, and `⦀` is not unital up to `≡`.
nodeBundle∼miniProtocols-lo : (l : Link) → FullConfig l
                            → nodeBundle l lo hi ∼ miniProtocols l lo hi
nodeBundle∼miniProtocols-lo l eq =
  subst (λ cfg → bundleFrom l lo hi cfg ∼ miniProtocols l lo hi)
        (sym eq) (bundleFrom-lo∼mini l)

------------------------------------------------------------------------
-- §5  Corollaries down the semantic ladder
------------------------------------------------------------------------

-- ≈DR via `sbisim→drbisim`
nodeBundle≈DRminiProtocols-lo : (l : Link) → FullConfig l
                              → nodeBundle l lo hi ≈DR miniProtocols l lo hi
nodeBundle≈DRminiProtocols-lo l eq = sbisim→drbisim (nodeBundle∼miniProtocols-lo l eq)

-- ≈FD via `drbisim→≈FD`: the switch to the config-driven builder loses no
-- failures-divergences fact at the `lo` endpoint
nodeBundle≈FDminiProtocols-lo : (l : Link) → FullConfig l
                              → nodeBundle l lo hi ≈FD miniProtocols l lo hi
nodeBundle≈FDminiProtocols-lo l eq = drbisim→≈FD (nodeBundle≈DRminiProtocols-lo l eq)

------------------------------------------------------------------------
-- §6  The bridge at the `hi` endpoint — at `≈FD`, unconditionally
------------------------------------------------------------------------

-- one adjacent transposition, applied at the head of a `⦀` spine whose tail
-- has already been permuted: rewrite under the two fixed heads with the
-- unconditional `≈FD`-congruence, then exchange them at the root
swapStep : {P Q X Y : Peer} → X ≈FD Y → (P ⦀ (Q ⦀ X)) ≈FD (Q ⦀ (P ⦀ Y))
swapStep {P} {Q} h = ≈FD-trans (⦀-tail-FD P (⦀-tail-FD Q h)) (⦀-exchange-FD P Q _)

-- under `fullCfg` the `cl = hi` bundle lists each protocol SERVER-then-CLIENT
-- (config order is by DIRECTION) while `miniProtocols` lists it
-- CLIENT-then-SERVER.  (a) absorb `⦀⋆`'s trailing `Skip` FIRST, at `∼`, so no
-- later rewrite has to drag it along; (b) undo the six disjoint adjacent
-- transpositions, innermost pair first — the last pair has no tail, so it is
-- plain commutativity, and each of the other five is one `swapStep`.
bundleFrom-hi≈mini : (l : Link)
                   → bundleFrom l hi lo fullCfg ≈FD miniProtocols l hi lo
bundleFrom-hi≈mini l =
  ≈FD-trans
    (∼→≈FD (⦀-tail _ (⦀-tail _ (⦀-tail _ (⦀-tail _ (⦀-tail _ (⦀-tail _
            (⦀-tail _ (⦀-tail _ (⦀-tail _ (⦀-tail _ (⦀-tail _
            (⦀-SkipR (LFclientA l hi))))))))))))))
    (swapStep (swapStep (swapStep (swapStep (swapStep (⦀-comm-FD _ _))))))

-- THE BRIDGE (hi endpoint): on a fully-configured link the config-driven
-- bundle and the uniform one are FAILURES-DIVERGENCES equivalent.  NOT `∼`,
-- and not `≈DR`: the role inversion needs `⦀`-exchange, which is false at `∼`
-- (see this module's header).
nodeBundle≈FDminiProtocols-hi : (l : Link) → FullConfig l
                              → nodeBundle l hi lo ≈FD miniProtocols l hi lo
nodeBundle≈FDminiProtocols-hi l eq =
  subst (λ cfg → bundleFrom l hi lo cfg ≈FD miniProtocols l hi lo)
        (sym eq) (bundleFrom-hi≈mini l)

------------------------------------------------------------------------
-- §7  Both endpoints, uniformly
------------------------------------------------------------------------

-- the other direction of a link
opp : Dir → Dir
opp lo = hi
opp hi = lo

-- BOTH endpoints at `≈FD`, quantified over the client direction.  Stated at
-- `≈FD` because that is all the `hi` half can honestly claim; the `lo` half is
-- strictly stronger and keeps its `∼` statement in §4.
nodeBundle≈FDminiProtocols : (l : Link) → FullConfig l → (cl : Dir)
                           → nodeBundle l cl (opp cl) ≈FD miniProtocols l cl (opp cl)
nodeBundle≈FDminiProtocols l eq lo = nodeBundle≈FDminiProtocols-lo l eq
nodeBundle≈FDminiProtocols l eq hi = nodeBundle≈FDminiProtocols-hi l eq
