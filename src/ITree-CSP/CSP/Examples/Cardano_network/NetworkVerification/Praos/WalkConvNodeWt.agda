{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- R3 — the io-sync NODE-WEIGHT ARITHMETIC scaffolding (WalkConv item (2)
-- support).  LIGHT (only `WalkConvMeasure` + `SysNode` records + `Data.Nat`);
-- no SIL6 inversion cone.
--
-- The io-sync bundle/node lift (`WalkConvNodeDrop`) threads a single firing
-- peer's leaf `posWt` drop up to a whole-node `nodesWt` drop.  This module
-- supplies the pure ℕ glue:
--   · `bundleWt` — one link-bundle's remaining-wire-event weight (the 5 driven
--     peers CS/BF client+server + the inert peer group of that link);
--   · the 12 per-peer `bundleWt-X-drop` lemmas — a firing peer's `posWt` drop
--     ⇒ the whole bundle's `bundleWt` drops (the other 4 slots FIXED), via
--     `+-mono{ˡ,ʳ}-<` chains (no reflection);
--   · the 4 `nodeWtX-split` identities — a node's `nodeWtX` equals the SUM of
--     its two link-bundles' `bundleWt` (a `+`-reassociation, `+-*-Solver`).
-- Together: a bundle drop on the firing link + the split ⇒ `nodeWtX nx′ <
-- nodeWtX nx` (one `+-monoˡ-<` at the node level, done in `WalkConvNodeDrop`).
--
-- No postulate/hole/meta.
------------------------------------------------------------------------

open import Data.Nat using (ℕ; _+_; _<_)
open import Data.Nat.Properties using (+-monoˡ-<; +-monoʳ-<)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkConvNodeWt (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysNode blkA
  using ( CScPos; CSsPos; BFcPos; BFsPos
        ; InertPos; tsc; tss; kac; kas; lnc; lns; lfc; lfs
        ; KAcPos; KAsPos; TScPos; TSsPos; LNcPos; LNsPos; LFcPos; LFsPos
        ; NodeStateA; NodeStateB; NodeStateC; NodeStateD )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkConvMeasure blkA
  using ( posWt-CSc; posWt-CSs; posWt-BFc; posWt-BFs; posWt-Inert
        ; posWt-KAc; posWt-KAs; posWt-TSc; posWt-TSs
        ; posWt-LNc; posWt-LNs; posWt-LFc; posWt-LFs
        ; nodeWtA; nodeWtB; nodeWtC; nodeWtD )

------------------------------------------------------------------------
-- one link-bundle's remaining-wire-event weight (the 5-slot sum, in the SAME
-- left-associated order the four `nodeWtX` use for that link's peers).
------------------------------------------------------------------------

-- CS client + CS server + BF client + BF server + the link's inert-peer group
bundleWt : CScPos → CSsPos → BFcPos → BFsPos → InertPos → ℕ
bundleWt csc css bfc bfs ip =
  posWt-CSc csc + posWt-CSs css + posWt-BFc bfc + posWt-BFs bfs + posWt-Inert ip

------------------------------------------------------------------------
-- The 8-slot inert-group drops — a single inert peer's `posWt` drop ⇒ the
-- whole `posWt-Inert (record ip { … })` drops (record projection reduces).
------------------------------------------------------------------------

-- `posWt-Inert ip = (((((( PTc + PTs) + PKc) + PKs) + PLc) + PLs) + PFc) + PFs`
-- TSc (slot 1) : left-most; six `+-monoˡ-<`
posWt-Inert-TSc-drop : ∀ {tsc′ ip} → posWt-TSc tsc′ < posWt-TSc (tsc ip)
  → posWt-Inert (record ip { tsc = tsc′ }) < posWt-Inert ip
posWt-Inert-TSc-drop {tsc′} {ip} lt =
  +-monoˡ-< (posWt-LFs (lfs ip)) (+-monoˡ-< (posWt-LFc (lfc ip)) (+-monoˡ-< (posWt-LNs (lns ip))
    (+-monoˡ-< (posWt-LNc (lnc ip)) (+-monoˡ-< (posWt-KAs (kas ip)) (+-monoˡ-< (posWt-KAc (kac ip))
      (+-monoˡ-< (posWt-TSs (tss ip)) lt))))))

-- TSs (slot 2)
posWt-Inert-TSs-drop : ∀ {tss′ ip} → posWt-TSs tss′ < posWt-TSs (tss ip)
  → posWt-Inert (record ip { tss = tss′ }) < posWt-Inert ip
posWt-Inert-TSs-drop {tss′} {ip} lt =
  +-monoˡ-< (posWt-LFs (lfs ip)) (+-monoˡ-< (posWt-LFc (lfc ip)) (+-monoˡ-< (posWt-LNs (lns ip))
    (+-monoˡ-< (posWt-LNc (lnc ip)) (+-monoˡ-< (posWt-KAs (kas ip)) (+-monoˡ-< (posWt-KAc (kac ip))
      (+-monoʳ-< (posWt-TSc (tsc ip)) lt))))))

-- KAc (slot 3)
posWt-Inert-KAc-drop : ∀ {kac′ ip} → posWt-KAc kac′ < posWt-KAc (kac ip)
  → posWt-Inert (record ip { kac = kac′ }) < posWt-Inert ip
posWt-Inert-KAc-drop {kac′} {ip} lt =
  +-monoˡ-< (posWt-LFs (lfs ip)) (+-monoˡ-< (posWt-LFc (lfc ip)) (+-monoˡ-< (posWt-LNs (lns ip))
    (+-monoˡ-< (posWt-LNc (lnc ip)) (+-monoˡ-< (posWt-KAs (kas ip))
      (+-monoʳ-< (posWt-TSc (tsc ip) + posWt-TSs (tss ip)) lt)))))

-- KAs (slot 4)
posWt-Inert-KAs-drop : ∀ {kas′ ip} → posWt-KAs kas′ < posWt-KAs (kas ip)
  → posWt-Inert (record ip { kas = kas′ }) < posWt-Inert ip
posWt-Inert-KAs-drop {kas′} {ip} lt =
  +-monoˡ-< (posWt-LFs (lfs ip)) (+-monoˡ-< (posWt-LFc (lfc ip)) (+-monoˡ-< (posWt-LNs (lns ip))
    (+-monoˡ-< (posWt-LNc (lnc ip))
      (+-monoʳ-< ((posWt-TSc (tsc ip) + posWt-TSs (tss ip)) + posWt-KAc (kac ip)) lt))))

-- LNc (slot 5)
posWt-Inert-LNc-drop : ∀ {lnc′ ip} → posWt-LNc lnc′ < posWt-LNc (lnc ip)
  → posWt-Inert (record ip { lnc = lnc′ }) < posWt-Inert ip
posWt-Inert-LNc-drop {lnc′} {ip} lt =
  +-monoˡ-< (posWt-LFs (lfs ip)) (+-monoˡ-< (posWt-LFc (lfc ip)) (+-monoˡ-< (posWt-LNs (lns ip))
    (+-monoʳ-< (((posWt-TSc (tsc ip) + posWt-TSs (tss ip)) + posWt-KAc (kac ip)) + posWt-KAs (kas ip)) lt)))

-- LNs (slot 6)
posWt-Inert-LNs-drop : ∀ {lns′ ip} → posWt-LNs lns′ < posWt-LNs (lns ip)
  → posWt-Inert (record ip { lns = lns′ }) < posWt-Inert ip
posWt-Inert-LNs-drop {lns′} {ip} lt =
  +-monoˡ-< (posWt-LFs (lfs ip)) (+-monoˡ-< (posWt-LFc (lfc ip))
    (+-monoʳ-< ((((posWt-TSc (tsc ip) + posWt-TSs (tss ip)) + posWt-KAc (kac ip)) + posWt-KAs (kas ip))
                 + posWt-LNc (lnc ip)) lt))

-- LFc (slot 7)
posWt-Inert-LFc-drop : ∀ {lfc′ ip} → posWt-LFc lfc′ < posWt-LFc (lfc ip)
  → posWt-Inert (record ip { lfc = lfc′ }) < posWt-Inert ip
posWt-Inert-LFc-drop {lfc′} {ip} lt =
  +-monoˡ-< (posWt-LFs (lfs ip))
    (+-monoʳ-< (((((posWt-TSc (tsc ip) + posWt-TSs (tss ip)) + posWt-KAc (kac ip)) + posWt-KAs (kas ip))
                  + posWt-LNc (lnc ip)) + posWt-LNs (lns ip)) lt)

-- LFs (slot 8) : right-most
posWt-Inert-LFs-drop : ∀ {lfs′ ip} → posWt-LFs lfs′ < posWt-LFs (lfs ip)
  → posWt-Inert (record ip { lfs = lfs′ }) < posWt-Inert ip
posWt-Inert-LFs-drop {lfs′} {ip} lt =
  +-monoʳ-< ((((((posWt-TSc (tsc ip) + posWt-TSs (tss ip)) + posWt-KAc (kac ip)) + posWt-KAs (kas ip))
                 + posWt-LNc (lnc ip)) + posWt-LNs (lns ip)) + posWt-LFc (lfc ip)) lt

------------------------------------------------------------------------
-- The 12 per-peer bundle drops.  `bundleWt = (((PC + PS) + PBc) + PBs) + PI`.
------------------------------------------------------------------------

-- CS-client (slot 1) : four `+-monoˡ-<`
bundleWt-CSc-drop : ∀ {csc′ csc css bfc bfs ip} → posWt-CSc csc′ < posWt-CSc csc
  → bundleWt csc′ css bfc bfs ip < bundleWt csc css bfc bfs ip
bundleWt-CSc-drop {csc′} {csc} {css} {bfc} {bfs} {ip} lt =
  +-monoˡ-< (posWt-Inert ip) (+-monoˡ-< (posWt-BFs bfs) (+-monoˡ-< (posWt-BFc bfc)
    (+-monoˡ-< (posWt-CSs css) lt)))

-- CS-server (slot 2)
bundleWt-CSs-drop : ∀ {css′ csc css bfc bfs ip} → posWt-CSs css′ < posWt-CSs css
  → bundleWt csc css′ bfc bfs ip < bundleWt csc css bfc bfs ip
bundleWt-CSs-drop {css′} {csc} {css} {bfc} {bfs} {ip} lt =
  +-monoˡ-< (posWt-Inert ip) (+-monoˡ-< (posWt-BFs bfs) (+-monoˡ-< (posWt-BFc bfc)
    (+-monoʳ-< (posWt-CSc csc) lt)))

-- BF-client (slot 3)
bundleWt-BFc-drop : ∀ {bfc′ csc css bfc bfs ip} → posWt-BFc bfc′ < posWt-BFc bfc
  → bundleWt csc css bfc′ bfs ip < bundleWt csc css bfc bfs ip
bundleWt-BFc-drop {bfc′} {csc} {css} {bfc} {bfs} {ip} lt =
  +-monoˡ-< (posWt-Inert ip) (+-monoˡ-< (posWt-BFs bfs)
    (+-monoʳ-< (posWt-CSc csc + posWt-CSs css) lt))

-- BF-server (slot 4)
bundleWt-BFs-drop : ∀ {bfs′ csc css bfc bfs ip} → posWt-BFs bfs′ < posWt-BFs bfs
  → bundleWt csc css bfc bfs′ ip < bundleWt csc css bfc bfs ip
bundleWt-BFs-drop {bfs′} {csc} {css} {bfc} {bfs} {ip} lt =
  +-monoˡ-< (posWt-Inert ip)
    (+-monoʳ-< ((posWt-CSc csc + posWt-CSs css) + posWt-BFc bfc) lt)

-- inert slot (5) : lift a `posWt-Inert` drop into the bundle
bundleWt-Inert-drop : ∀ {csc css bfc bfs ip′ ip} → posWt-Inert ip′ < posWt-Inert ip
  → bundleWt csc css bfc bfs ip′ < bundleWt csc css bfc bfs ip
bundleWt-Inert-drop {csc} {css} {bfc} {bfs} {ip′} {ip} lt =
  +-monoʳ-< (((posWt-CSc csc + posWt-CSs css) + posWt-BFc bfc) + posWt-BFs bfs) lt

-- the 8 inert-peer bundle drops = inert-group drop ∘ the slot lift
bundleWt-KAc-drop : ∀ {kac′ csc css bfc bfs ip} → posWt-KAc kac′ < posWt-KAc (kac ip)
  → bundleWt csc css bfc bfs (record ip { kac = kac′ }) < bundleWt csc css bfc bfs ip
bundleWt-KAc-drop {kac′} {csc} {css} {bfc} {bfs} {ip} lt =
  bundleWt-Inert-drop {csc} {css} {bfc} {bfs} {record ip { kac = kac′ }} {ip} (posWt-Inert-KAc-drop {kac′} {ip} lt)

bundleWt-KAs-drop : ∀ {kas′ csc css bfc bfs ip} → posWt-KAs kas′ < posWt-KAs (kas ip)
  → bundleWt csc css bfc bfs (record ip { kas = kas′ }) < bundleWt csc css bfc bfs ip
bundleWt-KAs-drop {kas′} {csc} {css} {bfc} {bfs} {ip} lt =
  bundleWt-Inert-drop {csc} {css} {bfc} {bfs} {record ip { kas = kas′ }} {ip} (posWt-Inert-KAs-drop {kas′} {ip} lt)

bundleWt-TSc-drop : ∀ {tsc′ csc css bfc bfs ip} → posWt-TSc tsc′ < posWt-TSc (tsc ip)
  → bundleWt csc css bfc bfs (record ip { tsc = tsc′ }) < bundleWt csc css bfc bfs ip
bundleWt-TSc-drop {tsc′} {csc} {css} {bfc} {bfs} {ip} lt =
  bundleWt-Inert-drop {csc} {css} {bfc} {bfs} {record ip { tsc = tsc′ }} {ip} (posWt-Inert-TSc-drop {tsc′} {ip} lt)

bundleWt-TSs-drop : ∀ {tss′ csc css bfc bfs ip} → posWt-TSs tss′ < posWt-TSs (tss ip)
  → bundleWt csc css bfc bfs (record ip { tss = tss′ }) < bundleWt csc css bfc bfs ip
bundleWt-TSs-drop {tss′} {csc} {css} {bfc} {bfs} {ip} lt =
  bundleWt-Inert-drop {csc} {css} {bfc} {bfs} {record ip { tss = tss′ }} {ip} (posWt-Inert-TSs-drop {tss′} {ip} lt)

bundleWt-LNc-drop : ∀ {lnc′ csc css bfc bfs ip} → posWt-LNc lnc′ < posWt-LNc (lnc ip)
  → bundleWt csc css bfc bfs (record ip { lnc = lnc′ }) < bundleWt csc css bfc bfs ip
bundleWt-LNc-drop {lnc′} {csc} {css} {bfc} {bfs} {ip} lt =
  bundleWt-Inert-drop {csc} {css} {bfc} {bfs} {record ip { lnc = lnc′ }} {ip} (posWt-Inert-LNc-drop {lnc′} {ip} lt)

bundleWt-LNs-drop : ∀ {lns′ csc css bfc bfs ip} → posWt-LNs lns′ < posWt-LNs (lns ip)
  → bundleWt csc css bfc bfs (record ip { lns = lns′ }) < bundleWt csc css bfc bfs ip
bundleWt-LNs-drop {lns′} {csc} {css} {bfc} {bfs} {ip} lt =
  bundleWt-Inert-drop {csc} {css} {bfc} {bfs} {record ip { lns = lns′ }} {ip} (posWt-Inert-LNs-drop {lns′} {ip} lt)

bundleWt-LFc-drop : ∀ {lfc′ csc css bfc bfs ip} → posWt-LFc lfc′ < posWt-LFc (lfc ip)
  → bundleWt csc css bfc bfs (record ip { lfc = lfc′ }) < bundleWt csc css bfc bfs ip
bundleWt-LFc-drop {lfc′} {csc} {css} {bfc} {bfs} {ip} lt =
  bundleWt-Inert-drop {csc} {css} {bfc} {bfs} {record ip { lfc = lfc′ }} {ip} (posWt-Inert-LFc-drop {lfc′} {ip} lt)

bundleWt-LFs-drop : ∀ {lfs′ csc css bfc bfs ip} → posWt-LFs lfs′ < posWt-LFs (lfs ip)
  → bundleWt csc css bfc bfs (record ip { lfs = lfs′ }) < bundleWt csc css bfc bfs ip
bundleWt-LFs-drop {lfs′} {csc} {css} {bfc} {bfs} {ip} lt =
  bundleWt-Inert-drop {csc} {css} {bfc} {bfs} {record ip { lfs = lfs′ }} {ip} (posWt-Inert-LFs-drop {lfs′} {ip} lt)

------------------------------------------------------------------------
-- The 4 node splits: `nodeWtX nx` = its two link-bundles' `bundleWt` sum
-- (a pure `+`-reassociation of the 10 peer weights, `+-*-Solver`).
------------------------------------------------------------------------

-- node A hosts links AB and AC
nodeWtA-split : (na : NodeStateA)
  → nodeWtA na ≡ bundleWt (NodeStateA.csC-AB na) (NodeStateA.csS-AB na) (NodeStateA.bfC-AB na) (NodeStateA.bfS-AB na) (NodeStateA.inert-AB na)
              + bundleWt (NodeStateA.csC-AC na) (NodeStateA.csS-AC na) (NodeStateA.bfC-AC na) (NodeStateA.bfS-AC na) (NodeStateA.inert-AC na)
nodeWtA-split na =
  solve 10 (λ a b c d e f g h i j →
              a :+ b :+ c :+ d :+ e :+ f :+ g :+ h :+ i :+ j
           := (a :+ b :+ c :+ d :+ i) :+ (e :+ f :+ g :+ h :+ j)) refl
    (posWt-CSc (NodeStateA.csC-AB na)) (posWt-CSs (NodeStateA.csS-AB na))
    (posWt-BFc (NodeStateA.bfC-AB na)) (posWt-BFs (NodeStateA.bfS-AB na))
    (posWt-CSc (NodeStateA.csC-AC na)) (posWt-CSs (NodeStateA.csS-AC na))
    (posWt-BFc (NodeStateA.bfC-AC na)) (posWt-BFs (NodeStateA.bfS-AC na))
    (posWt-Inert (NodeStateA.inert-AB na)) (posWt-Inert (NodeStateA.inert-AC na))

-- node B hosts links AB and BD
nodeWtB-split : (nb : NodeStateB)
  → nodeWtB nb ≡ bundleWt (NodeStateB.csC-AB nb) (NodeStateB.csS-AB nb) (NodeStateB.bfC-AB nb) (NodeStateB.bfS-AB nb) (NodeStateB.inert-AB nb)
              + bundleWt (NodeStateB.csC-BD nb) (NodeStateB.csS-BD nb) (NodeStateB.bfC-BD nb) (NodeStateB.bfS-BD nb) (NodeStateB.inert-BD nb)
nodeWtB-split nb =
  solve 10 (λ a b c d e f g h i j →
              a :+ b :+ c :+ d :+ e :+ f :+ g :+ h :+ i :+ j
           := (a :+ b :+ c :+ d :+ i) :+ (e :+ f :+ g :+ h :+ j)) refl
    (posWt-CSc (NodeStateB.csC-AB nb)) (posWt-CSs (NodeStateB.csS-AB nb))
    (posWt-BFc (NodeStateB.bfC-AB nb)) (posWt-BFs (NodeStateB.bfS-AB nb))
    (posWt-CSc (NodeStateB.csC-BD nb)) (posWt-CSs (NodeStateB.csS-BD nb))
    (posWt-BFc (NodeStateB.bfC-BD nb)) (posWt-BFs (NodeStateB.bfS-BD nb))
    (posWt-Inert (NodeStateB.inert-AB nb)) (posWt-Inert (NodeStateB.inert-BD nb))

-- node C hosts links AC and CD
nodeWtC-split : (nc : NodeStateC)
  → nodeWtC nc ≡ bundleWt (NodeStateC.csC-AC nc) (NodeStateC.csS-AC nc) (NodeStateC.bfC-AC nc) (NodeStateC.bfS-AC nc) (NodeStateC.inert-AC nc)
              + bundleWt (NodeStateC.csC-CD nc) (NodeStateC.csS-CD nc) (NodeStateC.bfC-CD nc) (NodeStateC.bfS-CD nc) (NodeStateC.inert-CD nc)
nodeWtC-split nc =
  solve 10 (λ a b c d e f g h i j →
              a :+ b :+ c :+ d :+ e :+ f :+ g :+ h :+ i :+ j
           := (a :+ b :+ c :+ d :+ i) :+ (e :+ f :+ g :+ h :+ j)) refl
    (posWt-CSc (NodeStateC.csC-AC nc)) (posWt-CSs (NodeStateC.csS-AC nc))
    (posWt-BFc (NodeStateC.bfC-AC nc)) (posWt-BFs (NodeStateC.bfS-AC nc))
    (posWt-CSc (NodeStateC.csC-CD nc)) (posWt-CSs (NodeStateC.csS-CD nc))
    (posWt-BFc (NodeStateC.bfC-CD nc)) (posWt-BFs (NodeStateC.bfS-CD nc))
    (posWt-Inert (NodeStateC.inert-AC nc)) (posWt-Inert (NodeStateC.inert-CD nc))

-- node D hosts links BD and CD
nodeWtD-split : (nd : NodeStateD)
  → nodeWtD nd ≡ bundleWt (NodeStateD.csC-BD nd) (NodeStateD.csS-BD nd) (NodeStateD.bfC-BD nd) (NodeStateD.bfS-BD nd) (NodeStateD.inert-BD nd)
              + bundleWt (NodeStateD.csC-CD nd) (NodeStateD.csS-CD nd) (NodeStateD.bfC-CD nd) (NodeStateD.bfS-CD nd) (NodeStateD.inert-CD nd)
nodeWtD-split nd =
  solve 10 (λ a b c d e f g h i j →
              a :+ b :+ c :+ d :+ e :+ f :+ g :+ h :+ i :+ j
           := (a :+ b :+ c :+ d :+ i) :+ (e :+ f :+ g :+ h :+ j)) refl
    (posWt-CSc (NodeStateD.csC-BD nd)) (posWt-CSs (NodeStateD.csS-BD nd))
    (posWt-BFc (NodeStateD.bfC-BD nd)) (posWt-BFs (NodeStateD.bfS-BD nd))
    (posWt-CSc (NodeStateD.csC-CD nd)) (posWt-CSs (NodeStateD.csS-CD nd))
    (posWt-BFc (NodeStateD.bfC-CD nd)) (posWt-BFs (NodeStateD.bfS-CD nd))
    (posWt-Inert (NodeStateD.inert-BD nd)) (posWt-Inert (NodeStateD.inert-CD nd))
