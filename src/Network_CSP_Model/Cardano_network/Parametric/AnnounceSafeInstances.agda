{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — ANNOUNCEMENT SAFETY OF THE SHIPPED INSTANCES,
-- premise-free.
--
-- `AnnounceSafeConcrete.announceSafeT` carries one premise, `LinkCfgWf`:
-- every link's configuration is non-empty and duplicate-free.  All three
-- shipped topologies configure every link with the same literal list of
-- eight (direction , protocol) pairs, so the premise is DECIDED, not
-- proved: `unique?` over the decidable equality of `Dir × IDs`, read off
-- with `from-yes`.  Non-emptiness is `λ ()` on a cons.
--
-- The diamond keeps its OWN `apiES` term (`FourNodeDiamond.apiES`, for
-- `DiamondInstance`'s faithfulness gate), so the copy-medium theorem is
-- re-assembled for it from `AnnounceSafeCopy.Generic.Assembly` under the
-- two `apiES` facts — both `tt`, by the same `apiSet` clauses the shared
-- alphabet has.  The line and the star use the shared `ApiAlphabet.apiES`
-- and take the headline directly.
------------------------------------------------------------------------

module CSP.Examples.Cardano_network.Parametric.AnnounceSafeInstances where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Product using (_×_; _,_)
open import Data.Product.Properties using (≡-dec)
open import Data.Unit.Polymorphic using (tt)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary.Decidable using (from-yes)
open import Class.DecEq using (DecEq)

open import CSP.Examples.Cardano_network.Base using (Dir; IDs; DecEq-Dir; DecEq-IDs)
import CSP.Examples.Cardano_network.ApiAlphabet as AA
import CSP.Examples.Cardano_network.Parametric.AnnounceSafe as AS
import CSP.Examples.Cardano_network.Parametric.AnnounceSafeCopy as ASCopy
import CSP.Examples.Cardano_network.Parametric.AnnounceSafeConcrete as ASC
open ASC using (LinkCfgWf)
import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond as FND
import CSP.Examples.Cardano_network.Parametric.DiamondInstance as DI
import CSP.Examples.Cardano_network.Parametric.LineInstance as LI
import CSP.Examples.Cardano_network.Parametric.StarInstance as SI

-- decidable equality of a configuration entry
entry-≟ : DecidableEquality (Dir × IDs)
entry-≟ = ≡-dec (DecEq._≟_ DecEq-Dir) (DecEq._≟_ DecEq-IDs)

open import Data.List.Relation.Unary.Unique.DecPropositional entry-≟ using (unique?)

------------------------------------------------------------------------
-- The line (two links, `lineCfg` on each)
------------------------------------------------------------------------

-- every link of the line is well-formed
lineCfgWf : LinkCfgWf LI.lineParams
lineCfgWf _ = (λ ()) , from-yes (unique? LI.lineCfg)

-- announcement safety of the line over the concrete medium, no premise
lineAnnounceSafeT : AS.Generic.AnnounceSafeT LI.lineParams LI.line (AA.apiES LI.lineParams)
lineAnnounceSafeT = ASC.announceSafeT LI.lineParams LI.line lineCfgWf

------------------------------------------------------------------------
-- The star (four links, `starCfg` on each)
------------------------------------------------------------------------

-- every link of the star is well-formed
starCfgWf : LinkCfgWf SI.starParams
starCfgWf _ = (λ ()) , from-yes (unique? SI.starCfg)

-- announcement safety of the star over the concrete medium, no premise
starAnnounceSafeT : AS.Generic.AnnounceSafeT SI.starParams SI.star (AA.apiES SI.starParams)
starAnnounceSafeT = ASC.announceSafeT SI.starParams SI.star starCfgWf

------------------------------------------------------------------------
-- The diamond (four links, `uniformCfg` on each, its OWN `apiES`)
------------------------------------------------------------------------

-- every link of the diamond is well-formed
diamondCfgWf : LinkCfgWf FND.p
diamondCfgWf _ = (λ ()) , from-yes (unique? FND.uniformCfg)

-- announcement safety of the diamond over the concrete medium, at the diamond's own
-- api alphabet, no premise: the copy-medium assembly under its two `apiES` facts
-- (the announcement and both BlockFetch block channels are synchronised — `apiSet`
-- is `⊤` on `apiLN` and `apiBF`), then the medium transport
diamondAnnounceSafeT : AS.Generic.AnnounceSafeT FND.p DI.diamond FND.apiES
diamondAnnounceSafeT =
  ASC.Generic.transport FND.p DI.diamond FND.apiES diamondCfgWf
    (ASCopy.Generic.Assembly.announceSafeT-copy FND.p DI.diamond FND.apiES
      (λ {l} {d} _ → tt) (λ {l} {d} _ → tt , tt))
