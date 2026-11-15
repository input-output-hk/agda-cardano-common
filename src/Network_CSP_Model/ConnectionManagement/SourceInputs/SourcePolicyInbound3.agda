{-# OPTIONS --guardedness #-}

-- Rechecks every original edge under the source 5/120 policy profile.
-- Explicit transformed successors are independently checked by refl.
module ConnectionManagement.SourceInputs.SourcePolicyInbound3 where
open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.InboundConfiguredSupport using (module B)
import ConnectionManagement.SourceInputs.Policy as Policy
configure : B.State → B.State
configure s = record s { runtime = Policy.runtime (B.runtime s) }
import ConnectionManagement.Negative.InboundConfiguredStart11 as S24
import ConnectionManagement.Negative.InboundConfiguredStart12 as S25
import ConnectionManagement.Negative.InboundConfiguredStart13 as S26
import ConnectionManagement.Negative.InboundConfiguredStart14 as S27
import ConnectionManagement.Negative.InboundConfiguredStart15 as S28
import ConnectionManagement.Negative.InboundConfiguredStart16 as S29
import ConnectionManagement.Negative.InboundConfiguredStart17 as S30
import ConnectionManagement.Negative.InboundConfiguredChainContract0 as S31
import ConnectionManagement.Negative.InboundConfiguredChainContract1 as S32

abstract
  path24 : B.Runs (configure S24.s0) S24.actions (configure S24.s3)
  path24 = B.more {t = configure S24.s1} refl (B.more {t = configure S24.s2} refl (B.more {t = configure S24.s3} refl (B.done)))

  path25 : B.Runs (configure S25.s0) S25.actions (configure S25.s3)
  path25 = B.more {t = configure S25.s1} refl (B.more {t = configure S25.s2} refl (B.more {t = configure S25.s3} refl (B.done)))

  path26 : B.Runs (configure S26.s0) S26.actions (configure S26.s3)
  path26 = B.more {t = configure S26.s1} refl (B.more {t = configure S26.s2} refl (B.more {t = configure S26.s3} refl (B.done)))

  path27 : B.Runs (configure S27.s0) S27.actions (configure S27.s3)
  path27 = B.more {t = configure S27.s1} refl (B.more {t = configure S27.s2} refl (B.more {t = configure S27.s3} refl (B.done)))

  path28 : B.Runs (configure S28.s0) S28.actions (configure S28.s3)
  path28 = B.more {t = configure S28.s1} refl (B.more {t = configure S28.s2} refl (B.more {t = configure S28.s3} refl (B.done)))

  path29 : B.Runs (configure S29.s0) S29.actions (configure S29.s3)
  path29 = B.more {t = configure S29.s1} refl (B.more {t = configure S29.s2} refl (B.more {t = configure S29.s3} refl (B.done)))

  path30 : B.Runs (configure S30.s0) S30.actions (configure S30.s2)
  path30 = B.more {t = configure S30.s1} refl (B.more {t = configure S30.s2} refl (B.done))

  path31 : B.Runs (configure S31.s0) S31.actions (configure S31.s3)
  path31 = B.more {t = configure S31.s1} refl (B.more {t = configure S31.s2} refl (B.more {t = configure S31.s3} refl (B.done)))

  path32 : B.Runs (configure S32.s0) S32.actions (configure S32.s2)
  path32 = B.more {t = configure S32.s1} refl (B.more {t = configure S32.s2} refl (B.done))

