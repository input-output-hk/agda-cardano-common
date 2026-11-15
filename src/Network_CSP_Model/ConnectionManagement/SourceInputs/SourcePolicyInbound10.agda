{-# OPTIONS --guardedness #-}

-- Rechecks every original edge under the source 5/120 policy profile.
-- Explicit transformed successors are independently checked by refl.
module ConnectionManagement.SourceInputs.SourcePolicyInbound10 where
open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.InboundConfiguredSupport using (module B)
import ConnectionManagement.SourceInputs.Policy as Policy
configure : B.State → B.State
configure s = record s { runtime = Policy.runtime (B.runtime s) }
import ConnectionManagement.Negative.InboundConfiguredCleanup6 as S83
import ConnectionManagement.Negative.InboundConfiguredCleanup7 as S84

abstract
  path83 : B.Runs (configure S83.s0) S83.actions (configure S83.s3)
  path83 = B.more {t = configure S83.s1} refl (B.more {t = configure S83.s2} refl (B.more {t = configure S83.s3} refl (B.done)))

  path84 : B.Runs (configure S84.s0) S84.actions (configure S84.s3)
  path84 = B.more {t = configure S84.s1} refl (B.more {t = configure S84.s2} refl (B.more {t = configure S84.s3} refl (B.done)))

