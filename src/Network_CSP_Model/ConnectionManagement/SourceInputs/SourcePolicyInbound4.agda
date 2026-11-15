{-# OPTIONS --guardedness #-}

-- Rechecks every original edge under the source 5/120 policy profile.
-- Explicit transformed successors are independently checked by refl.
module ConnectionManagement.SourceInputs.SourcePolicyInbound4 where
open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.InboundConfiguredSupport using (module B)
import ConnectionManagement.SourceInputs.Policy as Policy
configure : B.State → B.State
configure s = record s { runtime = Policy.runtime (B.runtime s) }
import ConnectionManagement.Negative.InboundConfiguredChainResult0 as S33
import ConnectionManagement.Negative.InboundConfiguredChainResult1 as S34
import ConnectionManagement.Negative.InboundConfiguredChainResult2 as S35
import ConnectionManagement.Negative.InboundConfiguredChainResult3 as S36
import ConnectionManagement.Negative.InboundConfiguredKeepContract0 as S37
import ConnectionManagement.Negative.InboundConfiguredKeepContract1 as S38
import ConnectionManagement.Negative.InboundConfiguredKeepResult0 as S39
import ConnectionManagement.Negative.InboundConfiguredKeepResult1 as S40
import ConnectionManagement.Negative.InboundConfiguredKeepResult2 as S41

abstract
  path33 : B.Runs (configure S33.s0) S33.actions (configure S33.s3)
  path33 = B.more {t = configure S33.s1} refl (B.more {t = configure S33.s2} refl (B.more {t = configure S33.s3} refl (B.done)))

  path34 : B.Runs (configure S34.s0) S34.actions (configure S34.s3)
  path34 = B.more {t = configure S34.s1} refl (B.more {t = configure S34.s2} refl (B.more {t = configure S34.s3} refl (B.done)))

  path35 : B.Runs (configure S35.s0) S35.actions (configure S35.s3)
  path35 = B.more {t = configure S35.s1} refl (B.more {t = configure S35.s2} refl (B.more {t = configure S35.s3} refl (B.done)))

  path36 : B.Runs (configure S36.s0) S36.actions (configure S36.s3)
  path36 = B.more {t = configure S36.s1} refl (B.more {t = configure S36.s2} refl (B.more {t = configure S36.s3} refl (B.done)))

  path37 : B.Runs (configure S37.s0) S37.actions (configure S37.s3)
  path37 = B.more {t = configure S37.s1} refl (B.more {t = configure S37.s2} refl (B.more {t = configure S37.s3} refl (B.done)))

  path38 : B.Runs (configure S38.s0) S38.actions (configure S38.s1)
  path38 = B.more {t = configure S38.s1} refl (B.done)

  path39 : B.Runs (configure S39.s0) S39.actions (configure S39.s3)
  path39 = B.more {t = configure S39.s1} refl (B.more {t = configure S39.s2} refl (B.more {t = configure S39.s3} refl (B.done)))

  path40 : B.Runs (configure S40.s0) S40.actions (configure S40.s3)
  path40 = B.more {t = configure S40.s1} refl (B.more {t = configure S40.s2} refl (B.more {t = configure S40.s3} refl (B.done)))

  path41 : B.Runs (configure S41.s0) S41.actions (configure S41.s3)
  path41 = B.more {t = configure S41.s1} refl (B.more {t = configure S41.s2} refl (B.more {t = configure S41.s3} refl (B.done)))

