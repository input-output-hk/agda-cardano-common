{-# OPTIONS --guardedness #-}

-- Rechecks every original edge under the source 5/120 policy profile.
-- Explicit transformed successors are independently checked by refl.
module ConnectionManagement.SourceInputs.SourcePolicyInbound5 where
open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.InboundConfiguredSupport using (module B)
import ConnectionManagement.SourceInputs.Policy as Policy
configure : B.State → B.State
configure s = record s { runtime = Policy.runtime (B.runtime s) }
import ConnectionManagement.Negative.InboundConfiguredKeepResult3 as S42
import ConnectionManagement.Negative.InboundConfiguredFetchContract0 as S43
import ConnectionManagement.Negative.InboundConfiguredFetchContract1 as S44
import ConnectionManagement.Negative.InboundConfiguredFetchResult0 as S45
import ConnectionManagement.Negative.InboundConfiguredFetchResult1 as S46
import ConnectionManagement.Negative.InboundConfiguredFetchResult2 as S47
import ConnectionManagement.Negative.InboundConfiguredFetchResult3 as S48
import ConnectionManagement.Negative.InboundConfiguredTxContract0 as S49

abstract
  path42 : B.Runs (configure S42.s0) S42.actions (configure S42.s3)
  path42 = B.more {t = configure S42.s1} refl (B.more {t = configure S42.s2} refl (B.more {t = configure S42.s3} refl (B.done)))

  path43 : B.Runs (configure S43.s0) S43.actions (configure S43.s3)
  path43 = B.more {t = configure S43.s1} refl (B.more {t = configure S43.s2} refl (B.more {t = configure S43.s3} refl (B.done)))

  path44 : B.Runs (configure S44.s0) S44.actions (configure S44.s2)
  path44 = B.more {t = configure S44.s1} refl (B.more {t = configure S44.s2} refl (B.done))

  path45 : B.Runs (configure S45.s0) S45.actions (configure S45.s3)
  path45 = B.more {t = configure S45.s1} refl (B.more {t = configure S45.s2} refl (B.more {t = configure S45.s3} refl (B.done)))

  path46 : B.Runs (configure S46.s0) S46.actions (configure S46.s3)
  path46 = B.more {t = configure S46.s1} refl (B.more {t = configure S46.s2} refl (B.more {t = configure S46.s3} refl (B.done)))

  path47 : B.Runs (configure S47.s0) S47.actions (configure S47.s3)
  path47 = B.more {t = configure S47.s1} refl (B.more {t = configure S47.s2} refl (B.more {t = configure S47.s3} refl (B.done)))

  path48 : B.Runs (configure S48.s0) S48.actions (configure S48.s3)
  path48 = B.more {t = configure S48.s1} refl (B.more {t = configure S48.s2} refl (B.more {t = configure S48.s3} refl (B.done)))

  path49 : B.Runs (configure S49.s0) S49.actions (configure S49.s3)
  path49 = B.more {t = configure S49.s1} refl (B.more {t = configure S49.s2} refl (B.more {t = configure S49.s3} refl (B.done)))

