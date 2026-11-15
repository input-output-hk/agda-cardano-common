{-# OPTIONS --guardedness #-}

-- Rechecks every original edge under the source 5/120 policy profile.
-- Explicit transformed successors are independently checked by refl.
module ConnectionManagement.SourceInputs.SourcePolicyInbound2 where
open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.InboundConfiguredSupport using (module B)
import ConnectionManagement.SourceInputs.Policy as Policy
configure : B.State → B.State
configure s = record s { runtime = Policy.runtime (B.runtime s) }
import ConnectionManagement.Negative.InboundConfiguredStart3 as S16
import ConnectionManagement.Negative.InboundConfiguredStart4 as S17
import ConnectionManagement.Negative.InboundConfiguredStart5 as S18
import ConnectionManagement.Negative.InboundConfiguredStart6 as S19
import ConnectionManagement.Negative.InboundConfiguredStart7 as S20
import ConnectionManagement.Negative.InboundConfiguredStart8 as S21
import ConnectionManagement.Negative.InboundConfiguredStart9 as S22
import ConnectionManagement.Negative.InboundConfiguredStart10 as S23

abstract
  path16 : B.Runs (configure S16.s0) S16.actions (configure S16.s3)
  path16 = B.more {t = configure S16.s1} refl (B.more {t = configure S16.s2} refl (B.more {t = configure S16.s3} refl (B.done)))

  path17 : B.Runs (configure S17.s0) S17.actions (configure S17.s3)
  path17 = B.more {t = configure S17.s1} refl (B.more {t = configure S17.s2} refl (B.more {t = configure S17.s3} refl (B.done)))

  path18 : B.Runs (configure S18.s0) S18.actions (configure S18.s3)
  path18 = B.more {t = configure S18.s1} refl (B.more {t = configure S18.s2} refl (B.more {t = configure S18.s3} refl (B.done)))

  path19 : B.Runs (configure S19.s0) S19.actions (configure S19.s3)
  path19 = B.more {t = configure S19.s1} refl (B.more {t = configure S19.s2} refl (B.more {t = configure S19.s3} refl (B.done)))

  path20 : B.Runs (configure S20.s0) S20.actions (configure S20.s3)
  path20 = B.more {t = configure S20.s1} refl (B.more {t = configure S20.s2} refl (B.more {t = configure S20.s3} refl (B.done)))

  path21 : B.Runs (configure S21.s0) S21.actions (configure S21.s3)
  path21 = B.more {t = configure S21.s1} refl (B.more {t = configure S21.s2} refl (B.more {t = configure S21.s3} refl (B.done)))

  path22 : B.Runs (configure S22.s0) S22.actions (configure S22.s3)
  path22 = B.more {t = configure S22.s1} refl (B.more {t = configure S22.s2} refl (B.more {t = configure S22.s3} refl (B.done)))

  path23 : B.Runs (configure S23.s0) S23.actions (configure S23.s3)
  path23 = B.more {t = configure S23.s1} refl (B.more {t = configure S23.s2} refl (B.more {t = configure S23.s3} refl (B.done)))

