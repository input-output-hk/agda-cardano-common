{-# OPTIONS --guardedness #-}

-- Rechecks every original edge under the source 5/120 policy profile.
-- Explicit transformed successors are independently checked by refl.
module ConnectionManagement.SourceInputs.SourcePolicyInbound9 where
open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.InboundConfiguredSupport using (module B)
import ConnectionManagement.SourceInputs.Policy as Policy
configure : B.State → B.State
configure s = record s { runtime = Policy.runtime (B.runtime s) }
import ConnectionManagement.Negative.InboundConfiguredMux7 as S75
import ConnectionManagement.Negative.InboundConfiguredMux8 as S76
import ConnectionManagement.Negative.InboundConfiguredCleanup0 as S77
import ConnectionManagement.Negative.InboundConfiguredCleanup1 as S78
import ConnectionManagement.Negative.InboundConfiguredCleanup2 as S79
import ConnectionManagement.Negative.InboundConfiguredCleanup3 as S80
import ConnectionManagement.Negative.InboundConfiguredCleanup4 as S81
import ConnectionManagement.Negative.InboundConfiguredCleanup5 as S82

abstract
  path75 : B.Runs (configure S75.s0) S75.actions (configure S75.s3)
  path75 = B.more {t = configure S75.s1} refl (B.more {t = configure S75.s2} refl (B.more {t = configure S75.s3} refl (B.done)))

  path76 : B.Runs (configure S76.s0) S76.actions (configure S76.s3)
  path76 = B.more {t = configure S76.s1} refl (B.more {t = configure S76.s2} refl (B.more {t = configure S76.s3} refl (B.done)))

  path77 : B.Runs (configure S77.s0) S77.actions (configure S77.s3)
  path77 = B.more {t = configure S77.s1} refl (B.more {t = configure S77.s2} refl (B.more {t = configure S77.s3} refl (B.done)))

  path78 : B.Runs (configure S78.s0) S78.actions (configure S78.s3)
  path78 = B.more {t = configure S78.s1} refl (B.more {t = configure S78.s2} refl (B.more {t = configure S78.s3} refl (B.done)))

  path79 : B.Runs (configure S79.s0) S79.actions (configure S79.s3)
  path79 = B.more {t = configure S79.s1} refl (B.more {t = configure S79.s2} refl (B.more {t = configure S79.s3} refl (B.done)))

  path80 : B.Runs (configure S80.s0) S80.actions (configure S80.s3)
  path80 = B.more {t = configure S80.s1} refl (B.more {t = configure S80.s2} refl (B.more {t = configure S80.s3} refl (B.done)))

  path81 : B.Runs (configure S81.s0) S81.actions (configure S81.s3)
  path81 = B.more {t = configure S81.s1} refl (B.more {t = configure S81.s2} refl (B.more {t = configure S81.s3} refl (B.done)))

  path82 : B.Runs (configure S82.s0) S82.actions (configure S82.s3)
  path82 = B.more {t = configure S82.s1} refl (B.more {t = configure S82.s2} refl (B.more {t = configure S82.s3} refl (B.done)))

