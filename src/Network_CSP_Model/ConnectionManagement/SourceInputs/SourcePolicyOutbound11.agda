{-# OPTIONS --guardedness #-}

-- Rechecks every original edge under the source 5/120 policy profile.
-- Explicit transformed successors are independently checked by refl.
module ConnectionManagement.SourceInputs.SourcePolicyOutbound11 where
open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.FullConfiguredContractProfile using (module B)
import ConnectionManagement.SourceInputs.Policy as Policy
configure : B.State → B.State
configure s = record s { runtime = Policy.runtime (B.runtime s) }
import ConnectionManagement.Negative.FullConfiguredResult3Body as S18
import ConnectionManagement.Negative.FullConfiguredResult3Select as S19
import ConnectionManagement.Negative.FullConfiguredResult3 as S20
import ConnectionManagement.Negative.FullConfiguredResult4Return as S21
import ConnectionManagement.Negative.FullConfiguredResult4Body as S22
import ConnectionManagement.Negative.FullConfiguredResult4Select as S23
import ConnectionManagement.Negative.FullConfiguredResult4 as S24

abstract
  path18 : B.Runs (configure S18.s0) S18.actions (configure S18.s6)
  path18 = B.more {t = configure S18.s1} refl (B.more {t = configure S18.s2} refl (B.more {t = configure S18.s3} refl (B.more {t = configure S18.s4} refl (B.more {t = configure S18.s5} refl (B.more {t = configure S18.s6} refl (B.done))))))

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

  path24 : B.Runs (configure S24.s0) S24.actions (configure S24.s3)
  path24 = B.more {t = configure S24.s1} refl (B.more {t = configure S24.s2} refl (B.more {t = configure S24.s3} refl (B.done)))

