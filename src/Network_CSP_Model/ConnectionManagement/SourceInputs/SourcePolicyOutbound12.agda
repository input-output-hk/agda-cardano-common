{-# OPTIONS --guardedness #-}

-- Rechecks every original edge under the source 5/120 policy profile.
-- Explicit transformed successors are independently checked by refl.
module ConnectionManagement.SourceInputs.SourcePolicyOutbound12 where
open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.FullConfiguredContractProfile using (module B)
import ConnectionManagement.SourceInputs.Policy as Policy
configure : B.State → B.State
configure s = record s { runtime = Policy.runtime (B.runtime s) }
import ConnectionManagement.Negative.FullConfiguredResult18Return as S25
import ConnectionManagement.Negative.FullConfiguredResult18BodyPart0 as S26
import ConnectionManagement.Negative.FullConfiguredResult18BodyPart1 as S27
import ConnectionManagement.Negative.FullConfiguredResult18Body as S28
import ConnectionManagement.Negative.FullConfiguredResult18SelectBudget0 as S29
import ConnectionManagement.Negative.FullConfiguredResult18Select as S30
import ConnectionManagement.Negative.FullConfiguredResult18Budget0 as S31
import ConnectionManagement.Negative.FullConfiguredResult18 as S32
import ConnectionManagement.Negative.FullConfiguredResult19ReturnBudget0 as S33
import ConnectionManagement.Negative.FullConfiguredResult19Return as S34
import ConnectionManagement.Negative.FullConfiguredResult19BodyPart0 as S35
import ConnectionManagement.Negative.FullConfiguredResult19BodyPart1 as S36
import ConnectionManagement.Negative.FullConfiguredResult19Body as S37
import ConnectionManagement.Negative.FullConfiguredResult19SelectBudget0Edge0 as S38
import ConnectionManagement.Negative.FullConfiguredResult19SelectBudget0 as S39
import ConnectionManagement.Negative.FullConfiguredResult19Select as S40
import ConnectionManagement.Negative.FullConfiguredResult19Budget0Edge0 as S41
import ConnectionManagement.Negative.FullConfiguredResult19Budget0 as S42
import ConnectionManagement.Negative.FullConfiguredResult19 as S43
import ConnectionManagement.Negative.FullConfiguredWarmBudget0Edge0 as S44

abstract
  path25 : B.Runs (configure S25.s0) S25.actions (configure S25.s3)
  path25 = B.more {t = configure S25.s1} refl (B.more {t = configure S25.s2} refl (B.more {t = configure S25.s3} refl (B.done)))

  path26 : B.Runs (configure S26.s0) S26.actions (configure S26.s1)
  path26 = B.more {t = configure S26.s1} refl (B.done)

  path27 : B.Runs (configure S27.s0) S27.actions (configure S27.s1)
  path27 = B.more {t = configure S27.s1} refl (B.done)

  path28 : B.Runs (configure S28.s0) S28.actions (configure S28.s1)
  path28 = B.more {t = configure S28.s1} refl (B.done)

  path29 : B.Runs (configure S29.s0) S29.actions (configure S29.s2)
  path29 = B.more {t = configure S29.s1} refl (B.more {t = configure S29.s2} refl (B.done))

  path30 : B.Runs (configure S30.s0) S30.actions (configure S30.s1)
  path30 = B.more {t = configure S30.s1} refl (B.done)

  path31 : B.Runs (configure S31.s0) S31.actions (configure S31.s2)
  path31 = B.more {t = configure S31.s1} refl (B.more {t = configure S31.s2} refl (B.done))

  path32 : B.Runs (configure S32.s0) S32.actions (configure S32.s1)
  path32 = B.more {t = configure S32.s1} refl (B.done)

  path33 : B.Runs (configure S33.s0) S33.actions (configure S33.s2)
  path33 = B.more {t = configure S33.s1} refl (B.more {t = configure S33.s2} refl (B.done))

  path34 : B.Runs (configure S34.s0) S34.actions (configure S34.s1)
  path34 = B.more {t = configure S34.s1} refl (B.done)

  path35 : B.Runs (configure S35.s0) S35.actions (configure S35.s1)
  path35 = B.more {t = configure S35.s1} refl (B.done)

  path36 : B.Runs (configure S36.s0) S36.actions (configure S36.s1)
  path36 = B.more {t = configure S36.s1} refl (B.done)

  path37 : B.Runs (configure S37.s0) S37.actions (configure S37.s1)
  path37 = B.more {t = configure S37.s1} refl (B.done)

  path38 : B.Runs (configure S38.s0) S38.actions (configure S38.s1)
  path38 = B.more {t = configure S38.s1} refl (B.done)

  path39 : B.Runs (configure S39.s0) S39.actions (configure S39.s1)
  path39 = B.more {t = configure S39.s1} refl (B.done)

  path40 : B.Runs (configure S40.s0) S40.actions (configure S40.s1)
  path40 = B.more {t = configure S40.s1} refl (B.done)

  path41 : B.Runs (configure S41.s0) S41.actions (configure S41.s1)
  path41 = B.more {t = configure S41.s1} refl (B.done)

  path42 : B.Runs (configure S42.s0) S42.actions (configure S42.s1)
  path42 = B.more {t = configure S42.s1} refl (B.done)

  path43 : B.Runs (configure S43.s0) S43.actions (configure S43.s1)
  path43 = B.more {t = configure S43.s1} refl (B.done)

  path44 : B.Runs (configure S44.s0) S44.actions (configure S44.s1)
  path44 = B.more {t = configure S44.s1} refl (B.done)

