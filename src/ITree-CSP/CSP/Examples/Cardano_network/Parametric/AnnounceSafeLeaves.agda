{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — THE LEAF `Safe` FACTS: the announcement-free
-- threads, and the ONE-SIDED parallel congruence that the peer bundles
-- and the medium need instead of a `Safe` fact of their own.
--
-- `Parametric.AnnounceSafeCarrier` supplies the coinductive carrier
-- `Safe ms M` and its four congruences but proves no leaf fact.  This
-- module proves the cheap ones.
--
-- THE LEVER.  Exactly one thread of `NodeLogic` ever performs
-- `apiLN … sendLNBlockAnnouncement`, namely `lnServerLoop`.  For every
-- other thread `Safe`'s `gate` is VACUOUS, and — every thread being a
-- `loop0` — its `noTick` is vacuous too.  Both facts are already
-- expressible with machinery the repo owns: `OffersOnly α`
-- (`CSP.Laws.Bisim.DRCongruenceRep`) is a step-closed "offers only α"
-- invariant with closure lemmas for `Prefix`/`Output`/`loop0`, and
-- `NoRet` beside it is a step-closed "never returns" invariant with
-- `NoRet-loop0` PREMISE-FREE.  `quiet→Safe` below turns that pair into a
-- `Safe` fact against ANY minted set, and each thread then costs one
-- line of loop-unrolling.
--
-- TWO LEAVES ARE NOT `Safe`, AND CANNOT BE MADE SO.  The task sketch
-- asked for `Safe ms NetworkLinkBreakableA` and for `Safe` facts about
-- `nodeBundle`'s configured peers.  BOTH ARE FALSE:
--
--   * `gate`.  The LeiosNotify SERVER PEER offers
--     `apiLN l d sendLNBlockAnnouncement` for an ARBITRARY header
--     (`LeiosNotify.agda:215`) — that api event is precisely the
--     rendezvous by which `lnServerLoop` hands the peer the block it
--     took from the store.  A peer bundle in isolation therefore
--     announces unminted blocks, so it is not `Gated` against any `ms`.
--
--   * `noTick`.  `NetCommon.breakableNetLinkA l = netLinkMediumA l △
--     (break l ⟶₀ Skip)` becomes `Skip` once its `break` fires, and
--     `⦀Fin` of ticking cells ticks; the mini-protocol peers likewise
--     terminate on `done`.  Neither is `NoRet`.
--
-- WHAT REPLACES THEM.  Both leaves sit on the LEFT of a `∥⇘ A ⇙` whose
-- RIGHT operand is node logic, and `Safe`'s obligations can all be met
-- from that right operand alone:
--
--   * `gate` — an announcement of the composite is either SYNCHRONISED
--     (then the logic performed it too, and the logic's `gate` answers)
--     or SOLO on the left (excluded: at `∥⇘ apiES ⇙` the announce
--     channel is IN the synchronisation set, and at `∥⇘ ioES ⇙` the
--     medium's own confinement forbids it);
--   * `noTick` — `Par` ticks only when BOTH operands are at `ret`, and
--     the logic never is.
--
-- `safe-ParE` below is that congruence: `Safe` on the RIGHT operand and
-- nothing but `Env` — "never announces an event this `A` does not
-- synchronise" — on the left.  It is what makes the peers and the medium
-- free, and it is strictly more general than `AnnounceSafeCarrier`'s
-- `safe-Par` at the two places the assembly uses it.
------------------------------------------------------------------------

module CSP.Examples.Cardano_network.Parametric.AnnounceSafeLeaves where

open import Level using (0ℓ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Class.DecEq using (DecEq)
import Class.DecEq.Instances as DecEqI

open import Process_Trees using (PTree; ptree; react; AnyTypes; ExtI)
open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Parametric.Topology using (Topology; opposite)
import CSP.Examples.Cardano_network.Net as N
import CSP.Examples.Cardano_network.Data as D
import CSP.Operators as O
import CSP.Examples.Cardano_network.Parametric.NodeLogic as NL
import CSP.Examples.Cardano_network.Parametric.AnnounceSafe as AS
import CSP.Examples.Cardano_network.Parametric.AnnounceInvariant as AI
import CSP.Examples.Cardano_network.Parametric.AnnounceSafeCarrier as ASC

------------------------------------------------------------------------
-- The generic layer
------------------------------------------------------------------------

-- the leaf facts, parametric in the network parameters, the topology and the api
-- alphabet — the same three parameters every other `Parametric.Announce*` module
-- takes, so `Safe`, `nodeLogic` and `ioES` below are literally those modules'
module Generic
  (p : Params) (t : Topology p)
  (apiES : O.EventSet (N.Net_Api-≟ p {D.Payload p})) where

  open Params p using (Block; EB; EBHash; decBlock)
  open N p
    using ( Link; Net_Api; Net_Api-≟; env; envMint; apiLN; store; break
          ; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack; done
          ; apiCS; apiBF; apiTS; apiKA; apiLF
          ; sendLNBlockAnnouncement )
  open D p
    using ( Payload; Point; Header; Tip; ChainRange; header; tip
          ; DecEq-Point; DecEq-Header; DecEq-Tip; DecEq-ChainRange; DecEq-Payload )
  open import CSP.Examples.Cardano_network.Base using (Dir)

  -- product `DecEq` for the `sendCSRollForward` carrier (`Header × Tip`) — the same
  -- instance `NodeLogic` declares, so `OffersOnly-Output` sees the one the `!`-output
  -- in `serverBody-k` was built with
  instance
    DecEq-Header×Tip : DecEq (Header × Tip)
    DecEq-Header×Tip = DecEqI.DecEq-×

  open import CSP.Examples.Cardano_network.NetCommon p
    using (ioES; NetworkLinkBreakableA)
  open Topology t using (Node)
  open O {E = Net_Api Payload} (Net_Api-≟ {Payload})
    using (EventSet; par-brBoth; _∥⇘_⇙_; loop0)
  open import CSP.Examples.Cardano_network.Parametric.Node p t apiES using (Proc)
  open NL.Generic p t apiES
    using (mint; clientLoop; serverLoop; lnClientLoop; clientBody-k; serverBody-k)
  open AS.Generic p t apiES using (Minted)
  open AI.Generic p t apiES
    using (NotMint; Gated; linkEvents; MediumConfined; confined-NetworkLinkBreakableA)
  open ASC.Generic p t apiES using (Safe; HideOK; safe-mono; mintedAfter-⊇; onOther′)
  open Safe
  open import Semantics.LTS
    {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
    using (Label; ev; τ; evl; √; evLabel; _─[_]─►_; sRet)
  open import CSP.Laws.Bisim.DRCongruenceRep (Net_Api-≟ {Payload})
    using ( Alpha; OffersOnly; NoRet
          ; OffersOnly-Skip; OffersOnly-Prefix; OffersOnly-Prefix₀; OffersOnly-Output
          ; OffersOnly-loop0; NoRet-loop0 )
  open import CSP.Laws.Traces.TraceLawsExtChoice (Net_Api-≟ {Payload}) using (NonRet)
  open import CSP.Laws.Traces.TraceLawsParallelElim (Net_Api-≟ {Payload})
    using (Par-τ-elim; τL; τR; Par-ev-elim; evSync; evL; evR; evBoth; ev√)
  open import CSP.Laws.Traces.TraceLawsParallelTrace (Net_Api-≟ {Payload})
    using (brBoth-τ-elim; brBoth-no-ev)

  ------------------------------------------------------------------------
  -- "Never announces", as an alphabet
  ------------------------------------------------------------------------

  -- an alphabet does not contain the Leios block-announcement channel.  This is the
  -- ONE property of a confining alphabet that `Safe`'s `gate` needs.
  NoAnn : Alpha → Set
  NoAnn α = ∀ {l : Link} {d : Dir} (h : Header)
          → α (Header , apiLN l d sendLNBlockAnnouncement) h → ⊥

  -- the largest such alphabet: everything EXCEPT a block announcement.  A process
  -- confined to it can be read off its syntax by `OffersOnly`'s closure lemmas.
  notAnn : Alpha
  notAnn (_ , apiLN _ _ sendLNBlockAnnouncement) _ = ⊥
  notAnn _                                      _ = ⊤ {0ℓ}

  ------------------------------------------------------------------------
  -- The generic leaf lemma
  ------------------------------------------------------------------------

  -- a process that never returns cannot TICK: a `√` step is exactly a `ret` node
  noRet→noTick : ∀ {M M′ : Proc} {x : ⊤ {0ℓ}}
               → NoRet M → M ─[ ev (√ x) ]─► M′ → ⊥
  noRet→noTick nr (sRet eq) = subst NonRet eq (NoRet.nowNR nr)

  -- THE LEVER OF THIS MODULE: a process that never announces and never returns is
  -- `Safe` against ANY minted set.  `gate` is refuted by the confining alphabet,
  -- `noTick` by non-termination, and the three step fields all corecurse on the two
  -- invariants' own step-closure — so a leaf costs exactly one `OffersOnly` and one
  -- `NoRet` witness, both of which the repo's closure lemmas already build.
  quiet→Safe : ∀ {α : Alpha} {ms : Minted} {M : Proc}
             → NoAnn α → OffersOnly α M → NoRet M → Safe ms M
  quiet→Safe na oo nr .gate st       = ⊥-elim (na _ (OffersOnly.now oo st))
  quiet→Safe na oo nr .onτ st        = quiet→Safe na (OffersOnly.step oo st) (NoRet.stepNR nr st)
  quiet→Safe na oo nr .onMint st     = quiet→Safe na (OffersOnly.step oo st) (NoRet.stepNR nr st)
  quiet→Safe na oo nr .onOther nm st = quiet→Safe na (OffersOnly.step oo st) (NoRet.stepNR nr st)
  quiet→Safe na oo nr .noTick st     = noRet→noTick nr st

  -- the shape every thread below instantiates: a `loop0` whose body is
  -- announcement-free.  `α` is given EXPLICITLY: `NoAnn` is a definition, not a
  -- datatype, so leaving it to unification poses a higher-order problem and strands
  -- the alphabet as an unsolved meta.  The `NoAnn notAnn` witness is `λ _ x → x`,
  -- `notAnn`'s announcement clause being `⊥` outright.
  quietLoop→Safe : ∀ {ms : Minted} {body : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})}
                 → OffersOnly notAnn body → Safe ms (loop0 body)
  quietLoop→Safe oob = quiet→Safe {α = notAnn} (λ _ x → x) (OffersOnly-loop0 oob) NoRet-loop0

  ------------------------------------------------------------------------
  -- The announcement-free threads
  --
  -- Each is `loop0 body` with `body` a chain of `⟶` / `!⟶` prefixes over channels
  -- OTHER than `apiLN … sendLNBlockAnnouncement`, so `notAnn` holds at every offer by
  -- reduction and the whole discharge is `OffersOnly-Prefix`/`-Output` plumbing.
  ------------------------------------------------------------------------

  -- the mint thread offers only `env … envMint`
  safe-mint : ∀ {ms} (n : Node) → Safe ms (mint n)
  safe-mint n = quietLoop→Safe (OffersOnly-Prefix₀ (λ _ → tt) OffersOnly-Skip)

  -- the client thread offers only `apiCS`, `apiBF` and the store's `stPut`
  safe-clientLoop : ∀ {ms} (n : Node) (ld : Link × Dir) → Safe ms (clientLoop n ld)
  safe-clientLoop n (l , d) =
    quietLoop→Safe (OffersOnly-Prefix₀ (λ _ → tt) (OffersOnly-Prefix (λ _ → tt) k))
    where
    -- the RollForward continuation: request the range, receive the block, store it
    k : ∀ a → OffersOnly notAnn (clientBody-k n l d a)
    k (header b , _) =
      OffersOnly-Output tt
        (OffersOnly-Prefix (λ _ → tt) (λ _ → OffersOnly-Output tt OffersOnly-Skip))

  -- the server thread offers only `apiCS`, `apiBF` and the store's `stGet`
  safe-serverLoop : ∀ {ms} (n : Node) (ld : Link × Dir) → Safe ms (serverLoop n ld)
  safe-serverLoop n (l , d) =
    quietLoop→Safe (OffersOnly-Prefix₀ (λ _ → tt) (OffersOnly-Prefix (λ _ → tt) k))
    where
    -- the tail of a server round, on the block the store handed over
    k : ∀ b → OffersOnly notAnn (serverBody-k n l (opposite d) b)
    k b = OffersOnly-Prefix₀ (λ _ → tt)
            (OffersOnly-Output tt
              (OffersOnly-Prefix (λ _ → tt) (λ _ →
                OffersOnly-Prefix₀ (λ _ → tt)
                  (OffersOnly-Output tt (OffersOnly-Prefix₀ (λ _ → tt) OffersOnly-Skip)))))

  -- the LN client thread offers only `sendLNRequestNext` / `recvLNBlockAnnouncement`,
  -- neither of which is the SEND side of an announcement
  safe-lnClientLoop : ∀ {ms} (ld : Link × Dir) → Safe ms (lnClientLoop ld)
  safe-lnClientLoop (l , d) =
    quietLoop→Safe
      (OffersOnly-Prefix₀ (λ _ → tt) (OffersOnly-Prefix (λ _ → tt) (λ _ → OffersOnly-Skip)))

  ------------------------------------------------------------------------
  -- The hiding side condition
  ------------------------------------------------------------------------

  -- STEP DISCHARGED: `∖ ioES` hides only `input`/`output`, and a mint rides `env`, so
  -- no hidden event is a mint and `safe-Hide` applies to the system's own hiding.
  -- One clause per `Net_Api` constructor, because `ioSet` does not reduce until the
  -- constructor is known; the sixteen non-io channels are refuted by their `ioSet`
  -- membership being `⊥`.
  HideOK-ioES : HideOK ioES
  HideOK-ioES {e = input  _ _ _} _  = tt
  HideOK-ioES {e = output _ _ _} _  = tt
  HideOK-ioES {e = sndmsg _ _ _} ()
  HideOK-ioES {e = rcvmsg _ _ _} ()
  HideOK-ioES {e = tx     _ _ _} ()
  HideOK-ioES {e = sndack _ _ _} ()
  HideOK-ioES {e = rcvack _ _ _} ()
  HideOK-ioES {e = ack    _ _ _} ()
  HideOK-ioES {e = done   _ _ _} ()
  HideOK-ioES {e = apiCS  _ _ _} ()
  HideOK-ioES {e = apiBF  _ _ _} ()
  HideOK-ioES {e = apiTS  _ _ _} ()
  HideOK-ioES {e = apiKA  _ _ _} ()
  HideOK-ioES {e = apiLN  _ _ _} ()
  HideOK-ioES {e = apiLF  _ _ _} ()
  HideOK-ioES {e = store  _ _ _} ()
  HideOK-ioES {e = env    _ _ _} ()
  HideOK-ioES {e = break  _}     ()

  ------------------------------------------------------------------------
  -- The environment operand, and the ONE-SIDED parallel congruence
  ------------------------------------------------------------------------

  -- `Env A P`: `P` never performs a block announcement that `A` leaves UNSYNCHRONISED
  -- — now or after any step.  This is everything `safe-ParE` needs of a left operand,
  -- and it is satisfiable by a peer bundle (which announces, but only in step with the
  -- logic) and by the breakable medium (which never announces at all), neither of
  -- which is `Safe`.
  record Env (A : EventSet) (P : Proc) : Set₁ where
    coinductive
    field
      noSolo : ∀ {l d b P′}
             → (EventSet.mem A (Header , apiLN l d sendLNBlockAnnouncement) (header b) → ⊥)
             → P ─[ ev (evl (evLabel Header (apiLN l d sendLNBlockAnnouncement) (header b))) ]─► P′
             → ⊥
      stepE  : ∀ {l : Label (⊤ {0ℓ})} {P′} → P ─[ l ]─► P′ → Env A P′
  open Env

  -- `A` SYNCHRONISES the announcement channel: then no operand can announce solo, and
  -- the left operand is unconstrained.  This is the node level (`∥⇘ apiES ⇙`).
  AnnSync : EventSet → Set
  AnnSync A = ∀ {l : Link} {d : Dir} (h : Header)
            → EventSet.mem A (Header , apiLN l d sendLNBlockAnnouncement) h

  -- a synchronised announcement channel makes EVERY process an `Env`
  env-sync : ∀ {A P} → AnnSync A → Env A P
  env-sync ann .noSolo ¬m st = ¬m (ann _)
  env-sync ann .stepE  st    = env-sync ann

  -- …and so does an alphabet confinement that excludes announcements outright.  This
  -- is the medium level (`∥⇘ ioES ⇙`), where the announce channel is NOT synchronised.
  env-oo : ∀ {α A P} → NoAnn α → OffersOnly α P → Env A P
  env-oo na oo .noSolo ¬m st = na _ (OffersOnly.now oo st)
  env-oo na oo .stepE  st    = env-oo na (OffersOnly.step oo st)

  -- THE DEFAULT MEDIUM AS AN ENVIRONMENT, for any synchronisation set.  `classify`
  -- sends every `apiLN` to `nothing`, so a confined medium can never announce — the
  -- same one-line argument as `AnnounceInvariant.confined-noAnnounce`.  Note the
  -- medium is NOT `Safe`: once every link's `break` has fired it is `Skip`, which
  -- ticks, and `Safe`'s `noTick` is then false.
  env-medium : ∀ (A : EventSet) → Env A NetworkLinkBreakableA
  env-medium A = env-oo {α = linkEvents} (λ h ne → ne refl) confined-NetworkLinkBreakableA

  -- THE ONE-SIDED PARALLEL CONGRUENCE, and its collision companion, mutually
  -- corecursive — the shape of `AnnounceSafeCarrier.safe-Par`/`safe-both`, but with
  -- `Safe` demanded of the RIGHT operand only.
  safe-ParE  : ∀ {ms} (A : EventSet) {P Q} → Env A P → Safe ms Q → Safe ms (P ∥⇘ A ⇙ Q)
  safe-bothE : ∀ {ms} (A : EventSet) {P Q P′ Q′}
             → Env A P → Env A P′ → Safe ms Q → Safe ms Q′
             → Safe ms (ptree (react (λ _ _ → nothing)
                               (par-brBoth A (λ _ _ → tt) P Q P′ Q′)))

  -- an announcement of the composite is either synchronised — and then the LOGIC
  -- announced it, so its `gate` answers — or solo on the left, which `Env` forbids
  safe-ParE A {P = P} {Q = Q} e s .gate st with Par-ev-elim A (λ _ _ → tt) P Q st
  ... | evSync _  _   stQ = gate s stQ
  ... | evL    ¬m stP     = ⊥-elim (noSolo e ¬m stP)
  ... | evR    _  stQ     = gate s stQ
  ... | evBoth ¬m stP _   = ⊥-elim (noSolo e ¬m stP)
  -- a τ of the composite is a τ of one operand; the other is untouched
  safe-ParE A {P = P} {Q = Q} e s .onτ st with Par-τ-elim A (λ _ _ → tt) P Q st
  ... | τL P′ stP refl    = safe-ParE A (stepE e stP) s
  ... | τR Q′ stQ refl    = safe-ParE A e (onτ s stQ)
  -- a mint: the right operand moves to the grown set if it took part, and is carried
  -- across by `safe-mono` if the left operand minted alone
  safe-ParE A {P = P} {Q = Q} e s .onMint {mb = mb} st
    with Par-ev-elim A (λ _ _ → tt) P Q st
  ... | evSync _ stP stQ  = safe-ParE A (stepE e stP) (onMint s stQ)
  ... | evL    _ stP      = safe-ParE A (stepE e stP) (safe-mono (mintedAfter-⊇ mb) s)
  ... | evR    _ stQ      = safe-ParE A e (onMint s stQ)
  ... | evBoth _ stP stQ  = safe-bothE A e (stepE e stP)
                                         (safe-mono (mintedAfter-⊇ mb) s) (onMint s stQ)
  -- every other label, by the same inversions; a `√` needs BOTH operands at `ret`, so
  -- the right operand's `noTick` alone refutes it
  safe-ParE A {P = P} {Q = Q} e s .onOther {a = τ} nm st
    with Par-τ-elim A (λ _ _ → tt) P Q st
  ... | τL P′ stP refl    = safe-ParE A (stepE e stP) s
  ... | τR Q′ stQ refl    = safe-ParE A e (onτ s stQ)
  safe-ParE A {P = P} {Q = Q} e s .onOther {a = ev (evl _)} nm st
    with Par-ev-elim A (λ _ _ → tt) P Q st
  ... | evSync _ stP stQ  = safe-ParE A (stepE e stP) (onOther′ s stQ nm)
  ... | evL    _ stP      = safe-ParE A (stepE e stP) s
  ... | evR    _ stQ      = safe-ParE A e (onOther′ s stQ nm)
  ... | evBoth _ stP stQ  = safe-bothE A e (stepE e stP) s (onOther′ s stQ nm)
  safe-ParE A {P = P} {Q = Q} e s .onOther {a = ev (√ _)} nm st
    with Par-ev-elim A (λ _ _ → tt) P Q st
  ... | ev√ _ fpQ         = ⊥-elim (noTick s (sRet fpQ))
  safe-ParE A {P = P} {Q = Q} e s .noTick st with Par-ev-elim A (λ _ _ → tt) P Q st
  ... | ev√ _ fpQ         = noTick s (sRet fpQ)

  -- the collision node offers no visible event at all, so only its two committing τ's
  -- have content — and each lands back in `safe-ParE`
  safe-bothE A {P = P} {Q = Q} {P′ = P′} {Q′ = Q′} eP eP′ sQ sQ′ .gate st =
    ⊥-elim (brBoth-no-ev A (λ _ _ → tt) P Q P′ Q′ st)
  safe-bothE A {P = P} {Q = Q} {P′ = P′} {Q′ = Q′} eP eP′ sQ sQ′ .onτ st
    with brBoth-τ-elim A (λ _ _ → tt) P Q P′ Q′ st
  ... | inj₁ refl = safe-ParE A eP′ sQ
  ... | inj₂ refl = safe-ParE A eP sQ′
  safe-bothE A {P = P} {Q = Q} {P′ = P′} {Q′ = Q′} eP eP′ sQ sQ′ .onMint st =
    ⊥-elim (brBoth-no-ev A (λ _ _ → tt) P Q P′ Q′ st)
  safe-bothE A {P = P} {Q = Q} {P′ = P′} {Q′ = Q′} eP eP′ sQ sQ′ .onOther {a = τ} nm st
    with brBoth-τ-elim A (λ _ _ → tt) P Q P′ Q′ st
  ... | inj₁ refl = safe-ParE A eP′ sQ
  ... | inj₂ refl = safe-ParE A eP sQ′
  safe-bothE A {P = P} {Q = Q} {P′ = P′} {Q′ = Q′} eP eP′ sQ sQ′ .onOther {a = ev _} nm st =
    ⊥-elim (brBoth-no-ev A (λ _ _ → tt) P Q P′ Q′ st)
  safe-bothE A {P = P} {Q = Q} {P′ = P′} {Q′ = Q′} eP eP′ sQ sQ′ .noTick st =
    brBoth-no-ev A (λ _ _ → tt) P Q P′ Q′ st

------------------------------------------------------------------------
-- The api alphabet really does synchronise the announcement channel
--
-- `apiES` is a module PARAMETER above, so `AnnSync` cannot be discharged
-- inside `Generic`.  It is discharged here for the shared
-- `ApiAlphabet.apiES`, which is what every non-diamond scenario passes.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.ApiAlphabet using (apiES)

-- `apiSet` answers `⊤` on every `apiLN` channel, so the announce event is
-- synchronised at every node's `∥⇘ apiES ⇙` and `env-sync` applies there
annSync-apiES : ∀ (p : Params) (t : Topology p)
              → Generic.AnnSync p t (apiES p) (apiES p)
annSync-apiES p t h = tt
