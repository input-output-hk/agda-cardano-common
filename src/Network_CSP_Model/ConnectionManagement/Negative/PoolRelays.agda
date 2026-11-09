{-# OPTIONS --guardedness #-}

-- Controls for the pool relays scope (network 2f1c154, Diffusion.hs
-- withPoolRelays). The owner cancels and joins the relays thread only after
-- the inner callback has returned; a plain node has no relays thread; the
-- thread body cannot return normally; an exited thread is only waited for.
module ConnectionManagement.Negative.PoolRelays where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Rules.PoolRelays

module Rules where
  scheduled plain : State
  scheduled = initial true
  plain = initial false

  -- Normal close of a scheduled node, after the inner callback returned.
  c1 : step true requestCancel scheduled ≡ just (relaysState (just cancelRequested) cancelling)
  c1 = refl
  c2 : step true (threadAct deliverCancel) (relaysState (just cancelRequested) cancelling) ≡
    just (relaysState (just cancelDelivered) cancelling)
  c2 = refl
  c3 : step true (threadAct bodyExit) (relaysState (just cancelDelivered) cancelling) ≡
    just (relaysState (just bodyExited) cancelling)
  c3 = refl
  c4 : step true (threadAct publishResult) (relaysState (just bodyExited) cancelling) ≡
    just (relaysState (just resultAvailable) cancelling)
  c4 = refl
  c5 : step true (threadAct join) (relaysState (just resultAvailable) cancelling) ≡
    just (relaysState (just joined) cancelling)
  c5 = refl
  c6 : step true finish (relaysState (just joined) cancelling) ≡ just (relaysState (just joined) finished)
  c6 = refl

  -- Cancellation waits for the inner return; the owner waits for the join.
  cancel-before-return-refused : step false requestCancel scheduled ≡ nothing
  cancel-before-return-refused = refl
  finish-before-join-refused : step true finish (relaysState (just cancelDelivered) cancelling) ≡ nothing
  finish-before-join-refused = refl
  finish-without-cancel-refused : step true finish scheduled ≡ nothing
  finish-without-cancel-refused = refl
  join-without-cancel-refused : step true (threadAct join) (relaysState (just resultAvailable) inside) ≡ nothing
  join-without-cancel-refused = refl
  -- The body is m Void: no normal exit while running.
  no-normal-exit : step true (threadAct bodyExit) scheduled ≡ nothing
  no-normal-exit = refl

  -- An early relays failure (seen by waitAny) exits before the owner cancels;
  -- the later cancel is only waited for, with nothing left to deliver.
  f1 : step false (threadAct beginFailure) scheduled ≡ just (relaysState (just bodyUnwinding) inside)
  f1 = refl
  f2 : step false (threadAct bodyExit) (relaysState (just bodyUnwinding) inside) ≡
    just (relaysState (just bodyExited) inside)
  f2 = refl
  f3 : step false (threadAct publishResult) (relaysState (just bodyExited) inside) ≡
    just (relaysState (just resultAvailable) inside)
  f3 = refl
  late-cancel-keeps-result : step true requestCancel (relaysState (just resultAvailable) inside) ≡
    just (relaysState (just resultAvailable) cancelling)
  late-cancel-keeps-result = refl
  nothing-to-deliver : step true (threadAct deliverCancel) (relaysState (just resultAvailable) cancelling) ≡ nothing
  nothing-to-deliver = refl

  -- A plain node: no thread, and the owner returns once the inner callback has.
  plain-finish : step true finish plain ≡ just (relaysState nothing finished)
  plain-finish = refl
  plain-finish-before-return-refused : step false finish plain ≡ nothing
  plain-finish-before-return-refused = refl
  plain-no-cancel : step true requestCancel plain ≡ nothing
  plain-no-cancel = refl
  plain-no-thread : ∀ ret a → step ret (threadAct a) plain ≡ nothing
  plain-no-thread ret a = refl
  finished-terminal : ∀ ret a t → step ret a (relaysState t finished) ≡ nothing
  finished-terminal ret a t = refl

-- Initialized: the accepted server-return run, lifted inside the relays scope
-- of a scheduled node, then the relays cancellation, join and owner return.
module Initialized where
  open import ConnectionManagement.Negative.ServerPeers using (module Protocols)
  import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
  import ConnectionManagement.Negative.GovernorPool as Prior
  import ConnectionManagement.ServerPeersRelays as Relays
  import ConnectionManagement.Properties.PoolRelays as Proof
  module Done = Protocols.StartTrace.ScopedCM.Completion
  module X = Relays.Protocols I.bearerClosed Prior.classify Protocols.capability
  module Cert = Proof.Certified X.V.advance X.runtimeReturned

  lift : ∀ {i as i′} t → X.V.Runs i as i′ →
    X.Executes (X.outer i (relaysState t inside)) (map X.innerAct as) (X.outer i′ (relaysState t inside))
  lift t X.V.stop = X.done
  lift t (X.V.more {s = i} {a = a} eq rest) = X.next (Cert.lift-inner a i t eq) (lift t rest)

  returnedAtFinish : X.runtimeReturned Done.serverFinished ≡ true
  returnedAtFinish = Relays.returned-of I.bearerClosed Prior.classify (X.V.base Done.serverFinished) Done.actual-server-return

  closeActions : List X.OuterAction
  closeActions = X.relaysAct requestCancel ∷ X.relaysAct (threadAct deliverCancel) ∷
    X.relaysAct (threadAct bodyExit) ∷ X.relaysAct (threadAct publishResult) ∷
    X.relaysAct (threadAct join) ∷ X.relaysAct finish ∷ []
  closed : X.Outer
  closed = X.outer Done.serverFinished (relaysState (just joined) finished)
  up : ∀ a r {r′} → step true a r ≡ just r′ →
    X.outerStep (X.relaysAct a) (X.outer Done.serverFinished r) ≡ just (X.outer Done.serverFinished r′)
  up a r = Cert.lift-relays a Done.serverFinished r returnedAtFinish
  closePath : X.Executes (X.outer Done.serverFinished (initial true)) closeActions closed
  closePath = X.next (up requestCancel (initial true) Rules.c1)
    (X.next (up (threadAct deliverCancel) (relaysState (just cancelRequested) cancelling) Rules.c2) (X.next (up (threadAct bodyExit) (relaysState (just cancelDelivered) cancelling) Rules.c3)
    (X.next (up (threadAct publishResult) (relaysState (just bodyExited) cancelling) Rules.c4) (X.next (up (threadAct join) (relaysState (just resultAvailable) cancelling) Rules.c5)
    (X.next (up finish (relaysState (just joined) cancelling) Rules.c6) X.done)))))

  abstract
    initialized-relays-close : X.Executes (X.outer Protocols.initial (initial true))
      (map X.innerAct Done.allFinishedActions ++ closeActions) closed
    initialized-relays-close = Cert.append (lift (just running) Done.initialized-server-finish) closePath

  -- The general certificate applied to this run.
  certified : X.runtimeReturned Done.serverFinished ≡ true ×
    (just joined ≡ nothing ⊎ just {A = ThreadPhase} joined ≡ just joined)
  certified = Cert.from-initial Protocols.initial true initialized-relays-close

  -- Inner steps stop once the owner is cancelling, and cancellation before
  -- the inner return is refused at every runtime state.
  inner-frozen : ∀ i a t → X.outerStep (X.innerAct a) (X.outer i (relaysState t cancelling)) ≡ nothing
  inner-frozen i a t = refl
  cancel-before-return-refused : ∀ i → X.runtimeReturned i ≡ false →
    X.outerStep (X.relaysAct requestCancel) (X.outer i (initial true)) ≡ nothing
  cancel-before-return-refused i eq rewrite eq = refl
