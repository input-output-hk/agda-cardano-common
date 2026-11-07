{-# OPTIONS --guardedness #-}

-- The bounded pipelined Notify replay language against the lookahead wire languages:
-- bounded ⊆ lookahead (server under genericNext, client), and the failures of every converse.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.BoundedRelation where

open import Data.Bool using (true; false; T)
open import Data.List using (List; []; _∷_; replicate)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _<_; _+_; _<ᵇ_)
open import Data.Nat.Properties using (<ᵇ⇒<; <-irrefl; +-suc; +-identityʳ)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
open import Cardano_network.Data exactParams using (header)
import Cardano_network.Replay.LeiosNotifySession as Log
open Log using (Send; Recv; server; client)
import Cardano_network.Replay.LeiosNotifyPipeline as Pipeline
open Pipeline using (St; openN; quitting; closed; issue; nextKind)
import Cardano_network.LeiosNotifyPipe exactParams as Payloads
import Cardano_network.LeiosNotifyPipeLookahead.Model Payloads.Notification as S
open S using (genericNext; nodeNext; normal; canceled)
import Cardano_network.LeiosNotifyPipeLookahead.Wire.Server Payloads.Notification as SW
import Cardano_network.LeiosNotifyPipeLookahead.Wire.Client Payloads.Notification as CW
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ServerAdapter as Server
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ClientAdapter as Client

-- Fixture announcement header (the exact-payload fixture of Wire/ServerAdapterTests).
h : Log.Announcement
h = just (17 , 23 , 31)

-- The notification the existing decoders produce for `BlockAnnouncement h`.
a : Payloads.Notification
a = Payloads.announcement (header h)

-- Keep a decoded row only when the rest of the list also decoded.
_∷?_ : ∀ {W : Set} → Maybe W → Maybe (List W) → Maybe (List W)
just w ∷? just ws = just (w ∷ ws)
just _ ∷? nothing = nothing
nothing ∷? _ = nothing

-- Server-role rows through the existing per-event server decoder (Task 3's translation).
serverWires : List Log.E → Maybe (List SW.Wire)
serverWires [] = just []
serverWires (e ∷ es) = Server.decode e ∷? serverWires es

-- Client-role rows through the existing per-event client decoder.
clientWires : List Log.E → Maybe (List CW.Wire)
clientWires [] = just []
clientWires (e ∷ es) = Client.decode e ∷? clientWires es

-- Bounded states read as lookahead server states: openN ↦ Open, quitting ↦ QuitSeen.
toServer : St → SW.State
toServer (openN n) = SW.Open n
toServer (quitting n) = SW.QuitSeen n
toServer closed = SW.Closed

-- Bounded states read as lookahead client states.
toClient : St → CW.State
toClient (openN n) = CW.Open n
toClient (quitting n) = CW.QuitSeen n
toClient closed = CW.Closed

-- A granted request credit is below the bound and increments the outstanding count.
issue-just : ∀ depth n {t} → issue depth n ≡ just t → n < depth × t ≡ openN (suc n)
issue-just depth n p with n <ᵇ depth in lt
issue-just depth n refl | true = <ᵇ⇒< n depth (subst T (sym lt) tt) , refl
issue-just depth n () | false

-- Each bounded server transition is a genericNext lookahead step on the decoded row.
serverStep : ∀ depth s e {t} → nextKind depth server s (Log.forget e) ≡ just t →
  Σ[ w ∈ SW.Wire ] (Server.decode e ≡ just w × SW.Step genericNext (toServer s) w (toServer t))
serverStep d (openN n) (Recv , Log.RequestNext) p with issue-just d n p
... | _ , refl = _ , refl , SW.receiveRequest
serverStep d (quitting zero) (Recv , Log.RequestNext) ()
serverStep d (quitting (suc n)) (Recv , Log.RequestNext) ()
serverStep d closed (Recv , Log.RequestNext) ()
serverStep d (openN zero) (Recv , Log.BlockAnnouncement _) ()
serverStep d (openN (suc n)) (Recv , Log.BlockAnnouncement _) ()
serverStep d (quitting zero) (Recv , Log.BlockAnnouncement _) ()
serverStep d (quitting (suc n)) (Recv , Log.BlockAnnouncement _) ()
serverStep d closed (Recv , Log.BlockAnnouncement _) ()
serverStep d (openN zero) (Recv , Log.BlockOffer _ _ _) ()
serverStep d (openN (suc n)) (Recv , Log.BlockOffer _ _ _) ()
serverStep d (quitting zero) (Recv , Log.BlockOffer _ _ _) ()
serverStep d (quitting (suc n)) (Recv , Log.BlockOffer _ _ _) ()
serverStep d closed (Recv , Log.BlockOffer _ _ _) ()
serverStep d (openN zero) (Recv , Log.BlockTxsOffer _ _) ()
serverStep d (openN (suc n)) (Recv , Log.BlockTxsOffer _ _) ()
serverStep d (quitting zero) (Recv , Log.BlockTxsOffer _ _) ()
serverStep d (quitting (suc n)) (Recv , Log.BlockTxsOffer _ _) ()
serverStep d closed (Recv , Log.BlockTxsOffer _ _) ()
serverStep d (openN zero) (Recv , Log.Votes _) ()
serverStep d (openN (suc n)) (Recv , Log.Votes _) ()
serverStep d (quitting zero) (Recv , Log.Votes _) ()
serverStep d (quitting (suc n)) (Recv , Log.Votes _) ()
serverStep d closed (Recv , Log.Votes _) ()
serverStep d (openN n) (Recv , Log.Quit) refl = _ , refl , SW.receiveQuit
serverStep d (quitting zero) (Recv , Log.Quit) ()
serverStep d (quitting (suc n)) (Recv , Log.Quit) ()
serverStep d closed (Recv , Log.Quit) ()
serverStep d (openN zero) (Recv , Log.Canceled) ()
serverStep d (openN (suc n)) (Recv , Log.Canceled) ()
serverStep d (quitting zero) (Recv , Log.Canceled) ()
serverStep d (quitting (suc n)) (Recv , Log.Canceled) ()
serverStep d closed (Recv , Log.Canceled) ()
serverStep d (openN zero) (Recv , Log.Done) ()
serverStep d (openN (suc n)) (Recv , Log.Done) ()
serverStep d (quitting zero) (Recv , Log.Done) ()
serverStep d (quitting (suc n)) (Recv , Log.Done) ()
serverStep d closed (Recv , Log.Done) ()
serverStep d (openN zero) (Send , Log.RequestNext) ()
serverStep d (openN (suc n)) (Send , Log.RequestNext) ()
serverStep d (quitting zero) (Send , Log.RequestNext) ()
serverStep d (quitting (suc n)) (Send , Log.RequestNext) ()
serverStep d closed (Send , Log.RequestNext) ()
serverStep d (openN zero) (Send , Log.BlockAnnouncement _) ()
serverStep d (openN (suc n)) (Send , Log.BlockAnnouncement _) refl = _ , refl , SW.normalOpen
serverStep d (quitting zero) (Send , Log.BlockAnnouncement _) ()
serverStep d (quitting (suc n)) (Send , Log.BlockAnnouncement _) ()
serverStep d closed (Send , Log.BlockAnnouncement _) ()
serverStep d (openN zero) (Send , Log.BlockOffer _ _ _) ()
serverStep d (openN (suc n)) (Send , Log.BlockOffer _ _ _) refl = _ , refl , SW.normalOpen
serverStep d (quitting zero) (Send , Log.BlockOffer _ _ _) ()
serverStep d (quitting (suc n)) (Send , Log.BlockOffer _ _ _) ()
serverStep d closed (Send , Log.BlockOffer _ _ _) ()
serverStep d (openN zero) (Send , Log.BlockTxsOffer _ _) ()
serverStep d (openN (suc n)) (Send , Log.BlockTxsOffer _ _) refl = _ , refl , SW.normalOpen
serverStep d (quitting zero) (Send , Log.BlockTxsOffer _ _) ()
serverStep d (quitting (suc n)) (Send , Log.BlockTxsOffer _ _) ()
serverStep d closed (Send , Log.BlockTxsOffer _ _) ()
serverStep d (openN zero) (Send , Log.Votes _) ()
serverStep d (openN (suc n)) (Send , Log.Votes _) refl = _ , refl , SW.normalOpen
serverStep d (quitting zero) (Send , Log.Votes _) ()
serverStep d (quitting (suc n)) (Send , Log.Votes _) ()
serverStep d closed (Send , Log.Votes _) ()
serverStep d (openN zero) (Send , Log.Quit) ()
serverStep d (openN (suc n)) (Send , Log.Quit) ()
serverStep d (quitting zero) (Send , Log.Quit) ()
serverStep d (quitting (suc n)) (Send , Log.Quit) ()
serverStep d closed (Send , Log.Quit) ()
serverStep d (openN zero) (Send , Log.Canceled) ()
serverStep d (openN (suc n)) (Send , Log.Canceled) refl = _ , refl , SW.canceledOpen
serverStep d (quitting zero) (Send , Log.Canceled) ()
serverStep d (quitting (suc n)) (Send , Log.Canceled) refl = _ , refl , SW.canceledQuitGeneric
serverStep d closed (Send , Log.Canceled) ()
serverStep d (openN zero) (Send , Log.Done) ()
serverStep d (openN (suc n)) (Send , Log.Done) ()
serverStep d (quitting zero) (Send , Log.Done) refl = _ , refl , SW.doneQuit
serverStep d (quitting (suc n)) (Send , Log.Done) ()
serverStep d closed (Send , Log.Done) ()

-- Each bounded client transition is a lookahead client step on the decoded row.
clientStep : ∀ depth s e {t} → nextKind depth client s (Log.forget e) ≡ just t →
  Σ[ w ∈ CW.Wire ] (Client.decode e ≡ just w × CW.Step (toClient s) w (toClient t))
clientStep d (openN zero) (Recv , Log.RequestNext) ()
clientStep d (openN (suc n)) (Recv , Log.RequestNext) ()
clientStep d (quitting zero) (Recv , Log.RequestNext) ()
clientStep d (quitting (suc n)) (Recv , Log.RequestNext) ()
clientStep d closed (Recv , Log.RequestNext) ()
clientStep d (openN zero) (Recv , Log.BlockAnnouncement _) ()
clientStep d (openN (suc n)) (Recv , Log.BlockAnnouncement _) refl = _ , refl , CW.receiveReply
clientStep d (quitting zero) (Recv , Log.BlockAnnouncement _) ()
clientStep d (quitting (suc n)) (Recv , Log.BlockAnnouncement _) refl = _ , refl , CW.drainReply
clientStep d closed (Recv , Log.BlockAnnouncement _) ()
clientStep d (openN zero) (Recv , Log.BlockOffer _ _ _) ()
clientStep d (openN (suc n)) (Recv , Log.BlockOffer _ _ _) refl = _ , refl , CW.receiveReply
clientStep d (quitting zero) (Recv , Log.BlockOffer _ _ _) ()
clientStep d (quitting (suc n)) (Recv , Log.BlockOffer _ _ _) refl = _ , refl , CW.drainReply
clientStep d closed (Recv , Log.BlockOffer _ _ _) ()
clientStep d (openN zero) (Recv , Log.BlockTxsOffer _ _) ()
clientStep d (openN (suc n)) (Recv , Log.BlockTxsOffer _ _) refl = _ , refl , CW.receiveReply
clientStep d (quitting zero) (Recv , Log.BlockTxsOffer _ _) ()
clientStep d (quitting (suc n)) (Recv , Log.BlockTxsOffer _ _) refl = _ , refl , CW.drainReply
clientStep d closed (Recv , Log.BlockTxsOffer _ _) ()
clientStep d (openN zero) (Recv , Log.Votes _) ()
clientStep d (openN (suc n)) (Recv , Log.Votes _) refl = _ , refl , CW.receiveReply
clientStep d (quitting zero) (Recv , Log.Votes _) ()
clientStep d (quitting (suc n)) (Recv , Log.Votes _) refl = _ , refl , CW.drainReply
clientStep d closed (Recv , Log.Votes _) ()
clientStep d (openN zero) (Recv , Log.Quit) ()
clientStep d (openN (suc n)) (Recv , Log.Quit) ()
clientStep d (quitting zero) (Recv , Log.Quit) ()
clientStep d (quitting (suc n)) (Recv , Log.Quit) ()
clientStep d closed (Recv , Log.Quit) ()
clientStep d (openN zero) (Recv , Log.Canceled) ()
clientStep d (openN (suc n)) (Recv , Log.Canceled) refl = _ , refl , CW.receiveReply
clientStep d (quitting zero) (Recv , Log.Canceled) ()
clientStep d (quitting (suc n)) (Recv , Log.Canceled) refl = _ , refl , CW.drainReply
clientStep d closed (Recv , Log.Canceled) ()
clientStep d (openN zero) (Recv , Log.Done) ()
clientStep d (openN (suc n)) (Recv , Log.Done) ()
clientStep d (quitting zero) (Recv , Log.Done) refl = _ , refl , CW.receiveDone
clientStep d (quitting (suc n)) (Recv , Log.Done) ()
clientStep d closed (Recv , Log.Done) ()
clientStep d (openN n) (Send , Log.RequestNext) p with issue-just d n p
... | _ , refl = _ , refl , CW.sendRequest
clientStep d (quitting zero) (Send , Log.RequestNext) ()
clientStep d (quitting (suc n)) (Send , Log.RequestNext) ()
clientStep d closed (Send , Log.RequestNext) ()
clientStep d (openN zero) (Send , Log.BlockAnnouncement _) ()
clientStep d (openN (suc n)) (Send , Log.BlockAnnouncement _) ()
clientStep d (quitting zero) (Send , Log.BlockAnnouncement _) ()
clientStep d (quitting (suc n)) (Send , Log.BlockAnnouncement _) ()
clientStep d closed (Send , Log.BlockAnnouncement _) ()
clientStep d (openN zero) (Send , Log.BlockOffer _ _ _) ()
clientStep d (openN (suc n)) (Send , Log.BlockOffer _ _ _) ()
clientStep d (quitting zero) (Send , Log.BlockOffer _ _ _) ()
clientStep d (quitting (suc n)) (Send , Log.BlockOffer _ _ _) ()
clientStep d closed (Send , Log.BlockOffer _ _ _) ()
clientStep d (openN zero) (Send , Log.BlockTxsOffer _ _) ()
clientStep d (openN (suc n)) (Send , Log.BlockTxsOffer _ _) ()
clientStep d (quitting zero) (Send , Log.BlockTxsOffer _ _) ()
clientStep d (quitting (suc n)) (Send , Log.BlockTxsOffer _ _) ()
clientStep d closed (Send , Log.BlockTxsOffer _ _) ()
clientStep d (openN zero) (Send , Log.Votes _) ()
clientStep d (openN (suc n)) (Send , Log.Votes _) ()
clientStep d (quitting zero) (Send , Log.Votes _) ()
clientStep d (quitting (suc n)) (Send , Log.Votes _) ()
clientStep d closed (Send , Log.Votes _) ()
clientStep d (openN n) (Send , Log.Quit) refl = _ , refl , CW.sendQuit
clientStep d (quitting zero) (Send , Log.Quit) ()
clientStep d (quitting (suc n)) (Send , Log.Quit) ()
clientStep d closed (Send , Log.Quit) ()
clientStep d (openN zero) (Send , Log.Canceled) ()
clientStep d (openN (suc n)) (Send , Log.Canceled) ()
clientStep d (quitting zero) (Send , Log.Canceled) ()
clientStep d (quitting (suc n)) (Send , Log.Canceled) ()
clientStep d closed (Send , Log.Canceled) ()
clientStep d (openN zero) (Send , Log.Done) ()
clientStep d (openN (suc n)) (Send , Log.Done) ()
clientStep d (quitting zero) (Send , Log.Done) ()
clientStep d (quitting (suc n)) (Send , Log.Done) ()
clientStep d closed (Send , Log.Done) ()

-- Bounded server runs translate row by row into genericNext lookahead runs.
serverRun : ∀ {depth s es u} → Pipeline.Spec._⇒⟨_⟩_ depth server s es u →
  Σ[ ws ∈ List SW.Wire ] (serverWires es ≡ just ws × SW.Run genericNext (toServer s) ws (toServer u))
serverRun Pipeline.Spec.done = [] , refl , SW.stop
serverRun (Pipeline.Spec.tau () _)
serverRun {depth} {s} (Pipeline.Spec.vis {e = e} st rest) with serverStep depth s e st | serverRun rest
... | w , dw , stp | ws , dws , run = w ∷ ws , cong₂ _∷?_ dw dws , SW.step stp run

-- Bounded client runs translate row by row into lookahead client runs.
clientRun : ∀ {depth s es u} → Pipeline.Spec._⇒⟨_⟩_ depth client s es u →
  Σ[ ws ∈ List CW.Wire ] (clientWires es ≡ just ws × CW.Run (toClient s) ws (toClient u))
clientRun Pipeline.Spec.done = [] , refl , CW.stop
clientRun (Pipeline.Spec.tau () _)
clientRun {depth} {s} (Pipeline.Spec.vis {e = e} st rest) with clientStep depth s e st | clientRun rest
... | w , dw , stp | ws , dws , run = w ∷ ws , cong₂ _∷?_ dw dws , CW.step stp run

-- Every bounded server trace, at any depth, translates into a genericNext lookahead trace.
server-included-generic : ∀ depth es → Pipeline.Spec.HasTrace depth server Pipeline.idle es →
  Σ[ ws ∈ List SW.Wire ] (serverWires es ≡ just ws × SW.HasTrace genericNext SW.initial ws)
server-included-generic depth es (u , run) with serverRun run
... | ws , eq , r = ws , eq , (toServer u , r)

-- Every bounded client trace, at any depth, translates into a lookahead client trace.
client-included : ∀ depth es → Pipeline.Spec.HasTrace depth client Pipeline.idle es →
  Σ[ ws ∈ List CW.Wire ] (clientWires es ≡ just ws × CW.HasTrace CW.initial ws)
client-included depth es (u , run) with clientRun run
... | ws , eq , r = ws , eq , (toClient u , r)

-- A read-ahead server cancels an outstanding request while the session is still open.
canceledOpenRows : List Log.E
canceledOpenRows = (Recv , Log.RequestNext) ∷ (Send , Log.Canceled) ∷ []

-- Canceled-while-open is bounded but not nodeNext: no inclusion under nodeNext.
node-canceled-open : ∀ depth →
  Pipeline.Spec.HasTrace (suc depth) server Pipeline.idle canceledOpenRows ×
  ¬ (SW.HasTrace nodeNext SW.initial (SW.request ∷ SW.reply canceled ∷ []))
node-canceled-open depth =
  (_ , Pipeline.Spec.vis {depth = suc depth} {role = server} refl
        (Pipeline.Spec.vis {depth = suc depth} {role = server} refl (Pipeline.Spec.done {depth = suc depth} {role = server}))) ,
  λ { (_ , SW.step SW.receiveRequest (SW.step () _)) }

-- A normal reply after Quit is lookahead (nodeNext) but never bounded: the converse fails.
normal-after-quit : ∀ depth →
  SW.HasTrace nodeNext SW.initial (SW.request ∷ SW.quit ∷ SW.reply (normal a) ∷ []) ×
  ¬ Pipeline.Spec.HasTrace (suc depth) server Pipeline.idle
      ((Recv , Log.RequestNext) ∷ (Recv , Log.Quit) ∷ (Send , Log.BlockAnnouncement h) ∷ [])
normal-after-quit depth =
  (_ , SW.step SW.receiveRequest (SW.step SW.receiveQuit (SW.step SW.normalQuit SW.stop))) ,
  λ { (_ , Pipeline.Spec.tau () _)
    ; (_ , Pipeline.Spec.vis _ (Pipeline.Spec.tau () _))
    ; (_ , Pipeline.Spec.vis _ (Pipeline.Spec.vis _ (Pipeline.Spec.tau () _)))
    ; (_ , Pipeline.Spec.vis refl (Pipeline.Spec.vis refl (Pipeline.Spec.vis () _))) }

-- From openN n with k + n ≡ depth, only k further requests fit.
over : ∀ depth k n {u} → k + n ≡ depth →
  ¬ Pipeline.Spec._⇒⟨_⟩_ depth server (openN n) (replicate (suc k) (Recv , Log.RequestNext)) u
over depth k n eq (Pipeline.Spec.tau () _)
over _ zero n refl (Pipeline.Spec.vis st _) with issue-just n n st
... | lt , _ = <-irrefl refl lt
over depth (suc k) n eq (Pipeline.Spec.vis st rest) with issue-just depth n st
... | _ , refl = over depth k (suc n) (trans (+-suc k n) eq) rest

-- The bounded server rejects depth + 1 outstanding requests.
over-depth : ∀ depth →
  ¬ Pipeline.Spec.HasTrace depth server Pipeline.idle (replicate (suc depth) (Recv , Log.RequestNext))
over-depth depth (_ , run) = over depth depth 0 (+-identityʳ depth) run

-- Request rows translate to lookahead request rows.
request-wires : ∀ k → serverWires (replicate k (Recv , Log.RequestNext)) ≡ just (replicate k SW.request)
request-wires zero = refl
request-wires (suc k) = cong (just SW.request ∷?_) (request-wires k)

-- The lookahead server accepts any number of requests from any open state.
requests : ∀ p k n → SW.HasTrace p (SW.Open n) (replicate k SW.request)
requests p zero n = _ , SW.stop
requests p (suc k) n with requests p k (suc n)
... | u , r = u , SW.step SW.receiveRequest r

-- The same over-depth rows are lookahead traces under either contract.
over-depth-lookahead : ∀ depth p →
  serverWires (replicate (suc depth) (Recv , Log.RequestNext)) ≡ just (replicate (suc depth) SW.request) ×
  SW.HasTrace p SW.initial (replicate (suc depth) SW.request)
over-depth-lookahead depth p = request-wires (suc depth) , requests p (suc depth) 0

-- A reply received before its request (lookahead Lead) is never bounded: the client converse fails.
client-lead : ∀ depth →
  CW.HasTrace CW.initial (CW.reply (normal a) ∷ CW.request ∷ []) ×
  ¬ Pipeline.Spec.HasTrace depth client Pipeline.idle
      ((Recv , Log.BlockAnnouncement h) ∷ (Send , Log.RequestNext) ∷ [])
client-lead depth =
  (_ , CW.step CW.earlyReply (CW.step CW.finishRequest CW.stop)) ,
  λ { (_ , Pipeline.Spec.tau () _) ; (_ , Pipeline.Spec.vis () _) }
