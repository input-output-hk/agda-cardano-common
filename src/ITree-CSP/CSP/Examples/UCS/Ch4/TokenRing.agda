{-# OPTIONS --guardedness #-}

-- UCS chapter 4 §4.2: the token ring and its EMPTY-TOKEN LIVELOCK.
--
-- Machine-readable companion file:
--
--   fdr-examples/ucs/chapter04/tokring.csp   (UCS ch. 4, the token ring)
--
-- FDR reports two assertions on the token ring:
--
--   assert Ring  :[deadlock free]      -- HOLDS  (the SIBLING module proves it)
--   assert RingH :[divergence free]    -- FAILS  (proved here: RingH *does* diverge)
--
-- `RingH = Ring \ {| ring |}` hides the internal `ring` channel over which the
-- circulating token is handed from node to node.  A single EMPTY token can
-- circle the ring forever without any `send`/`receive` ever occurring: node 0
-- hands the empty token to node 1 (`ring.1.Empty`), node 1 hands it back to
-- node 0 (`ring.0.Empty`), and so on.  Each hand-off is a synchronisation on a
-- `ring` event; once `ring` is HIDDEN every hand-off becomes an internal τ, so
-- the endless empty-token circulation is an infinite τ-loop — divergence.  This
-- is the token analogue of `CSP.Examples.UCS.Ch4.GeneralNetworkLivelock` (there
-- a packet circles a directed cycle over a hidden `pass` channel).
--
-- REDUCTION.  We take the minimal instance N = 2 nodes, 1 token.  Node arithmetic
-- is `sucm` = (·+1) mod 2 (0↦1, 1↦0); the message payload is trivial (T = ⊤), so
-- the routing header carried by a *full* token is just (src , dst) : Node × Node.
--
-- PINNED offers.  Every offer of every node state is PINNED to its exact value
-- (no value-generalisation), because these same node definitions are re-used by
-- the sibling `Ring :[deadlock free]` module, whose claim is UNIVERSAL — a
-- generalised offer there would be unsound.  Here the divergence only ever visits
-- the purely-EMPTY states (`NodeR`/`NodeE`), never a `NodeF`, faithful to the
-- source's "the ring can diverge in the empty state".

module CSP.Examples.UCS.Ch4.TokenRing where

open import Level using () renaming (zero to lzero)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
import Data.Fin as Fin
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic renaming (⊤ to ⊤poly) using ()
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable.Core using (_⊎-dec_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees
open PTree

-------------------------------------------------------------------------------------
-- §1. Node type and ring arithmetic (N = 2)
-------------------------------------------------------------------------------------

Node : Set
Node = Fin 2

n0 n1 : Node
n0 = fzero
n1 = fsuc fzero

-- (·+1) mod 2 : 0 ↦ 1, 1 ↦ 0
sucm : Node → Node
sucm fzero        = n1
sucm (fsuc fzero) = n0

-------------------------------------------------------------------------------------
-- §2. Tokens and the event type
-------------------------------------------------------------------------------------

-- A token is either EMPTY (free to carry a fresh packet) or FULL, carrying a
-- routing header (src , dst).  The message payload proper is trivial (T = ⊤).
data Token : Set where
  Empty : Token
  Full  : (Node × Node) → Token      -- Full (src , dst)

data TkEv : Set → Set where
  send    : TkEv (Node × Node)       -- send.n.dst     : (n , dst)
  receive : TkEv (Node × Node)       -- receive.n.src  : (n , src)
  ring    : TkEv (Node × Token)      -- ring.n.token   : (n , tok)

TkEv-≟ : (x y : AnyTypes TkEv) → Dec (x ≡ y)
TkEv-≟ (_ , send)    (_ , send)    = yes refl
TkEv-≟ (_ , receive) (_ , receive) = yes refl
TkEv-≟ (_ , ring)    (_ , ring)    = yes refl
TkEv-≟ (_ , send)    (_ , receive) = no (λ ())
TkEv-≟ (_ , send)    (_ , ring)    = no (λ ())
TkEv-≟ (_ , receive) (_ , send)    = no (λ ())
TkEv-≟ (_ , receive) (_ , ring)    = no (λ ())
TkEv-≟ (_ , ring)    (_ , send)    = no (λ ())
TkEv-≟ (_ , ring)    (_ , receive) = no (λ ())

open import CSP.Operators TkEv-≟
open EventSet

-------------------------------------------------------------------------------------
-- §3. Per-node alphabet
-------------------------------------------------------------------------------------

-- Node `n` owns `send.n`, `receive.n` (both solo), and the two ring endpoints it
-- touches: `ring.n` (the token arriving from its predecessor) and `ring.(sucm n)`
-- (the token it hands to its successor).  `ring.j` therefore lives in both `A j`
-- and `A (pred j)`, i.e. it is a SYNCHRONISATION between the two adjacent nodes.
A : Node → EventSet
A n .mem (_ , send)    (j , _) = j ≡ n
A n .mem (_ , receive) (j , _) = j ≡ n
A n .mem (_ , ring)    (j , _) = (j ≡ n) ⊎ (j ≡ sucm n)
A n .dec (_ , send)    (j , _) = j Fin.≟ n
A n .dec (_ , receive) (j , _) = j Fin.≟ n
A n .dec (_ , ring)    (j , _) = (j Fin.≟ n) ⊎-dec (j Fin.≟ sucm n)

-------------------------------------------------------------------------------------
-- §4. The node states, the ring, and its hidden form
-------------------------------------------------------------------------------------

TProc : Set₁
TProc = PTree TkEv (ExtI TkEv) (⊤poly {lzero})

-- NodeE n       — EMPTY node (does not hold the token).  Accepts the token from its
--                 predecessor: `ring.n.Empty → NodeR n`  and  `ring.n.(Full p) → NodeF n p`.
-- NodeR n       — node holding the EMPTY token.  Either injects a fresh packet
--                 `send.n?dst:diff(Nodes,{n}) → NodeF n (n , dst)`  (no self-send, matching
--                 the source `tokring.csp`)  or forwards the empty token to its successor
--                 `ring.(sucm n).Empty → NodeE n`.
-- NodeF n (s,r) — node holding a FULL token (packet (s , r)).  If it is the destination
--                 (`r ≡ n`) it delivers `receive.n.s → NodeR n`; otherwise it forwards
--                 `ring.(sucm n).(Full (s,r)) → NodeE n`.  Offers are PINNED to the exact
--                 value throughout.
NodeE : Node → TProc
NodeR : Node → TProc
NodeF : Node → (Node × Node) → TProc

force (NodeE n) = react
  (λ where
     (_ , send)    _            → nothing
     (_ , receive) _            → nothing
     (_ , ring)    (j , Empty)  → case j Fin.≟ n of λ where
         (yes _) → just (NodeR n)
         (no  _) → nothing
     (_ , ring)    (j , Full p) → case j Fin.≟ n of λ where
         (yes _) → just (NodeF n p)
         (no  _) → nothing)
  ∅t

force (NodeR n) = react
  (λ where
     (_ , send)    (j , dst)   → case j Fin.≟ n of λ where
         (yes _) → case dst Fin.≟ n of λ where
             (yes _) → nothing                         -- no self-send: dst ≢ n
             (no  _) → just (NodeF n (n , dst))
         (no  _) → nothing
     (_ , receive) _           → nothing
     (_ , ring)    (j , Empty) → case j Fin.≟ sucm n of λ where
         (yes _) → just (NodeE n)
         (no  _) → nothing
     (_ , ring)    (j , Full _) → nothing)
  ∅t

force (NodeF n (s , r)) = react
  (λ where
     (_ , send)    _                    → nothing
     (_ , receive) (j , src)            → case r Fin.≟ n of λ where
         (yes _) → case j Fin.≟ n of λ where
             (yes _) → case src Fin.≟ s of λ where
                 (yes _) → just (NodeR n)
                 (no  _) → nothing
             (no  _) → nothing
         (no  _) → nothing
     (_ , ring)    (j , Empty)          → nothing
     (_ , ring)    (j , Full (s′ , r′)) → case r Fin.≟ n of λ where
         (yes _) → nothing                         -- destination: deliver, never forward
         (no  _) → case j Fin.≟ sucm n of λ where
             (yes _) → case s′ Fin.≟ s of λ where
                 (yes _) → case r′ Fin.≟ r of λ where
                     (yes _) → just (NodeE n)      -- forward to (sucm n) at the PINNED value
                     (no  _) → nothing
                 (no  _) → nothing
             (no  _) → nothing)
  ∅t

-- Initial ring: node 0 holds the (single, empty) token; node 1 is empty.
Init : Node → TProc
Init fzero        = NodeR fzero
Init (fsuc fzero) = NodeE (fsuc fzero)

node : Node → Comp TkEv (⊤poly {lzero})
node i = comp (A i) (Init i)

RetR : Set
RetR = RetOf⁺ (node n0) (node n1 ∷ [])

Ring : PTree TkEv (ExtI TkEv) RetR
Ring = ∥ₐ⁺ (node n0) (node n1 ∷ [])

-- The hidden channel: every `ring` event.
ring-cs : AnyTypes TkEv → Set
ring-cs (_ , send)    = ⊥
ring-cs (_ , receive) = ⊥
ring-cs (_ , ring)    = ⊤

ring-dec : (at : AnyTypes TkEv) → Dec (ring-cs at)
ring-dec (_ , send)    = no (λ z → z)
ring-dec (_ , receive) = no (λ z → z)
ring-dec (_ , ring)    = yes tt

ringES : EventSet
ringES = chanSet ring-cs ring-dec

RingH : PTree TkEv (ExtI TkEv) RetR
RingH = Ring ∖ ringES

-------------------------------------------------------------------------------------
-- §5. Livelock: RingH diverges in the purely-empty state
-------------------------------------------------------------------------------------

open import Semantics.LTS       {E = TkEv} {I = ExtI TkEv} hiding (Diverges)
open import Semantics.Deadlock  {E = TkEv} {I = ExtI TkEv}
  using (_⟹∖√⟨_⟩_; ∖√-refl; ∖√-ev)
open import Semantics.DRBisim   {E = TkEv} {I = ExtI TkEv} using (Diverges)
open import Semantics.DeadlockDR {E = TkEv} {I = ExtI TkEv} using (DivergenceFree)
open import CSP.Laws.Traces.TraceLawsHide TkEv-≟ using (Hide-hidden)

-- The two empty-token configurations, cycled by the circulating empty token.
--   configA : node 0 holds the empty token (NodeR 0), node 1 empty (NodeE 1)  [= Ring]
--   configB : node 1 holds the empty token (NodeR 1), node 0 empty (NodeE 0)
configA configB : PTree TkEv (ExtI TkEv) RetR
configA = Ring
configB = ∥ₐ⁺ (comp (A n0) (NodeE n0)) (comp (A n1) (NodeR n1) ∷ [])

-- Their hidden (τ-cycling) forms.  circA is definitionally RingH.
circA circB : PTree TkEv (ExtI TkEv) RetR
circA = configA ∖ ringES
circB = configB ∖ ringES

ringEv : Node → Token → Event
ringEv j tok = evLabel (Node × Token) ring (j , tok)

-- configA → configB : node 0 hands the empty token to node 1 over `ring.1.Empty`
-- (a synchronisation: `ring.1` ∈ A 0 as `ring.(sucm 0)`, and ∈ A 1 as `ring.1`).
configA-pass : configA ─[ ev (evl (ringEv n1 Empty)) ]─► configB
configA-pass = αpar-sync-step {at = _ , ring} {a = n1 , Empty}
                 (inj₂ refl)          -- ring.1 ∈ A 0  (1 ≡ sucm 0)
                 (inj₁ (inj₁ refl))   -- ring.1 ∈ A 1  (1 ≡ 1)
                 refl refl refl refl

-- configB → configA : node 1 hands the empty token back to node 0 over `ring.0.Empty`.
configB-pass : configB ─[ ev (evl (ringEv n0 Empty)) ]─► configA
configB-pass = αpar-sync-step {at = _ , ring} {a = n0 , Empty}
                 (inj₁ refl)          -- ring.0 ∈ A 0  (0 ≡ 0)
                 (inj₁ (inj₂ refl))   -- ring.0 ∈ A 1  (0 ≡ sucm 1)
                 refl refl refl refl

-- Under `∖ ringES` each hand-off becomes an internal τ (`Hide-hidden`).
circA-τ : circA ─[ τ ]─► circB
circA-τ = Hide-hidden ringES configA tt configA-pass

circB-τ : circB ─[ τ ]─► circA
circB-τ = Hide-hidden ringES configB tt configB-pass

-- The 2-periodic τ-loop: circA (= RingH) diverges.
circA-diverges : Diverges circA
circB-diverges : Diverges circB

circA-diverges .Diverges.next = circB
circA-diverges .Diverges.step = circA-τ
circA-diverges .Diverges.rest = circB-diverges

circB-diverges .Diverges.next = circA
circB-diverges .Diverges.step = circB-τ
circB-diverges .Diverges.rest = circA-diverges

-------------------------------------------------------------------------------------
-- §6. The livelock theorem: `RingH :[divergence free]` FAILS.
-------------------------------------------------------------------------------------

-- At the initial empty state (s = [], reach = ∖√-refl, t′ = RingH) the empty token
-- already circulates forever, so no `send` is ever needed.
tokenRing-livelocks :
  Σ[ s ∈ List Event ] Σ[ t′ ∈ PTree TkEv (ExtI TkEv) RetR ]
    (RingH ⟹∖√⟨ s ⟩ t′ × Diverges t′)
tokenRing-livelocks = [] , RingH , ∖√-refl , circA-diverges

¬tokenRing-divergenceFree : ¬ DivergenceFree RingH
¬tokenRing-divergenceFree df =
  let (s , t′ , reach , div) = tokenRing-livelocks in df reach div
