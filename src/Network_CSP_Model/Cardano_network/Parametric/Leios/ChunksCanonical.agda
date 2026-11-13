{-# OPTIONS --safe --guardedness #-}

-- Honest requests are canonical when their EB table fits the wire ceiling.
-- The premise also applies to locally forged bodies; fetchBody alone does not
-- constrain the forge/store path.
open import Cardano_network.Params using (Params)
module Cardano_network.Parametric.Leios.ChunksCanonical (p : Params) where

open import Data.Bool using (T; true; false)
open import Data.List using (List; []; _∷_; _++_; concat; length; applyUpTo)
import Data.List.Relation.Binary.Sublist.Propositional as Sub
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _≤ᵇ_; _<ᵇ_; z≤n; s≤s)
import Data.Nat.Properties as N
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl; sym; subst)
open import Cardano_network.Replay.LeiosFetchWire using (maxTxs)
open import Cardano_network.Replay.LeiosFetchWords
  using (canonical; canonicalFrom; canonical-lower; canonical-bound; canonical-tail; ∧-intro)
open import Cardano_network.Parametric.Leios.LeiosParams p

-- Relax the initial lower bound without changing strict ordering or the cap.
canonical-weaken : ∀ lo hi xs → lo ≤ hi → T (canonicalFrom hi xs) → T (canonicalFrom lo xs)
canonical-weaken lo hi [] low can = tt
canonical-weaken lo hi (x ∷ xs) low can =
  ∧-intro {a = lo ≤ᵇ x} {b = (x <ᵇ maxTxs) Data.Bool.∧ canonicalFrom (suc x) xs}
    (N.≤⇒≤ᵇ (N.≤-trans low (canonical-lower hi x xs can)))
    (∧-intro {a = x <ᵇ maxTxs} {b = canonicalFrom (suc x) xs}
      (N.<⇒<ᵇ (canonical-bound hi x xs can)) (canonical-tail hi x xs can))

-- A canonical concatenation gives a canonical prefix and a canonical suffix.
canonical-split : ∀ lo xs ys → T (canonicalFrom lo (xs ++ ys)) →
  T (canonicalFrom lo xs) × T (canonical ys)
canonical-split lo [] ys can = tt , canonical-weaken 0 lo ys z≤n can
canonical-split lo (x ∷ xs) ys can =
  ∧-intro {a = lo ≤ᵇ x} {b = (x <ᵇ maxTxs) Data.Bool.∧ canonicalFrom (suc x) xs}
    (N.≤⇒≤ᵇ (canonical-lower lo x (xs ++ ys) can))
    (∧-intro {a = x <ᵇ maxTxs} {b = canonicalFrom (suc x) xs}
      (N.<⇒<ᵇ (canonical-bound lo x (xs ++ ys) can)) (proj₁ rest)) , proj₂ rest
  where
  -- Recurse after removing the shared head of the concatenation.
  rest = canonical-split (suc x) xs ys (canonical-tail lo x (xs ++ ys) can)

-- Every component of a canonical concatenation is itself canonical.
canonical-chunks : ∀ xss → T (canonical (concat xss)) → All (λ xs → T (canonical xs)) xss
canonical-chunks [] can = []
canonical-chunks (xs ∷ xss) can = proj₁ parts ∷ canonical-chunks xss (proj₂ parts)
  where
  -- Split at the first chunk boundary.
  parts = canonical-split 0 xs (concat xss) can

-- Increasing tabulations below the cap satisfy the Boolean canonical predicate.
canonical-tabulate : ∀ n (f : ℕ → ℕ) lo → lo ≤ f 0 →
  (∀ i → i < n → f i < maxTxs) → (∀ i → suc (f i) ≤ f (suc i)) →
  T (canonicalFrom lo (applyUpTo f n))
canonical-tabulate zero f lo low bounded increasing = tt
canonical-tabulate (suc n) f lo low bounded increasing =
  ∧-intro {a = lo ≤ᵇ f 0} {b = (f 0 <ᵇ maxTxs) Data.Bool.∧ canonicalFrom (suc (f 0)) (applyUpTo (λ i → f (suc i)) n)}
    (N.≤⇒≤ᵇ low)
    (∧-intro {a = f 0 <ᵇ maxTxs} {b = canonicalFrom (suc (f 0)) (applyUpTo (λ i → f (suc i)) n)}
      (N.<⇒<ᵇ (bounded 0 (s≤s z≤n)))
      (canonical-tabulate n (λ i → f (suc i)) (suc (f 0)) (increasing 0)
        (λ i lt → bounded (suc i) (s≤s lt)) (λ i → increasing (suc i))))

-- All body offsets are ordered and below maxTxs when the table fits the cap.
allOffsets-canonical : ∀ lp h → length (LeiosParams.ebTxs lp h) ≤ maxTxs →
  T (canonical (allOffsets lp h))
allOffsets-canonical lp h bounded = canonical-tabulate (length (LeiosParams.ebTxs lp h))
  (λ i → i) 0 N.≤-refl (λ i lt → N.≤-trans lt bounded) (λ i → N.≤-refl)

-- Removing offsets preserves their strict order and the wire ceiling.
missing-canonical : ∀ {xs ys} → Sub._⊆_ xs ys → T (canonical ys) → T (canonical xs)
missing-canonical sub can = from 0 sub can
  where
  -- Track the lower bound while skipped entries advance the source list.
  from : ∀ lo {xs ys} → Sub._⊆_ xs ys → T (canonicalFrom lo ys) → T (canonicalFrom lo xs)
  from lo Sub.[] can = tt
  from lo {xs = y ∷ xs} {ys = .y ∷ ys} (Sub._∷_ refl sub) can =
    ∧-intro {a = lo ≤ᵇ y} {b = (y <ᵇ maxTxs) Data.Bool.∧ canonicalFrom (suc y) xs}
      (N.≤⇒≤ᵇ (canonical-lower lo y ys can))
      (∧-intro {a = y <ᵇ maxTxs} {b = canonicalFrom (suc y) xs}
        (N.<⇒<ᵇ (canonical-bound lo y ys can))
        (from (suc y) sub (canonical-tail lo y ys can)))
  from lo {xs = xs} {ys = y ∷ ys} (Sub._∷ʳ_ .y sub) can =
    canonical-weaken lo (suc y) xs (N.m≤n⇒m≤1+n (canonical-lower lo y ys can))
      (from (suc y) sub (canonical-tail lo y ys can))

-- Partitioning any canonical missing list preserves canonicity per request.
chunksOf-canonical : ∀ c xs → 1 ≤ c → T (canonical xs) →
  All (λ bm → T (canonical bm)) (chunksOf c xs)
chunksOf-canonical c xs positive can = canonical-chunks (chunksOf c xs)
  (subst (λ ys → T (canonical ys)) (sym (chunksOf-concat {xs = xs} positive)) can)

-- A sublist of the body's offsets supplies the client-send canonical condition.
missingChunks-canonical : ∀ lp h ms → Sub._⊆_ ms (allOffsets lp h) →
  length (LeiosParams.ebTxs lp h) ≤ maxTxs →
  All (λ bm → T (canonical bm)) (chunksOf (LeiosParams.chunk lp) ms)
missingChunks-canonical lp h ms sub bounded =
  chunksOf-canonical (LeiosParams.chunk lp) ms (LeiosParams.chunk-pos lp)
    (missing-canonical sub (allOffsets-canonical lp h bounded))

-- Partitioning the complete ordered offset list preserves canonicity per request.
txChunks-canonical : ∀ lp h → length (LeiosParams.ebTxs lp h) ≤ maxTxs →
  All (λ bm → T (canonical bm)) (txChunks lp h)
txChunks-canonical lp h bounded = chunksOf-canonical (LeiosParams.chunk lp)
  (allOffsets lp h) (LeiosParams.chunk-pos lp) (allOffsets-canonical lp h bounded)

open import Cardano_network.Parametric.Topology using (Topology)
import Cardano_network.Parametric.Node as NodeModule
import Cardano_network.Parametric.Leios.NodeLogicL as NLL
import Cardano_network.Net as Net
import Cardano_network.Data as Data
import CSP.Operators as Operators
import Data.Unit as U
open import Data.Maybe using (nothing; just)
open import Process_Trees using (ExtI)
open import Semantics.LTS {E = Net.Net_Api p (Data.Payload p)} {I = ExtI (Net.Net_Api p (Data.Payload p))}
  using (Event; evLabel)
open import CSP.Laws.DivFree.Count (Net.Net_Api-≟ p {Data.Payload p})
  using (AllT; AllT-Stop; AllT-Ret; AllT-⟶; AllT-Output; AllT-□; AllT->>=)

-- Connect the pure sublist facts to every branch of the actual client walk.
module Walk (lp : LeiosParams) (t : Topology p)
  (apiES : Operators.EventSet (Net.Net_Api-≟ p {Data.Payload p}))
  (voterOf : Topology.Node t → Params.VoterId p) where

  open NodeModule p t apiES using (Proc)
  open NLL.Generic p lp t apiES voterOf
    using (missingOffsets; getTxEv; lacksTxEv; at?; DecEq-⊤poly
          ; fetchTxs; fetchChunks; getBodyEv; putAll; putChecked; putTxEv; entryOk)
  open Params p using (EBHash)
  open Topology t using (Node)

  -- A continuation need only handle order-preserving sublists of the input offsets.
  missingOffsets-sublist : ∀ (P : Event → Set) n h os (k : Data.TxBitmap p → Proc) →
    (∀ hash tx → P (evLabel _ (getTxEv n hash) tx)) →
    (∀ hash → P (evLabel _ (lacksTxEv n hash) U.tt)) →
    (∀ ms → Sub._⊆_ ms os → AllT P (k ms)) →
    AllT P (missingOffsets n h os k)
  missingOffsets-sublist P n h [] k pos neg cont = cont [] Sub.[]
  missingOffsets-sublist P n h (o ∷ os) k pos neg cont with at? o (LeiosParams.ebTxs lp h)
  ... | nothing = AllT-Stop
  ... | just (hash , _) = AllT-□
    (AllT-⟶ _ (pos hash) (λ _ → missingOffsets-sublist P n h os k pos neg
      (λ ms sub → cont ms (Sub._∷ʳ_ o sub))))
    (AllT-⟶ _ (λ _ → neg hash) (λ _ →
      missingOffsets-sublist P n h os (λ ms → k (o ∷ ms)) pos neg
        (λ ms sub → cont (o ∷ ms) (Sub._∷_ refl sub))))

  -- The walk supplies canonical missing chunks to its client-send continuation.
  missingOffsets-canonical : ∀ (P : Event → Set) n h (k : Data.TxBitmap p → Proc) →
    (∀ hash tx → P (evLabel _ (getTxEv n hash) tx)) →
    (∀ hash → P (evLabel _ (lacksTxEv n hash) U.tt)) →
    length (LeiosParams.ebTxs lp h) ≤ maxTxs →
    (∀ ms → All (λ bm → T (canonical bm)) (chunksOf (LeiosParams.chunk lp) ms) → AllT P (k ms)) →
    AllT P (missingOffsets n h (allOffsets lp h) k)
  missingOffsets-canonical P n h k pos neg bounded cont =
    missingOffsets-sublist P n h (allOffsets lp h) k pos neg
      (λ ms sub → cont ms (missingChunks-canonical lp h ms sub bounded))

  open Operators (Net.Net_Api-≟ p {Data.Payload p}) using (_>>_; _◁_▷_; Stop)
  open Net p using (apiLP; lfpSendBlockTxsRequest; lfpRecvBlockTxs)
  open Params p using (decTx)
  open Data p using (DecEq-TxsRequest; DecEq-EBPoint)
  open import Data.Bool.ListAction using (all)
  open import Class.DecEq using (_≟_)
  open import Relation.Nullary.Decidable using (⌊_⌋)

  -- Only BlockTxsRequest sends constrain the bitmap; other visible events are free.
  CanonicalSend : Event → Set
  CanonicalSend (evLabel _ (apiLP _ _ lfpSendBlockTxsRequest) (_ , bm)) = T (canonical bm)
  CanonicalSend _ = U.⊤

  -- Depositing checked transactions cannot emit a request bitmap.
  putAll-canonical : ∀ n es → AllT CanonicalSend (putAll n es)
  putAll-canonical n [] = AllT-Ret
  putAll-canonical n ((o , tx) ∷ es) =
    AllT-Output (putTxEv n) tx tt (putAll-canonical n es)

  -- Reply validation either deposits transactions or stops without a send.
  putChecked-canonical : ∀ n h es → AllT CanonicalSend (putChecked n h es)
  putChecked-canonical n h es with all (entryOk h) es
  ... | true = putAll-canonical n es
  ... | false = AllT-Stop

  -- The actual chunk sender preserves canonicity through every received reply.
  fetchChunks-canonical : ∀ n l d q bms → All (λ bm → T (canonical bm)) bms →
    AllT CanonicalSend (fetchChunks n l d q bms)
  fetchChunks-canonical n l d q [] [] = AllT-Ret
  fetchChunks-canonical n l d q (bm ∷ bms) (can ∷ cans) =
    AllT-Output ⦃ DecEq-TxsRequest ⦄ (apiLP l d lfpSendBlockTxsRequest) (q , bm) can
      (AllT-⟶ (apiLP l d lfpRecvBlockTxs) (λ _ → tt)
        (λ { (q′ , es) → checked q′ es }))
    where
    -- A bad reply point stops; a matching point continues with the canonical tail.
    checked : ∀ q′ es → AllT CanonicalSend
      ((putChecked n (proj₁ q) es >> fetchChunks n l d q bms)
        ◁ ⌊ DecEq-EBPoint ._≟_ q′ q ⌋ ▷ Stop)
    checked q′ es with ⌊ DecEq-EBPoint ._≟_ q′ q ⌋
    ... | true = AllT->>= (putChecked-canonical n (proj₁ q) es)
        (λ _ → fetchChunks-canonical n l d q bms cans)
    ... | false = AllT-Stop

  -- Every BlockTxsRequest sent by fetchTxs has a canonical missing-only bitmap.
  -- The table bound is the same stored/forged-body premise as txChunks-canonical.
  fetchTxs-canonical : ∀ n l d q →
    length (LeiosParams.ebTxs lp (proj₁ q)) ≤ maxTxs →
    AllT CanonicalSend (fetchTxs n l d q)
  fetchTxs-canonical n l d q bounded =
    AllT-⟶ (getBodyEv n (proj₁ q)) (λ _ → tt) (λ _ →
      missingOffsets-canonical CanonicalSend n (proj₁ q)
        (λ ms → fetchChunks n l d q (chunksOf (LeiosParams.chunk lp) ms))
        (λ _ _ → tt) (λ _ → tt) bounded
        (λ ms cans → fetchChunks-canonical n l d q _ cans))
