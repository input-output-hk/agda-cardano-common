{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — the network graph (`Topology`).
--
-- The campaign's four nodes have so far been four hand-written
-- definitions with no shared node type. This module supplies that
-- missing graph layer: a finite set of nodes, and for each link (drawn
-- from `Params`' `numLinks`) the pair of nodes at its `lo`/`hi` ends,
-- together with each node's incident (link, own-direction) list.
--
-- `numNodes` is derived from a `numNodes-1 : ℕ` field (so `numNodes =
-- suc numNodes-1`) rather than being a bare `ℕ` field: the system fold
-- over nodes uses `⦀Fin⁺`, which is indexed by a `suc _`-shaped count,
-- and this structurally encodes "a network has at least one node" the
-- same way `endpointsOf`'s head-plus-tail shape encodes "a node has at
-- least one incident link".
--
-- `endpointsOf` is a field, not a computed filter over `Fin numLinks`,
-- because deriving it by filtering would make later definitional gates
-- depend on that filter reducing at a concrete instance — exactly the
-- kind of thing that silently fails to normalise. Supplying the list
-- and requiring it to agree with `ends` (via `endpoints-sound`/
-- `endpoints-complete`) moves that obligation to a one-line proof at
-- instantiation instead.
------------------------------------------------------------------------

module CSP.Examples.Cardano_network.Parametric.Topology where

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.List using (List; []; _∷_; filter; allFin; cartesianProduct)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
  using (∈-allFin; ∈-cartesianProduct⁺; ∈-filter⁺; ∈-filter⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.List.Relation.Unary.Unique.Propositional.Properties
  using (allFin⁺; cartesianProduct⁺; filter⁺)
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.AllPairs as AP
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Unary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst)

open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Base using (Dir; lo; hi)

-- the network graph: a finite set of nodes, and for each link the pair of nodes at its
-- `lo` and `hi` ends, together with each node's incident (link, own-direction) list.
record Topology (p : Params) : Set where
  open Params p using (numLinks)

  field
    -- one less than the number of nodes (so a network always has ≥ 1 node)
    numNodes-1 : ℕ

  -- the number of nodes in the network
  numNodes : ℕ
  numNodes = suc numNodes-1

  -- a node index
  Node : Set
  Node = Fin numNodes

  field
    -- the (lo-endpoint , hi-endpoint) node pair of each link
    ends        : Fin numLinks → Node × Node
    -- no link joins a node to itself
    ends-irrefl : ∀ l → proj₁ (ends l) ≢ proj₂ (ends l)

  -- the node sitting at direction `d` of link `l` (a single-clause pattern-matching
  -- lambda, not a multi-clause function: Agda rejects a multi-clause definition
  -- sitting between two `field` blocks inside a record)
  endAt : Fin numLinks → Dir → Node
  endAt l = λ { lo → proj₁ (ends l) ; hi → proj₂ (ends l) }

  field
    -- each node's incident endpoints, as a head plus tail (every node has ≥ 1 link)
    endpointsOf : Node → (Fin numLinks × Dir) × List (Fin numLinks × Dir)

  -- the flattening of `endpointsOf n` into a single (link, direction) list
  endpointsList : Node → List (Fin numLinks × Dir)
  endpointsList n = proj₁ (endpointsOf n) ∷ proj₂ (endpointsOf n)

  field
    -- every listed endpoint really belongs to that node
    endpoints-sound     : ∀ n l d → (l , d) ∈ endpointsList n → endAt l d ≡ n
    -- every endpoint belonging to a node is listed
    endpoints-complete  : ∀ n l d → endAt l d ≡ n → (l , d) ∈ endpointsList n
    -- no endpoint is listed twice, so a node never runs one link's bundle more than once
    endpoints-unique    : ∀ n → Unique (endpointsList n)

-- the opposite direction on a link
opposite : Dir → Dir
opposite lo = hi
opposite hi = lo

-- distinct nodes share no endpoint: if (l , d) were incident to both, soundness makes
-- both equal to `endAt l d`, hence equal to each other.
endpoints-disj : ∀ {p} (t : Topology p) n m → n ≢ m
               → ∀ l d → (l , d) ∈ Topology.endpointsList t n → (l , d) ∈ Topology.endpointsList t m → ⊥
endpoints-disj t n m n≢m l d n∈ m∈ =
  n≢m (trans (sym (Topology.endpoints-sound t n l d n∈)) (Topology.endpoints-sound t m l d m∈))

------------------------------------------------------------------------
-- A smart constructor: `endpointsOf` and its three laws from `ends`
--
-- Hand-building a `Topology` costs one `endpointsOf` clause per node
-- plus three proofs whose sizes grow with the degrees — `endpoints-
-- unique` alone is d(d-1)/2 pairwise `≢`s at a degree-d node, which is
-- already six terms at the five-node star's hub.  All of it is in fact
-- determined by `ends`: a node's endpoints are exactly the (link ,
-- direction) pairs the graph puts at that node, so filtering the full
-- enumeration of endpoints by decidable ownership derives the list and
-- all three laws.  The one thing `ends` does NOT determine is that
-- every node HAS an endpoint — `endpointsOf` returns a head-plus-tail
-- pair, so the derived list must be non-empty — hence the Σ-shaped
-- "no isolated nodes" hypothesis.
--
-- `mkTopology` is an ADDITIONAL constructor for new instances, never a
-- replacement for the field-supplied route: as the header note above
-- explains, a derived `endpointsOf` puts any definitional gate (e.g.
-- `Parametric.DiamondInstance`'s `diamond-faithful`) at the mercy of
-- `filter` normalising AND of the order `filter` happens to pick.
-- Instances that carry such a gate keep their hand-written lists.
------------------------------------------------------------------------

-- the node at direction `d` of link `l`, read straight off an `ends` function; the
-- free-standing counterpart of the record's derived `endAt`, usable in the types of
-- `mkTopology`'s hypotheses (i.e. before the record value exists)
endAtOf : ∀ {L N : ℕ} → (Fin L → Fin N × Fin N) → Fin L → Dir → Fin N
endAtOf ends l lo = proj₁ (ends l)
endAtOf ends l hi = proj₂ (ends l)

-- the head and tail of a provably non-empty list (the `[]` case is discharged, not
-- defaulted: there is no element to return)
headTail : ∀ {a} {A : Set a} (xs : List A) → xs ≢ [] → A × List A
headTail []       ne = ⊥-elim (ne refl)
headTail (x ∷ xs) _  = x , xs

-- re-consing `headTail`'s head onto its tail recovers the original list; this is what
-- transports the three endpoint laws from the derived list to `endpointsList`
headTail-flatten : ∀ {a} {A : Set a} (xs : List A) (ne : xs ≢ [])
                 → proj₁ (headTail xs ne) ∷ proj₂ (headTail xs ne) ≡ xs
headTail-flatten []       ne = ⊥-elim (ne refl)
headTail-flatten (_ ∷ _)  _  = refl

-- a list with a member is not empty
∈⇒≢[] : ∀ {a} {A : Set a} {x : A} {xs : List A} → x ∈ xs → xs ≢ []
∈⇒≢[] (here  _) = λ ()
∈⇒≢[] (there _) = λ ()

-- both link directions, as a list
allDirs : List Dir
allDirs = lo ∷ hi ∷ []

-- `lo` and `hi` are distinct, so `allDirs` lists each direction once
allDirs-unique : Unique allDirs
allDirs-unique = ((λ ()) All.∷ All.[]) AP.∷ (All.[] AP.∷ AP.[])

-- every direction occurs in `allDirs`
∈-allDirs : ∀ d → d ∈ allDirs
∈-allDirs lo = here refl
∈-allDirs hi = there (here refl)

-- the enumeration of every (link , direction) endpoint of an `L`-link graph
allEndpoints : (L : ℕ) → List (Fin L × Dir)
allEndpoints L = cartesianProduct (allFin L) allDirs

-- `allEndpoints` lists each endpoint exactly once (a product of two repeat-free lists)
allEndpoints-unique : ∀ L → Unique (allEndpoints L)
allEndpoints-unique L = cartesianProduct⁺ (allFin⁺ L) allDirs-unique

-- every endpoint occurs in `allEndpoints`
∈-allEndpoints : ∀ L (l : Fin L) d → (l , d) ∈ allEndpoints L
∈-allEndpoints _ l d = ∈-cartesianProduct⁺ (∈-allFin l) (∈-allDirs d)

-- "endpoint `ld` belongs to node `n`" is decidable, because `Fin` has a decidable
-- equality; this is the filter predicate the derivation runs on
ownedBy? : ∀ {L k} (ends : Fin L → Fin (suc k) × Fin (suc k)) (n : Fin (suc k))
         → Decidable (λ (ld : Fin L × Dir) → endAtOf ends (proj₁ ld) (proj₂ ld) ≡ n)
ownedBy? ends n ld = endAtOf ends (proj₁ ld) (proj₂ ld) ≟F n

-- the endpoints incident to node `n`, sieved out of the full enumeration
incidentOf : ∀ {L k} (ends : Fin L → Fin (suc k) × Fin (suc k)) (n : Fin (suc k))
           → List (Fin L × Dir)
incidentOf {L} ends n = filter (ownedBy? ends n) (allEndpoints L)

-- filtering preserves repeat-freeness, so `incidentOf` lists each endpoint once
incidentOf-unique : ∀ {L k} (ends : Fin L → Fin (suc k) × Fin (suc k)) (n : Fin (suc k))
                  → Unique (incidentOf ends n)
incidentOf-unique {L} ends n = filter⁺ (ownedBy? ends n) (allEndpoints-unique L)

-- everything the sieve keeps really is an endpoint of `n` (that is what it tested)
incidentOf-sound : ∀ {L k} (ends : Fin L → Fin (suc k) × Fin (suc k)) (n : Fin (suc k))
                 → ∀ l d → (l , d) ∈ incidentOf ends n → endAtOf ends l d ≡ n
incidentOf-sound {L} ends n _ _ mem =
  proj₂ (∈-filter⁻ (ownedBy? ends n) {xs = allEndpoints L} mem)

-- and the sieve drops nothing: every endpoint of `n` is enumerated and passes the test
incidentOf-complete : ∀ {L k} (ends : Fin L → Fin (suc k) × Fin (suc k)) (n : Fin (suc k))
                    → ∀ l d → endAtOf ends l d ≡ n → (l , d) ∈ incidentOf ends n
incidentOf-complete {L} ends n l d eq =
  ∈-filter⁺ (ownedBy? ends n) (∈-allEndpoints L l d) eq

-- build a `Topology` from the link-ends function alone: given that no link is a
-- self-loop and that no node is isolated, `endpointsOf`, `endpoints-sound`,
-- `endpoints-complete` and `endpoints-unique` are all derived
module _ {p : Params} where
  open Params p using (numLinks)

  mkTopology : (k : ℕ)
             → (ends : Fin numLinks → Fin (suc k) × Fin (suc k))
             → (∀ l → proj₁ (ends l) ≢ proj₂ (ends l))
             → (∀ n → Σ[ ld ∈ Fin numLinks × Dir ] (endAtOf ends (proj₁ ld) (proj₂ ld) ≡ n))
             → Topology p
  mkTopology k ends irr inh = record
    { numNodes-1        = k
    ; ends              = ends
    ; ends-irrefl       = irr
    ; endpointsOf       = eps
      -- the laws are stated with an abstract direction `d`, but the record's derived
      -- `endAt` is an extended lambda that only reduces at a CONCRETE direction, so
      -- each law is handed over through a pattern lambda that splits `d` first
    ; endpoints-sound    = λ { n l lo mem → sound n l lo mem
                             ; n l hi mem → sound n l hi mem }
    ; endpoints-complete = λ { n l lo eq → complete n l lo eq
                             ; n l hi eq → complete n l hi eq }
    ; endpoints-unique   = unique
    }
    where
    -- no node is isolated, so its sieved endpoint list has at least one element
    nonEmpty : ∀ n → incidentOf ends n ≢ []
    nonEmpty n = ∈⇒≢[] (incidentOf-complete ends n
                          (proj₁ (proj₁ (inh n))) (proj₂ (proj₁ (inh n))) (proj₂ (inh n)))

    -- the derived `endpointsOf`: the sieved list split into head and tail
    eps : Fin (suc k) → (Fin numLinks × Dir) × List (Fin numLinks × Dir)
    eps n = headTail (incidentOf ends n) (nonEmpty n)

    -- `endpointsList n` is literally the sieved list again
    flat : ∀ n → proj₁ (eps n) ∷ proj₂ (eps n) ≡ incidentOf ends n
    flat n = headTail-flatten (incidentOf ends n) (nonEmpty n)

    -- soundness, transported from the sieved list to the head-plus-tail flattening
    sound : ∀ n l d → (l , d) ∈ (proj₁ (eps n) ∷ proj₂ (eps n)) → endAtOf ends l d ≡ n
    sound n l d mem =
      incidentOf-sound ends n l d (subst (λ xs → (l , d) ∈ xs) (flat n) mem)

    -- completeness, transported the other way
    complete : ∀ n l d → endAtOf ends l d ≡ n → (l , d) ∈ (proj₁ (eps n) ∷ proj₂ (eps n))
    complete n l d eq =
      subst (λ xs → (l , d) ∈ xs) (sym (flat n)) (incidentOf-complete ends n l d eq)

    -- uniqueness, likewise transported
    unique : ∀ n → Unique (proj₁ (eps n) ∷ proj₂ (eps n))
    unique n = subst Unique (sym (flat n)) (incidentOf-unique ends n)
