import BFSOrder189

namespace GraphPathLift
open SimpleGraph

/-- The propositional atom ordering of `graff189-sat/cage.py` v2. -/
inductive CageAtom (n : ℕ) where
  | edge : Fin n → Fin n → CageAtom n
  | two : Fin n → Fin n → CageAtom n
  | common : Fin n → Fin n → Fin n → CageAtom n
  | low : Fin n → CageAtom n
  deriving DecidableEq

def closeLayers (a b : ℕ) : Bool := decide (a ≤ b+1 ∧ b ≤ a+1)

def auxAtoms {n : ℕ} (L : Fin n → ℕ) : List (CageAtom n) :=
  (edgeTable n).flatMap fun (i,j) =>
    .two i j :: ((List.finRange n).filter fun w =>
      decide (w ≠ i ∧ w ≠ j) && closeLayers (L w) (L i) && closeLayers (L w) (L j)).map
      (CageAtom.common i j)

def atomTable {n : ℕ} (L : Fin n → ℕ) : List (CageAtom n) :=
  (edgeTable n).map (fun e => .edge e.1 e.2) ++ auxAtoms L ++
    (List.finRange n).map CageAtom.low

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

def adjCount (i : Fin n) : ℕ := (Finset.univ.filter (G.Adj i)).card

noncomputable def evalAtom : CageAtom n → Bool
  | .edge i j => adjBit G (i,j)
  | .two i j => decide (G.dist i j=2)
  | .common i j w => decide (G.Adj i w ∧ G.Adj j w)
  | .low i => decide (adjCount G i < 3)

noncomputable def cageBit (L : Fin n → ℕ) (k : ℕ) : Bool :=
  (((atomTable L)[k-1]?).map (evalAtom G)).getD false

theorem cageBit_at {L : Fin n → ℕ} {k : ℕ} {p : CageAtom n}
    (h : (atomTable L)[k-1]? = some p) : cageBit G L k = evalAtom G p := by
  simp [cageBit,h]

theorem adjCount_degree (i : Fin n) : adjCount G i = G.degree i := by
  unfold adjCount
  rw [← G.card_neighborFinset_eq_degree]
  congr 1
  ext j
  simp

theorem edge_atom_true {i j : Fin n} : evalAtom G (.edge i j)=true ↔ G.Adj i j :=
  adjBit_eq_true G (i,j)

theorem edge_atom_false {i j : Fin n} : evalAtom G (.edge i j)=false ↔ ¬ G.Adj i j := by
  simp [evalAtom,adjBit]

theorem contact_atom_true {i j w : Fin n} :
    evalAtom G (.common i j w)=true ↔ G.Adj i w ∧ G.Adj j w := by simp [evalAtom]

theorem contact_atom_false {i j w : Fin n} :
    evalAtom G (.common i j w)=false ↔ ¬ (G.Adj i w ∧ G.Adj j w) := by simp [evalAtom]

theorem two_atom_true {i j : Fin n} : evalAtom G (.two i j)=true ↔ G.dist i j=2 := by
  simp [evalAtom]

theorem two_atom_false {i j : Fin n} : evalAtom G (.two i j)=false ↔ G.dist i j≠2 := by
  simp [evalAtom]

theorem low_atom_true {i : Fin n} : evalAtom G (.low i)=true ↔ G.degree i < 3 := by
  simp [evalAtom,adjCount_degree]

theorem low_atom_false {i : Fin n} : evalAtom G (.low i)=false ↔ 3 ≤ G.degree i := by
  simp [evalAtom,adjCount_degree,Nat.not_lt]

/-- Atom values do not depend on orientation of the edge / distance pair. -/
theorem edge_atom_symm (i j : Fin n) : evalAtom G (.edge i j) = evalAtom G (.edge j i) := by
  simp [evalAtom,adjBit,G.adj_comm]

theorem two_atom_symm (i j : Fin n) : evalAtom G (.two i j) = evalAtom G (.two j i) := by
  simp [evalAtom,G.dist_comm]

theorem common_link_clause {i j w : Fin n}
    (h₁ : evalAtom G (.edge i w)=true) (h₂ : evalAtom G (.edge j w)=true)
    (hh : evalAtom G (.common i j w)=false) : False :=
  (contact_atom_false G).mp hh ⟨(edge_atom_true G).mp h₁,(edge_atom_true G).mp h₂⟩

theorem dist_link_clause (hc : G.Connected) {i j w : Fin n} (hij : i ≠ j)
    (h₁ : evalAtom G (.common i j w)=true) (h₂ : evalAtom G (.edge i j)=false)
    (hh : evalAtom G (.two i j)=false) : False := by
  obtain ⟨e₁,e₂⟩ := (contact_atom_true G).mp h₁
  have hbound := G.dist_le (Walk.cons e₁ e₂.symm.toWalk)
  change G.dist i j ≤ 2 at hbound
  have hpos := hc.pos_dist_of_ne hij
  have hno : G.dist i j ≠ 1 := fun h => (edge_atom_false G).mp h₂
    (SimpleGraph.dist_eq_one_iff_adj.mp h)
  exact (two_atom_false G).mp hh (by omega)

theorem two_atMost_clause {i : Fin n} (hmax : (Finset.univ.filter
    (fun j => G.dist i j=2)).card ≤ 3) (L : Finset (Fin n)) (hcard : 4 ≤ L.card)
    (hL : ∀ j ∈ L, evalAtom G (.two i j)=true) : False := by
  have h : L ⊆ Finset.univ.filter (fun j => G.dist i j=2) :=
    fun j hj => Finset.mem_filter.mpr ⟨Finset.mem_univ _,(two_atom_true G).mp (hL j hj)⟩
  have := Finset.card_le_card h
  omega

theorem low_atMost_clause (hmax : (Finset.univ.filter
    (fun j => G.degree j<3)).card ≤ 1) (L : Finset (Fin n)) (hcard : 2 ≤ L.card)
    (hL : ∀ j ∈ L, evalAtom G (.low j)=true) : False := by
  have h : L ⊆ Finset.univ.filter (fun j => G.degree j<3) :=
    fun j hj => Finset.mem_filter.mpr ⟨Finset.mem_univ _,(low_atom_true G).mp (hL j hj)⟩
  have := Finset.card_le_card h
  omega

/-- If Z lists nonedges inside the only possible neighbors S, their counts fit into S. -/
theorem count_zeros_and_neighbors {i : Fin n} (S Z : Finset (Fin n))
    (hS : ∀ j, G.Adj i j → j ∈ S) (hZ : Z ⊆ S)
    (hZero : ∀ j ∈ Z, evalAtom G (.edge i j)=false) :
    G.degree i + Z.card ≤ S.card := by
  let N := Finset.univ.filter (G.Adj i)
  have hn : N.card = G.degree i := adjCount_degree G i
  have hNS : N ⊆ S := fun x hx => hS x (Finset.mem_filter.mp hx).2
  have hDZ : Disjoint N Z := Finset.disjoint_left.mpr (fun x hx hz =>
    (edge_atom_false G).mp (hZero x hz) (Finset.mem_filter.mp hx).2)
  rw [← hn, ← Finset.card_union_of_disjoint hDZ]
  exact Finset.card_le_card (Finset.union_subset hNS hZ)

theorem minDegree_clause {i : Fin n} (S Z : Finset (Fin n)) (hi : 2 ≤ G.degree i)
    (hS : ∀ j, G.Adj i j → j ∈ S) (hZ : Z ⊆ S)
    (hcards : S.card < Z.card + 2)
    (hZero : ∀ j ∈ Z, evalAtom G (.edge i j)=false) : False := by
  have := count_zeros_and_neighbors G S Z hS hZ hZero
  omega

theorem low_link_clause {i : Fin n} (S Z : Finset (Fin n))
    (hS : ∀ j, G.Adj i j → j ∈ S) (hZ : Z ⊆ S)
    (hcards : S.card ≤ Z.card + 2)
    (hZero : ∀ j ∈ Z, evalAtom G (.edge i j)=false)
    (hLow : evalAtom G (.low i)=false) : False := by
  have := count_zeros_and_neighbors G S Z hS hZ hZero
  have := (low_atom_false G).mp hLow
  omega

#print axioms cageBit_at
#print axioms common_link_clause
#print axioms dist_link_clause
#print axioms two_atMost_clause
#print axioms low_atMost_clause
#print axioms minDegree_clause
#print axioms low_link_clause

def candidateNeighbors (L : Fin n → ℕ) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => j ≠ i ∧ L i ≤ L j+1 ∧ L j ≤ L i+1)

def precedingCandidates (L : Fin n → ℕ) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => j < i ∧ L j+1=L i)

omit [DecidableRel G.Adj] in
/-- A same- or neighboring-layer cage position contains every real neighbor. -/
theorem mem_candidateNeighbors (hc : G.Connected) (r : Fin n) (L : Fin n → ℕ)
    (hL : ∀ i, G.dist r i = L i) {i j : Fin n} (e : G.Adj i j) :
    j ∈ candidateNeighbors L i := by
  have hs := adj_distance_steps G hc r e
  rw [hL,hL] at hs
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,e.ne.symm,hs⟩

theorem forbidden_edge_clause (hc : G.Connected) (r : Fin n) (L : Fin n → ℕ)
    (hL : ∀ i, G.dist r i = L i) {i j : Fin n} (hn : 1 + L i < L j)
    (he : evalAtom G (.edge i j)=true) : False := by
  have hs := adj_distance_steps G hc r ((edge_atom_true G).mp he)
  rw [hL,hL] at hs
  omega

theorem root_edge_clause (r : Fin n) (L : Fin n → ℕ)
    (hL : ∀ i, G.dist r i = L i) {j : Fin n} (hj : L j=1)
    (he : evalAtom G (.edge r j)=false) : False := by
  apply (edge_atom_false G).mp he
  apply SimpleGraph.dist_eq_one_iff_adj.mp
  rw [hL,hj]

theorem predecessor_clause (hc : G.Connected) (r : Fin n) (L : Fin n → ℕ)
    (hL : ∀ i, G.dist r i = L i) (hs : ∀ i j, i ≤ j → L i ≤ L j)
    {i : Fin n} (hi : i ≠ r)
    (he : ∀ j ∈ precedingCandidates L i, evalAtom G (.edge i j)=false) : False := by
  obtain ⟨j,e,hj⟩ := exists_preceding_neighbor G hc r hi
  rw [hL,hL] at hj
  have hlt : j < i := lt_of_not_ge (fun hij => by have hh := hs i j hij; omega)
  have hm : j ∈ precedingCandidates L i :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hlt,hj⟩
  exact (edge_atom_false G).mp (he j hm) e

/-- Partially directed DIMACS literal: with assignment x, the clause
is false exactly when all of its listed required values hold. -/
def ClauseFalsified (x : ℕ → Bool) (c : List (ℕ × Bool)) : Prop :=
  ∀ lit ∈ c, x lit.1 = lit.2

/-- A concrete, kernel-reducible atom lookup discharges a cage clause literal. -/
theorem cage_lookup_literal {L : Fin n → ℕ} {c : List (ℕ × Bool)} {k : ℕ} {b : Bool}
    {a : CageAtom n} (hf : ClauseFalsified (cageBit G L) c)
    (hk : (k,b) ∈ c) (ha : (atomTable L)[k-1]? = some a) :
    evalAtom G a = b := (cageBit_at G ha).symm.trans (hf (k,b) hk)

#print axioms predecessor_clause
#print axioms cage_lookup_literal
end GraphPathLift
