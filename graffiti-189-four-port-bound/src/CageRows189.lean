import CageAtoms189

namespace GraphPathLift
open SimpleGraph

variable {n : ℕ}

def edgeNorm (i j : Fin n) : CageAtom n :=
  if i ≤ j then .edge i j else .edge j i

def twoNorm (i j : Fin n) : CageAtom n :=
  if i ≤ j then .two i j else .two j i

inductive CageRow (n : ℕ)
  | skip : Fin n → Fin n → CageRow n
  | root : Fin n → CageRow n
  | predecessor : Fin n → List (Fin n) → CageRow n
  | forcesWitness : Fin n → Fin n → Fin n → CageRow n
  | forcesDistanceTwo : Fin n → Fin n → Fin n → CageRow n
  | distanceTwoBudget : Fin n → List (Fin n) → CageRow n
  | twoLow : Fin n → Fin n → CageRow n
  | minDegree : Fin n → List (Fin n) → CageRow n
  | lowFlag : Fin n → List (Fin n) → CageRow n

/-- Each literal stores the value that would *falsify* it, so DIMACS positive
literals store false and DIMACS negative literals store true. Order is preserved. -/
def rowLits (r : Fin n) : CageRow n → List (CageAtom n × Bool)
  | .skip i j => [(edgeNorm i j,true)]
  | .root j => [(edgeNorm r j,false)]
  | .predecessor i js => js.map (fun j => (edgeNorm i j,false))
  | .forcesWitness i j w => [(.common i j w,false),(edgeNorm i w,true),(edgeNorm j w,true)]
  | .forcesDistanceTwo i j w => [(.common i j w,true),(edgeNorm i j,false),(twoNorm i j,false)]
  | .distanceTwoBudget i js => js.map (fun j => (twoNorm i j,true))
  | .twoLow i j => [(.low i,true),(.low j,true)]
  | .minDegree i zs => zs.map (fun j => (edgeNorm i j,false))
  | .lowFlag i zs => (.low i,false) :: zs.map (fun j => (edgeNorm i j,false))

/-- The non-graph hypotheses for each kind of initial SAT input clause. -/
def rowValid (L : Fin n → ℕ) (r : Fin n) : CageRow n → Prop
  | .skip i j => 1 + L i < L j
  | .root j => L j = 1
  | .predecessor i js => i ≠ r ∧ js.toFinset = precedingCandidates L i
  | .forcesWitness _ _ _ => True
  | .forcesDistanceTwo i j _ => i ≠ j
  | .distanceTwoBudget _ js => 4 ≤ js.toFinset.card
  | .twoLow i j => i ≠ j
  | .minDegree i zs => zs.toFinset ⊆ candidateNeighbors L i ∧
      (candidateNeighbors L i).card < zs.toFinset.card + 2
  | .lowFlag i zs => zs.toFinset ⊆ candidateNeighbors L i ∧
      (candidateNeighbors L i).card ≤ zs.toFinset.card + 2

instance (L : Fin n → ℕ) (r : Fin n) (row : CageRow n) : Decidable (rowValid L r row) := by
  cases row <;> dsimp [rowValid] <;> infer_instance

variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

@[simp] theorem eval_edgeNorm (i j : Fin n) : evalAtom G (edgeNorm i j) = evalAtom G (.edge i j) := by
  unfold edgeNorm
  split
  · rfl
  · exact edge_atom_symm G j i

@[simp] theorem eval_twoNorm (i j : Fin n) : evalAtom G (twoNorm i j) = evalAtom G (.two i j) := by
  unfold twoNorm
  split
  · rfl
  · exact two_atom_symm G j i

theorem rowSound (hc : G.Connected) (r : Fin n) (L : Fin n → ℕ)
    (hL : ∀ i, G.dist r i = L i) (hs : ∀ i j, i ≤ j → L i ≤ L j)
    (hMin : ∀ i, 2 ≤ G.degree i)
    (hD2 : ∀ i, (Finset.univ.filter (fun j => G.dist i j=2)).card ≤ 3)
    (hLow : (Finset.univ.filter (fun j => G.degree j<3)).card ≤ 1)
    (row : CageRow n) (hValid : rowValid L r row)
    (hf : ∀ lit ∈ rowLits r row, evalAtom G lit.1 = lit.2) : False := by
  cases row with
  | skip i j =>
    apply forbidden_edge_clause G hc r L hL hValid
    simpa using hf (edgeNorm i j,true) (by simp [rowLits])
  | root j =>
    apply root_edge_clause G r L hL hValid
    simpa using hf (edgeNorm r j,false) (by simp [rowLits])
  | predecessor i js =>
    obtain ⟨hi,hjs⟩ := hValid
    apply predecessor_clause G hc r L hL hs hi
    intro j hj
    rw [← hjs, List.mem_toFinset] at hj
    simpa using hf (edgeNorm i j,false) (List.mem_map_of_mem hj)
  | forcesWitness i j w =>
    apply common_link_clause G (i:=i) (j:=j) (w:=w)
    · simpa using hf (edgeNorm i w,true) (by simp [rowLits])
    · simpa using hf (edgeNorm j w,true) (by simp [rowLits])
    · exact hf (.common i j w,false) (by simp [rowLits])
  | forcesDistanceTwo i j w =>
    apply dist_link_clause G hc (w:=w) hValid
    · exact hf (.common i j w,true) (by simp [rowLits])
    · simpa using hf (edgeNorm i j,false) (by simp [rowLits])
    · simpa using hf (twoNorm i j,false) (by simp [rowLits])
  | distanceTwoBudget i js =>
    apply two_atMost_clause G (hD2 i) js.toFinset hValid
    intro j hj
    rw [List.mem_toFinset] at hj
    simpa using hf (twoNorm i j,true) (List.mem_map_of_mem hj)
  | twoLow i j =>
    have hn : i ≠ j := hValid
    refine low_atMost_clause G hLow {i,j} (by simp [hn]) ?_
    intro k hk
    simp only [Finset.mem_insert,Finset.mem_singleton] at hk
    have h₁ := hf (.low i,true) (by simp [rowLits])
    have h₂ := hf (.low j,true) (by simp [rowLits])
    rcases hk with e|e
    · simpa [e] using h₁
    · simpa [e] using h₂
  | minDegree i zs =>
    obtain ⟨hsub,hcard⟩ := hValid
    apply minDegree_clause G (candidateNeighbors L i) zs.toFinset (hMin i)
      (fun j e => mem_candidateNeighbors G hc r L hL e) hsub hcard
    intro j hj
    rw [List.mem_toFinset] at hj
    simpa using hf (edgeNorm i j,false) (List.mem_map_of_mem hj)
  | lowFlag i zs =>
    obtain ⟨hsub,hcard⟩ := hValid
    apply low_link_clause G (candidateNeighbors L i) zs.toFinset
      (fun j e => mem_candidateNeighbors G hc r L hL e) hsub hcard
    · intro j hj
      rw [List.mem_toFinset] at hj
      simpa using hf (edgeNorm i j,false) (List.mem_cons_of_mem _ (List.mem_map_of_mem hj))
    · exact hf (.low i,false) (by simp [rowLits])

def decodeClause (table : List (CageAtom n)) (c : List (ℕ × Bool)) :
    List (Option (CageAtom n × Bool)) :=
  c.map (fun (k,b) => (table[k-1]?).map (fun atom => (atom,b)))

/-- Lift an initial clause validated by graph-free metadata to the actual graph valuation. -/
theorem rowSound_lookup (hc : G.Connected) (r : Fin n) (L : Fin n → ℕ)
    (hL : ∀ i, G.dist r i = L i) (hs : ∀ i j, i ≤ j → L i ≤ L j)
    (hMin : ∀ i, 2 ≤ G.degree i)
    (hD2 : ∀ i, (Finset.univ.filter (fun j => G.dist i j=2)).card ≤ 3)
    (hLow : (Finset.univ.filter (fun j => G.degree j<3)).card ≤ 1)
    (row : CageRow n) (hValid : rowValid L r row)
    (T : List (CageAtom n)) (hT : T = atomTable L)
    (c : List (ℕ × Bool)) (hDecode : decodeClause T c = (rowLits r row).map some) :
    ¬ ClauseFalsified (cageBit G L) c := by
  intro hf
  apply rowSound G hc r L hL hs hMin hD2 hLow row hValid
  rintro ⟨a,v⟩ ha
  have hm : some (a,v) ∈ decodeClause T c :=
    hDecode.symm ▸ List.mem_map_of_mem ha
  obtain ⟨⟨k,b⟩,hk,hkval⟩ := List.mem_map.mp hm
  cases hlook : T[k-1]? with
  | none => simp [hlook] at hkval
  | some a' =>
    simp only [hlook,Option.map_some,Option.some.injEq,Prod.mk.injEq] at hkval
    obtain ⟨rfl,rfl⟩ := hkval
    exact cage_lookup_literal G hf hk (by rwa [← hT])

#print axioms rowSound
#print axioms rowSound_lookup
end GraphPathLift
