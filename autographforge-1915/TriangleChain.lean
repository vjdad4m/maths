import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Nat.Lattice
import Lean.Elab.Tactic.Omega

/-! AutoGraphForge normalized row 1915. The elimination-order certificate and
Slater definitions below come from the published row 501/764 proof. -/
namespace TriangleChain
open SimpleGraph Finset
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

/-- Consecutive indices of a simple cycle in either direction, including its closing edge. -/
def consecutive {k : ℕ} (i j : Fin k) : Prop :=
  i.val+1 = j.val ∨ j.val+1 = i.val ∨
    (i.val=0 ∧ j.val+1=k) ∨ (j.val=0 ∧ i.val+1=k)

/-- The usual forbidden-induced-cycle definition of a chordal graph. -/
def Chordal {U : Type*} (G : SimpleGraph U) : Prop :=
  ∀ k, 4 ≤ k → ¬∃ f : Fin k ↪ U, ∀ i j, G.Adj (f i) (f j) ↔ consecutive i j

/-- The two neighbors of an index on an induced cycle of length at least four
are distinct and are not consecutive to one another. -/
private theorem cycle_neighbors {k : ℕ} (hk : 4 ≤ k) (i : Fin k) :
    ∃ p s : Fin k, consecutive i p ∧ consecutive i s ∧ p ≠ s ∧ ¬consecutive p s := by
  let near (a b : ℕ) := a+1=b ∨ b+1=a ∨ (a=0 ∧ b+1=k) ∨ (b=0 ∧ a+1=k)
  have build (a b : ℕ) (ha : a<k) (hb : b<k)
      (check : near i.val a ∧ near i.val b ∧ a≠b ∧ ¬near a b) :
      ∃ p s : Fin k, consecutive i p ∧ consecutive i s ∧ p≠s ∧ ¬consecutive p s :=
    ⟨⟨a,ha⟩,⟨b,hb⟩,check.1,check.2.1,fun e => check.2.2.1 (congrArg Fin.val e),check.2.2.2⟩
  by_cases first : i.val=0
  · exact build (k-1) 1 (by omega) (by omega) (by dsimp [near]; omega)
  by_cases last : i.val+1=k
  · exact build (i.val-1) 0 (by omega) (by omega) (by dsimp [near]; omega)
  · exact build (i.val-1) (i.val+1) (by omega) (by omega) (by dsimp [near]; omega)

/-- An elimination order certifies the forbidden-induced-cycle definition. -/
theorem chordal_of_elimination {U : Type*} (G : SimpleGraph U) (r : U → ℕ)
    (clique : ∀ x y z, G.Adj x y → G.Adj x z → y≠z →
      r y ≤ r x → r z ≤ r x → G.Adj y z) : Chordal G := by
  rintro k hk ⟨f,cyc⟩
  have nonempty : (univ : Finset (Fin k)).Nonempty := ⟨⟨0,by omega⟩,mem_univ _⟩
  obtain ⟨i,_,top⟩ := exists_max_image univ (fun j => r (f j)) nonempty
  obtain ⟨p,s,ip,is,ne,gap⟩ := cycle_neighbors hk i
  exact gap ((cyc p s).mp (clique (f i) (f p) (f s) ((cyc i p).mpr ip) ((cyc i s).mpr is)
    (f.injective.ne ne) (top p (mem_univ _)) (top s (mem_univ _))))

noncomputable def degreesDesc {U : Type*} [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj] :=
  (univ.val.map (fun v => G.degree v)).sort (· ≥ ·)

noncomputable def slater {U : Type*} [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj] :=
  sInf {t | Fintype.card U ≤ t + ((degreesDesc G).take t).sum}

/-- Connected and every vertex has even degree, the Euler criterion used by the source. -/
def Eulerian {U : Type*} [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj] : Prop :=
  G.Connected ∧ ∀ u, G.degree u % 2 = 0


/-- A chain of m+1 triangles has vertex labels from 0 through 2m+2.
The i-th triangle is {2i, 2i+1, 2i+2}. -/
abbrev V (m : ℕ) := Fin (2*m+3)

def edge (i j : ℕ) : Prop :=
  i+1 = j ∨ j+1 = i ∨ (i%2 = 0 ∧ i+2 = j) ∨ (j%2 = 0 ∧ j+2 = i)

instance (i j : ℕ) : Decidable (edge i j) := by unfold edge; infer_instance

def graph (m : ℕ) : SimpleGraph (V m) where
  Adj x y := edge x.val y.val
  symm := by intro x y h; unfold edge at *; tauto
  loopless := by intro x; unfold edge; omega

instance (m : ℕ) : DecidableRel (graph m).Adj := fun x y =>
  inferInstanceAs (Decidable (edge x.val y.val))

theorem chordal (m : ℕ) : Chordal (graph m) := by
  apply chordal_of_elimination _ Fin.val
  intro x y z hxy hxz hne hy hz
  have distinct : y.val ≠ z.val := fun h => hne (Fin.ext h)
  change edge x.val y.val at hxy
  change edge x.val z.val at hxz
  change edge y.val z.val
  unfold edge at *
  omega

theorem connected (m : ℕ) : (graph m).Connected := by
  let zero : V m := ⟨0,by omega⟩
  have reach (n : ℕ) (h : n < 2*m+3) : (graph m).Reachable zero ⟨n,h⟩ := by
    induction n with
    | zero => exact .rfl
    | succ n ih =>
      have hn : n < 2*m+3 := by omega
      have e : (graph m).Adj ⟨n,hn⟩ ⟨n+1,h⟩ := Or.inl rfl
      exact (ih hn).trans e.reachable
  exact ⟨fun x y => (reach x x.isLt).symm.trans (reach y y.isLt)⟩

private def neighborLabels (m i : ℕ) : Finset ℕ :=
  if i = 0 then {1,2} else if i = 2*m+2 then {i-2,i-1} else
  if i%2 = 1 then {i-1,i+1} else {i-2,i-1,i+1,i+2}

private theorem neighbor_labels (m : ℕ) (x : V m) :
    ((graph m).neighborFinset x).map Fin.valEmbedding = neighborLabels m x.val := by
  ext j
  have equivalence : j ∈ ((graph m).neighborFinset x).map Fin.valEmbedding ↔
      j < 2*m+3 ∧ edge x.val j := by
    constructor
    · intro hj
      obtain ⟨v,hv,rfl⟩ := mem_map.mp hj
      exact ⟨v.isLt,((graph m).mem_neighborFinset _ _).mp hv⟩
    · rintro ⟨hj,he⟩
      exact mem_map.mpr ⟨⟨j,hj⟩,((graph m).mem_neighborFinset _ _).mpr he,rfl⟩
  rw [equivalence]
  have hx := x.isLt
  unfold neighborLabels edge
  split <;> (try split) <;> (try split) <;> simp only [mem_insert,mem_singleton] <;> omega

theorem degree_formula (m : ℕ) (x : V m) :
    (graph m).degree x = if x.val = 0 ∨ x.val = 2*m+2 ∨ x.val%2 = 1 then 2 else 4 := by
  have h := congrArg Finset.card (neighbor_labels m x)
  rw [card_map, SimpleGraph.card_neighborFinset_eq_degree] at h
  rw [h]
  have hx := x.isLt
  unfold neighborLabels
  split
  · rename_i z
    simp [z]
  · rename_i nonzero
    split
    · rename_i last
      simp [last, show x.val-2 ≠ x.val-1 by omega]
    · rename_i interior
      split
      · rename_i odd
        simp [odd,show x.val-1 ≠ x.val+1 by omega]
      · rename_i even
        have ge : 2 ≤ x.val := by omega
        simp [nonzero,interior,even,show x.val-2 ≠ x.val-1 by omega,
          show x.val-2 ≠ x.val+1 by omega,show x.val-2 ≠ x.val+2 by omega,
          show x.val-1 ≠ x.val+1 by omega,show x.val-1 ≠ x.val+2 by omega]

theorem eulerian (m : ℕ) : Eulerian (graph m) := by
  refine ⟨connected m,fun x => ?_⟩
  rw [degree_formula]
  split <;> decide

theorem maximum_degree (m : ℕ) (hm : 1 ≤ m) : (graph m).maxDegree = 4 := by
  apply le_antisymm
  · apply SimpleGraph.maxDegree_le_of_forall_degree_le
    intro x
    rw [degree_formula]
    split <;> decide
  · let x : V m := ⟨2,by omega⟩
    have interior : (graph m).degree x = 4 := by
      rw [degree_formula, if_neg]
      change ¬ (2 = 0 ∨ 2 = 2*m+2 ∨ 2%2 = 1)
      omega
    exact interior ▸ (graph m).degree_le_maxDegree x

/-- A maximum-degree bound limits how much each of the first s entries
can contribute to the Slater inequality. -/
theorem slater_capacity {U : Type*} [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj] :
    Fintype.card U ≤ (G.maxDegree+1) * slater G := by
  have prefixBound (l : List ℕ) (k : ℕ) (bound : ∀ d ∈ l, d ≤ G.maxDegree) :
      (l.take k).sum ≤ k * G.maxDegree := by
    induction l generalizing k with
    | nil => simp
    | cons a l ih =>
      cases k with
      | zero => simp
      | succ k =>
        have head := bound a (by simp)
        have tail := ih k (fun d hd => bound d (List.mem_cons_of_mem a hd))
        simp only [List.take_succ_cons, List.sum_cons, Nat.succ_mul]
        omega
  have bounded (d : ℕ) (h : d ∈ degreesDesc G) : d ≤ G.maxDegree := by
    obtain ⟨v,_,rfl⟩ := Multiset.mem_map.mp ((Multiset.mem_sort (· ≥ ·)).mp h)
    exact G.degree_le_maxDegree v
  have attained : Fintype.card U ≤ slater G + ((degreesDesc G).take (slater G)).sum :=
    Nat.sInf_mem (s := {k | Fintype.card U ≤ k + ((degreesDesc G).take k).sum})
      ⟨Fintype.card U,Nat.le_add_right _ _⟩
  have := prefixBound (degreesDesc G) (slater G) bounded
  rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm G.maxDegree]
  omega

theorem family_lower (m : ℕ) (hm : 1 ≤ m) : 2*m+3 ≤ 5 * slater (graph m) := by
  have h := slater_capacity (graph m)
  rw [maximum_degree m hm] at h
  simpa [V] using h

/-- Five triangles give an eleven-vertex witness with exact Slater number three. -/
theorem five_triangles_slater : slater (graph 4) = 3 := by
  have lower := family_lower 4 (by decide)
  have seq : degreesDesc (graph 4) = List.replicate 4 4 ++ List.replicate 7 2 := by
    unfold degreesDesc
    rw [Finset.val_univ_fin, Multiset.map_coe, Multiset.coe_sort]
    have raw : (List.finRange 11).map ((graph 4).degree ·) = [2,2,4,2,4,2,4,2,4,2,2] := by decide
    rw [raw]
    simp [List.mergeSort]
  have upper : slater (graph 4) ≤ 3 := by
    apply Nat.sInf_le (s := {k | Fintype.card (V 4) ≤ k + ((degreesDesc (graph 4)).take k).sum})
    change 11 ≤ 3 + ((degreesDesc (graph 4)).take 3).sum
    rw [seq]
    decide
  omega

theorem row1915_false : ¬ (∀ (U : Type) [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj],
    2 ≤ Fintype.card U → Chordal G → Eulerian G → 2 * slater G ≤ G.maxDegree) := by
  intro claim
  have h := claim (V 4) (graph 4) (by decide) (chordal 4) (eulerian 4)
  rw [five_triangles_slater,maximum_degree 4 (by decide)] at h
  omega

/-- Every chain of at least five triangles violates the catalogue bound. -/
theorem family_violation (m : ℕ) (hm : 4 ≤ m) :
    (graph m).maxDegree < 2 * slater (graph m) := by
  have positive : 1 ≤ m := by omega
  rw [maximum_degree m positive]
  have := family_lower m positive
  omega

theorem unbounded_gap (gap : ℕ) : ∃ m, 2 ≤ Fintype.card (V m) ∧ Chordal (graph m) ∧
    Eulerian (graph m) ∧ (graph m).maxDegree = 4 ∧
    (graph m).maxDegree + gap < 2 * slater (graph m) := by
  let m := 5 * (gap+1)
  have hm : 1 ≤ m := by dsimp [m]; omega
  refine ⟨m,by simp [V],chordal m,eulerian m,maximum_degree m hm,?_⟩
  rw [maximum_degree m hm]
  have := family_lower m hm
  dsimp [m] at this ⊢
  omega

#print axioms chordal
#print axioms eulerian
#print axioms maximum_degree
#print axioms five_triangles_slater
#print axioms row1915_false
#print axioms family_violation
#print axioms unbounded_gap

end TriangleChain
