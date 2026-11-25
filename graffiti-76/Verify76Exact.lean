import Std
set_option warningAsError true
set_option linter.unusedVariables false
namespace Graffiti76

/-- The numbers of selected base vertices in the five independent clusters.
If a cluster has at least two selected vertices, at most one vertex can
be selected across the two adjacent clusters: otherwise there is a 4-cycle. -/
theorem baseTreeBound (r₀ r₁ r₂ r₃ r₄ : Nat)
    (h₀ : r₀ ≤ 5) (h₁ : r₁ ≤ 5) (h₂ : r₂ ≤ 5) (h₃ : r₃ ≤ 5) (h₄ : r₄ ≤ 5)
    (hc₀ : 2 ≤ r₀ → r₄ + r₁ ≤ 1)
    (hc₁ : 2 ≤ r₁ → r₀ + r₂ ≤ 1)
    (hc₂ : 2 ≤ r₂ → r₁ + r₃ ≤ 1)
    (hc₃ : 2 ≤ r₃ → r₂ + r₄ ≤ 1)
    (hc₄ : 2 ≤ r₄ → r₃ + r₀ ≤ 1) :
    r₀ + r₁ + r₂ + r₃ + r₄ ≤ 12 := by
  by_cases ha : 2 ≤ r₀ <;>
  by_cases hb : 2 ≤ r₁ <;>
  by_cases hc : 2 ≤ r₂ <;>
  by_cases hd : 2 ≤ r₃ <;>
  by_cases he : 2 ≤ r₄ <;> omega

def graphOrder : Nat := 5 * 5 * 9
def edgeCount : Nat := 5 * (5*5) + 5*5*8
def maxTreeBound : Nat := 12*9

theorem checkedCounterexampleArithmetic :
    2*edgeCount/graphOrder = 2 ∧
    (2*edgeCount/graphOrder)*maxTreeBound < graphOrder := by decide

#print axioms baseTreeBound
#print axioms checkedCounterexampleArithmetic


abbrev Cluster := Fin 5
abbrev Copy := Fin 5
abbrev LeafIdx := Fin 8

inductive Vertex where
  | base : Cluster → Copy → Vertex
  | leaf : Cluster → Copy → LeafIdx → Vertex
deriving DecidableEq

abbrev clusterAdj (i j : Cluster) : Prop := (i.val+1)%5 = j.val ∨ (j.val+1)%5 = i.val

def adj : Vertex → Vertex → Prop
  | .base i _, .base j _ => clusterAdj i j
  | .base i a, .leaf j b _ => i=j ∧ a=b
  | .leaf i a _, .base j b => i=j ∧ a=b
  | .leaf .., .leaf .. => False

def select (S : Vertex → Bool) (v : Vertex) : Prop := S v = true

def noSquare (S : Vertex → Bool) : Prop :=
  ∀ A B C D, A ≠ B → A ≠ C → A ≠ D → B ≠ C → B ≠ D → C ≠ D →
    select S A → select S B → select S C → select S D →
    adj A B → adj B C → adj C D → adj D A → False

inductive Walk (S : Vertex → Bool) : Vertex → Vertex → Prop
  | nil {v} : Walk S v v
  | cons {u v w} : adj u v → select S v → Walk S v w → Walk S u w

def connected (S : Vertex → Bool) : Prop :=
  ∀ a b, select S a → select S b → Walk S a b

def lc {n : Nat} (p : Fin n → Bool) : Nat := ((List.finRange n).filter p).length

theorem lc_bound {n} (p : Fin n → Bool) : lc p ≤ n := by
  simpa [lc] using List.length_filter_le p (List.finRange n)

theorem lc_have {n} (p : Fin n → Bool) (h : 1 ≤ lc p) : ∃ a, p a = true := by
  unfold lc at h
  cases hp : List.filter p (List.finRange n) with
  | nil => simp [hp] at h
  | cons a as =>
    have hm : a ∈ List.filter p (List.finRange n) := by simp [hp]
    exact ⟨a, (List.mem_filter.mp hm).2⟩

theorem fin5_nodup : (List.finRange 5).Nodup := by decide

theorem lc_two (p : Fin 5 → Bool) (h : 2 ≤ lc p) :
    ∃ a b, a ≠ b ∧ p a = true ∧ p b = true := by
  unfold lc at h
  have hn := (List.filter_sublist (p:=p)).nodup fin5_nodup
  cases hp : List.filter p (List.finRange 5) with
  | nil => simp [hp] at h
  | cons a as =>
    cases he : as with
    | nil => simp [hp, he] at h
    | cons b bs =>
      rw [hp,he] at hn
      have hab : a ≠ b := by
        intro heq
        subst b
        exact (List.nodup_cons.mp hn).1 (List.mem_cons_self ..)
      have ham : a ∈ List.filter p (List.finRange 5) := by simp [hp,he]
      have hbm : b ∈ List.filter p (List.finRange 5) := by simp [hp,he]
      exact ⟨a,b,hab,(List.mem_filter.mp ham).2,(List.mem_filter.mp hbm).2⟩

def bc (S : Vertex → Bool) (i : Cluster) : Nat := lc (fun a => S (.base i a))
def fc (S : Vertex → Bool) (i : Cluster) (a : Copy) : Nat :=
  lc (fun k => S (.leaf i a k))

theorem adj_sym {a b : Vertex} (h : adj a b) : adj b a := by
  cases a <;> cases b <;> simp [adj, clusterAdj, eq_comm, or_comm] at *
  all_goals assumption

theorem leaf_must_attach {S} (hc : connected S) {i a k}
    (hsel : select S (.leaf i a k))
    (hother : ∃ v, v ≠ .leaf i a k ∧ select S v) :
    select S (.base i a) := by
  obtain ⟨v,hne,hv⟩ := hother
  have h := hc _ _ hsel hv
  cases h with
  | nil => exact False.elim (hne rfl)
  | cons =>
    rename_i q hs ha hwalk
    cases q with
    | base x b =>
        simp [adj] at ha
        obtain ⟨rfl,rfl⟩ := ha
        exact hs
    | leaf => contradiction

theorem circle_bound {S} (h : noSquare S) {i j k : Cluster}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (aij : clusterAdj i j) (aik : clusterAdj i k)
    (hi : 2 ≤ bc S i) : bc S j + bc S k ≤ 1 := by
  by_cases hb : bc S j + bc S k ≤ 1
  · exact hb
  exfalso
  obtain ⟨a,c,hac,ha,hc⟩ := lc_two (fun a => S (.base i a)) hi
  have finish {x y : Cluster} {b d : Copy}
      (hix : i ≠ x) (hiy : i ≠ y)
      (hbd : Vertex.base x b ≠ Vertex.base y d)
      (aix : clusterAdj i x) (aiy : clusterAdj i y)
      (hsb : select S (.base x b)) (hsd : select S (.base y d)) : False := by
    apply h (.base i a) (.base x b) (.base i c) (.base y d)
    · intro he; exact hix ((Vertex.base.inj he).1)
    · intro he; exact hac ((Vertex.base.inj he).2)
    · intro he; exact hiy ((Vertex.base.inj he).1)
    · intro he; exact hix ((Vertex.base.inj he).1.symm)
    · exact hbd
    · intro he; exact hiy ((Vertex.base.inj he).1)
    · exact ha
    · exact hsb
    · exact hc
    · exact hsd
    · exact aix
    · exact adj_sym (show adj (.base i c) (.base x b) from aix)
    · exact aiy
    · exact adj_sym (show adj (.base i a) (.base y d) from aiy)
  by_cases h₂ : 2 ≤ bc S j
  · obtain ⟨b,d,hbd,hsb,hsd⟩ := lc_two (fun a => S (.base j a)) h₂
    exact finish hij hij (fun he => hbd ((Vertex.base.inj he).2)) aij aij hsb hsd
  by_cases h₃ : 2 ≤ bc S k
  · obtain ⟨b,d,hbd,hsb,hsd⟩ := lc_two (fun a => S (.base k a)) h₃
    exact finish hik hik (fun he => hbd ((Vertex.base.inj he).2)) aik aik hsb hsd
  have hj : 1 ≤ bc S j := by omega
  have hk : 1 ≤ bc S k := by omega
  obtain ⟨b,hsb⟩ := lc_have (fun a => S (.base j a)) hj
  obtain ⟨d,hsd⟩ := lc_have (fun a => S (.base k a)) hk
  exact finish hij hik (fun he => hjk ((Vertex.base.inj he).1)) aij aik hsb hsd

theorem graph_base_bound {S} (h : noSquare S) :
    bc S 0 + bc S 1 + bc S 2 + bc S 3 + bc S 4 ≤ 12 := by
  apply baseTreeBound
  · apply lc_bound
  · apply lc_bound
  · apply lc_bound
  · apply lc_bound
  · apply lc_bound
  · exact circle_bound h (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact circle_bound h (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact circle_bound h (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact circle_bound h (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact circle_bound h (by decide) (by decide) (by decide) (by decide) (by decide)

def family (i : Cluster) (a : Copy) : List Vertex :=
  .base i a :: (List.finRange 8).map (.leaf i a)

def bag (i : Cluster) : List Vertex :=
  (List.finRange 5).flatMap (family i)

def verts : List Vertex := [0,1,2,3,4].flatMap bag

theorem fin_mem_range {n : Nat} (i : Fin n) : i ∈ List.finRange n := by
  have hi : i.val < (List.finRange n).length := by simp
  have hm := List.getElem_mem hi
  rw [List.getElem_finRange] at hm
  have he : Fin.cast List.length_finRange ⟨i.val,hi⟩ = i := by apply Fin.ext; rfl
  rwa [he] at hm

theorem cluster_enum : ([0,1,2,3,4] : List Cluster) = List.finRange 5 := by decide

theorem verts_complete (u : Vertex) : u ∈ verts := by
  unfold verts
  apply List.mem_flatMap.mpr
  cases u with
  | base i a =>
    refine ⟨i, by rw [cluster_enum]; exact fin_mem_range i, ?_⟩
    exact List.mem_flatMap.mpr ⟨a, fin_mem_range a, List.mem_cons_self ..⟩
  | leaf i a k =>
    refine ⟨i, by rw [cluster_enum]; exact fin_mem_range i, ?_⟩
    exact List.mem_flatMap.mpr ⟨a, fin_mem_range a, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨k, fin_mem_range k, rfl⟩)⟩

def orderOf (S : Vertex → Bool) : Nat := (verts.filter S).length

theorem family_bnd {S} {i : Cluster} {a : Copy}
    (h : ∀ k, select S (.leaf i a k) → select S (.base i a)) :
    ((family i a).filter S).length ≤ 9 * (if S (.base i a) then 1 else 0) := by
  cases hh : S (.base i a) with
  | true =>
    have h8 := lc_bound (fun k : LeafIdx => S (.leaf i a k))
    simp only [family, List.filter_cons, if_pos hh, List.length_cons,
      List.filter_map, List.length_map]
    change lc (fun k : LeafIdx => S (.leaf i a k)) + 1 ≤ 9
    omega
  | false =>
    have hl : List.filter (fun k : LeafIdx => S (.leaf i a k)) (List.finRange 8) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro k _ hs
      have hp := h k hs
      simp [select, hh] at hp
    have hn : ¬ S (.base i a) = true := by simp [hh]
    simp only [family, List.filter_cons, if_neg hn, List.filter_map, List.length_map]
    change (List.filter (fun k : LeafIdx => S (.leaf i a k)) (List.finRange 8)).length ≤ 0
    rw [hl]
    decide

theorem flat_bnd {S} {i : Cluster} (as : List Copy)
    (h : ∀ a k, select S (.leaf i a k) → select S (.base i a)) :
    ((as.flatMap (family i)).filter S).length ≤ 9 * (as.filter (fun a => S (.base i a))).length := by
  induction as with
  | nil => simp
  | cons a as ih =>
    have h1 := family_bnd (h a)
    rw [List.flatMap_cons, List.filter_append, List.length_append, List.filter_cons]
    cases hh : S (.base i a)
    · have h0 : ((family i a).filter S).length ≤ 0 := by simpa only [hh, Bool.false_eq_true, if_false, Nat.mul_zero] using h1
      simp only [hh, Bool.false_eq_true, if_false]
      omega
    · have h9 : ((family i a).filter S).length ≤ 9 := by simpa only [if_pos hh, Nat.mul_one] using h1
      simp only [if_pos hh, if_true, List.length_cons]
      omega

set_option maxRecDepth 5000 in
set_option maxHeartbeats 1000000 in
theorem verts_nodup : verts.Nodup := by
  decide

theorem no_two_small {S} (h : ¬ ∃ u v, u ≠ v ∧ select S u ∧ select S v) :
    orderOf S ≤ 1 := by
  have hn := (List.filter_sublist (p:=S)).nodup verts_nodup
  unfold orderOf
  cases hs : verts.filter S with
  | nil => decide
  | cons a as =>
    cases ht : as with
    | nil => simp
    | cons b bs =>
      exfalso
      rw [hs,ht] at hn
      have hab : a ≠ b := by
        intro heq
        subst b
        exact (List.nodup_cons.mp hn).1 (List.mem_cons_self ..)
      have ham : a ∈ verts.filter S := by simp [hs,ht]
      have hbm : b ∈ verts.filter S := by simp [hs,ht]
      exact h ⟨a,b,hab,(List.mem_filter.mp ham).2,(List.mem_filter.mp hbm).2⟩

/-- Any connected vertex selection with no 4-cycle, hence every induced tree,
contains at most 108 vertices of the explicit 225-vertex graph. -/
theorem inducedTree_card_bound {S} (hs : noSquare S) (hc : connected S) :
    orderOf S ≤ 108 := by
  by_cases ht : ∃ u v, u ≠ v ∧ select S u ∧ select S v
  · have hskin (i : Cluster) (a : Copy) (k : LeafIdx)
        (hsel : select S (.leaf i a k)) : select S (.base i a) := by
      apply leaf_must_attach hc hsel
      obtain ⟨u,v,hn,hu,hv⟩ := ht
      by_cases he : u = .leaf i a k
      · exact ⟨v, by simpa [he, ne_comm] using hn, hv⟩
      · exact ⟨u,he,hu⟩
    have hl (i : Cluster) : ((bag i).filter S).length ≤ 9 * bc S i :=
      flat_bnd (List.finRange 5) (hskin i)
    have hbase := graph_base_bound hs
    have h0 := hl 0; have h1 := hl 1; have h2 := hl 2; have h3 := hl 3; have h4 := hl 4
    simp only [orderOf, verts, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.filter_append, List.length_append]
    omega
  · have := no_two_small ht
    omega

def all : Vertex → Bool := fun _ => true

theorem walk_concat {S} {u v w : Vertex} (h1 : Walk S u v) (h2 : Walk S v w) :
    Walk S u w := by
  induction h1 with
  | nil => exact h2
  | cons ha hs _ ih => exact .cons ha hs (ih h2)

theorem walk_reverse {S} {u v : Vertex} (hu : select S u) (h : Walk S u v) :
    Walk S v u := by
  induction h with
  | nil => exact .nil
  | cons ha hs _ ih =>
    exact walk_concat (ih hs) (.cons (adj_sym ha) hu .nil)

theorem all_sel (v : Vertex) : select all v := rfl

theorem all_edge {u v : Vertex} (h : adj u v) : Walk all u v :=
  .cons h (all_sel v) .nil

theorem hub_base (i : Cluster) (a : Copy) : Walk all (.base i a) (.base 0 0) := by
  have h0 : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 := by omega
  rcases h0 with h|h|h|h|h
  · have e : i=0 := Fin.ext h
    subst i
    exact walk_concat (all_edge (v:=Vertex.base 1 0) (by change clusterAdj 0 1; decide))
      (all_edge (by change clusterAdj 1 0; decide))
  · have e : i=1 := Fin.ext h
    subst i
    exact all_edge (by change clusterAdj 1 0; decide)
  · have e : i=2 := Fin.ext h
    subst i
    exact walk_concat (all_edge (v:=Vertex.base 1 0) (by change clusterAdj 2 1; decide))
      (all_edge (by change clusterAdj 1 0; decide))
  · have e : i=3 := Fin.ext h
    subst i
    exact walk_concat (all_edge (v:=Vertex.base 4 0) (by change clusterAdj 3 4; decide))
      (all_edge (by change clusterAdj 4 0; decide))
  · have e : i=4 := Fin.ext h
    subst i
    exact all_edge (by change clusterAdj 4 0; decide)

theorem hub (x : Vertex) : Walk all x (.base 0 0) := by
  cases x with
  | base i a => exact hub_base i a
  | leaf i a k => exact walk_concat (all_edge (v:=Vertex.base i a) ⟨rfl,rfl⟩) (hub_base i a)

theorem graph_connected : connected all := by
  intro u v _ _
  exact walk_concat (hub u) (walk_reverse (all_sel v) (hub v))

theorem graph_no_loops (u : Vertex) : ¬ adj u u := by
  cases u with
  | leaf => simp [adj]
  | base i a =>
    simp only [adj, clusterAdj, or_self]
    have := i.isLt
    omega

theorem leaf_only_neighbor {i a k} {v : Vertex} (h : adj (.leaf i a k) v) :
    v = .base i a := by
  cases v with
  | leaf => contradiction
  | base c d =>
    obtain ⟨rfl,rfl⟩ := h
    rfl

theorem cluster_no_triangles :
    ∀ i j k : Cluster, clusterAdj i j → clusterAdj j k → ¬ clusterAdj k i := by
  decide

theorem graph_triangle_free (u v w : Vertex) (h1 : adj u v) (h2 : adj v w)
    (h3 : adj w u) : False := by
  cases u with
  | leaf i a k =>
     rw [leaf_only_neighbor h1, leaf_only_neighbor (adj_sym h3)] at h2
     exact graph_no_loops _ h2
  | base i a =>
     cases v with
     | leaf j b k =>
         rw [leaf_only_neighbor (adj_sym h1), leaf_only_neighbor h2] at h3
         exact graph_no_loops _ h3
     | base j b =>
         cases w with
         | leaf k c m =>
             rw [leaf_only_neighbor (adj_sym h2), leaf_only_neighbor h3] at h1
             exact graph_no_loops _ h1
         | base k c => exact cluster_no_triangles i j k h1 h2 h3

instance (u v : Vertex) : Decidable (adj u v) := by
  cases u <;> cases v <;> unfold adj <;> infer_instance

set_option maxRecDepth 5000 in
theorem graph_order : verts.length = graphOrder := by decide

def crossEdges (as bs : List Vertex) : Nat :=
  (as.map (fun u => (bs.filter (fun v => decide (adj u v))).length)).sum

def orderedEdges : Nat := crossEdges verts verts

theorem cross_append_left (as bs cs : List Vertex) :
    crossEdges (as ++ bs) cs = crossEdges as cs + crossEdges bs cs := by
  induction as with
  | nil => simp [crossEdges]
  | cons a as ih =>
    simp [crossEdges] at ih ⊢
    omega

theorem cross_append_right (as bs cs : List Vertex) :
    crossEdges as (bs ++ cs) = crossEdges as bs + crossEdges as cs := by
  induction as with
  | nil => simp [crossEdges]
  | cons a as ih =>
    simp [crossEdges, List.filter_append] at ih ⊢
    omega

set_option maxRecDepth 5000 in
set_option maxHeartbeats 1000000 in
private theorem cross_00 : crossEdges (bag 0) (bag 0) = 80 := by decide
set_option maxRecDepth 5000 in
set_option maxHeartbeats 1000000 in
private theorem cross_01 : crossEdges (bag 0) (bag 1) = 25 := by decide
set_option maxRecDepth 5000 in
set_option maxHeartbeats 1000000 in
private theorem cross_02 : crossEdges (bag 0) (bag 2) = 0 := by decide
set_option maxRecDepth 5000 in
set_option maxHeartbeats 1000000 in
private theorem cross_03 : crossEdges (bag 0) (bag 3) = 0 := by decide
set_option maxRecDepth 5000 in
set_option maxHeartbeats 1000000 in
private theorem cross_04 : crossEdges (bag 0) (bag 4) = 25 := by decide
set_option maxRecDepth 5000 in
set_option maxHeartbeats 1000000 in
private theorem cross_10 : crossEdges (bag 1) (bag 0) = 25 := by decide
set_option maxRecDepth 5000 in
set_option maxHeartbeats 1000000 in
private theorem cross_11 : crossEdges (bag 1) (bag 1) = 80 := by decide
set_option maxRecDepth 5000 in
set_option maxHeartbeats 1000000 in
private theorem cross_12 : crossEdges (bag 1) (bag 2) = 25 := by decide
set_option maxRecDepth 5000 in
set_option maxHeartbeats 1000000 in
private theorem cross_13 : crossEdges (bag 1) (bag 3) = 0 := by decide
set_option maxRecDepth 5000 in
set_option maxHeartbeats 1000000 in
private theorem cross_14 : crossEdges (bag 1) (bag 4) = 0 := by decide
set_option maxRecDepth 5000 in
set_option maxHeartbeats 1000000 in
private theorem cross_20 : crossEdges (bag 2) (bag 0) = 0 := by decide
set_option maxRecDepth 5000 in
set_option maxHeartbeats 1000000 in
private theorem cross_21 : crossEdges (bag 2) (bag 1) = 25 := by decide
set_option maxRecDepth 5000 in
set_option maxHeartbeats 1000000 in
private theorem cross_22 : crossEdges (bag 2) (bag 2) = 80 := by decide
set_option maxRecDepth 5000 in
set_option maxHeartbeats 1000000 in
private theorem cross_23 : crossEdges (bag 2) (bag 3) = 25 := by decide
set_option maxRecDepth 5000 in
set_option maxHeartbeats 1000000 in
private theorem cross_24 : crossEdges (bag 2) (bag 4) = 0 := by decide
set_option maxRecDepth 5000 in
set_option maxHeartbeats 1000000 in
private theorem cross_30 : crossEdges (bag 3) (bag 0) = 0 := by decide
set_option maxRecDepth 5000 in
set_option maxHeartbeats 1000000 in
private theorem cross_31 : crossEdges (bag 3) (bag 1) = 0 := by decide
set_option maxRecDepth 5000 in
set_option maxHeartbeats 1000000 in
private theorem cross_32 : crossEdges (bag 3) (bag 2) = 25 := by decide
set_option maxRecDepth 5000 in
set_option maxHeartbeats 1000000 in
private theorem cross_33 : crossEdges (bag 3) (bag 3) = 80 := by decide
set_option maxRecDepth 5000 in
set_option maxHeartbeats 1000000 in
private theorem cross_34 : crossEdges (bag 3) (bag 4) = 25 := by decide
set_option maxRecDepth 5000 in
set_option maxHeartbeats 1000000 in
private theorem cross_40 : crossEdges (bag 4) (bag 0) = 25 := by decide
set_option maxRecDepth 5000 in
set_option maxHeartbeats 1000000 in
private theorem cross_41 : crossEdges (bag 4) (bag 1) = 0 := by decide
set_option maxRecDepth 5000 in
set_option maxHeartbeats 1000000 in
private theorem cross_42 : crossEdges (bag 4) (bag 2) = 0 := by decide
set_option maxRecDepth 5000 in
set_option maxHeartbeats 1000000 in
private theorem cross_43 : crossEdges (bag 4) (bag 3) = 25 := by decide
set_option maxRecDepth 5000 in
set_option maxHeartbeats 1000000 in
private theorem cross_44 : crossEdges (bag 4) (bag 4) = 80 := by decide
theorem graph_edges : orderedEdges = 2 * edgeCount := by
  simp only [orderedEdges, verts, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      cross_append_left, cross_append_right,
cross_00, cross_01, cross_02, cross_03, cross_04, cross_10, cross_11, cross_12, cross_13, cross_14, cross_20, cross_21, cross_22, cross_23, cross_24, cross_30, cross_31, cross_32, cross_33, cross_34, cross_40, cross_41, cross_42, cross_43, cross_44]
  decide

/-- All graph-side hypotheses of the exact candidate and a certified strict
violation for every connected, C4-free induced vertex set. Since every
induced tree is connected and C4-free, this certifies the counterexample. -/
theorem certifiedViolation :
    connected all ∧ (∀ u v w, adj u v → adj v w → adj w u → False) ∧
    orderedEdges / verts.length = 2 ∧
    ∀ S, connected S → noSquare S → (orderedEdges / verts.length) * orderOf S < verts.length := by
  refine ⟨graph_connected,graph_triangle_free,?_,?_⟩
  · rw [graph_edges,graph_order]
    decide
  · intro S hc hs
    have h := inducedTree_card_bound hs hc
    rw [graph_edges, graph_order]
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ h) checkedCounterexampleArithmetic.2

/-- Includes the finite, duplicate-free ambient vertex domain and its simple
undirected-graph structure. -/
theorem graphCertificate :
    verts.length = 225 ∧ verts.Nodup ∧ (∀ u, u ∈ verts) ∧
    (∀ u, ¬ adj u u) ∧ (∀ u v, adj u v → adj v u) ∧
    connected all ∧ (∀ u v w, adj u v → adj v w → adj w u → False) ∧
    orderedEdges = 650 ∧ orderedEdges / verts.length = 2 ∧
    (∀ S, connected S → noSquare S →
      (orderedEdges / verts.length) * orderOf S < verts.length) := by
  exact ⟨graph_order, verts_nodup, verts_complete, graph_no_loops,
    fun _ _ h => adj_sym h, graph_connected, graph_triangle_free,
    graph_edges, certifiedViolation.2.2.1, certifiedViolation.2.2.2⟩

#print axioms graphCertificate

/-- A simple cycle is a cyclic sequence of at least three pairwise distinct vertices. -/
def consecutive : List Vertex → Prop
  | a :: b :: tail => adj a b ∧ consecutive (b :: tail)
  | _ => True

def cycleIn (S : Vertex → Bool) (a : Vertex) (tail : List Vertex) (z : Vertex) : Prop :=
  3 ≤ (a :: tail).length ∧ (a :: tail).Nodup ∧
  (∀ v ∈ a :: tail, select S v) ∧
  consecutive (a :: tail) ∧ (a :: tail).getLast? = some z ∧ adj z a

def acyclic (S : Vertex → Bool) : Prop := ¬ ∃ a tail z, cycleIn S a tail z

def inducedTree (S : Vertex → Bool) : Prop :=
  0 < orderOf S ∧ connected S ∧ acyclic S

theorem acyclic_noSquare {S} (h : acyclic S) : noSquare S := by
  intro a b c d hab hac had hbc hbd hcd ha hb hc hd eab ebc ecd eda
  apply h
  refine ⟨a,[b,c,d],d,by show 3 ≤ 4; decide, ?_, ?_, ?_, rfl, eda⟩
  · simp [List.nodup_cons, hab, hac, had, hbc, hbd, hcd]
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with e|e|e|e <;> subst v <;> assumption
  · exact ⟨eab,ebc,ecd,trivial⟩

def neighbors (v : Vertex) : List Vertex := verts.filter (fun w => decide (adj v w))

/-- Edges between pairs of neighbors count incident triangles, twice before dividing. -/
def triangleCount (v : Vertex) : Nat := crossEdges (neighbors v) (neighbors v) / 2

theorem map_sum_zero {α : Type} {f : α → Nat} (xs : List α)
    (h : ∀ x ∈ xs, f x = 0) : (xs.map f).sum = 0 := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    rw [List.map_cons, List.sum_cons, h a (by simp),
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem validNeighbor {v w} (h : w ∈ neighbors v) : adj v w := by
  have hf := (List.mem_filter.mp h).2
  exact of_decide_eq_true hf

theorem triangleCount_zero (v : Vertex) : triangleCount v = 0 := by
  unfold triangleCount crossEdges
  have hz : ((neighbors v).map (fun u =>
      ((neighbors v).filter (fun w => decide (adj u w))).length)).sum = 0 := by
    apply map_sum_zero
    intro u hu
    have hn : (neighbors v).filter (fun w => decide (adj u w)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro w hw huw
      exact graph_triangle_free v u w (validNeighbor hu)
        (of_decide_eq_true huw) (adj_sym (validNeighbor hw))
    rw [hn]
    rfl
  rw [hz]

def maxTriangleCount : Nat := (verts.map triangleCount).foldl max 0

theorem fold_max_zero {α : Type} {f : α → Nat} (xs : List α)
    (h : ∀ x ∈ xs, f x = 0) : (xs.map f).foldl max 0 = 0 := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    rw [List.map_cons, List.foldl_cons, h a (by simp)]
    exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem maxTriangleCount_zero : maxTriangleCount = 0 :=
  fold_max_zero verts (fun x _ => triangleCount_zero x)

def triangleFrequency : Nat :=
  (verts.filter (fun v => decide (triangleCount v = maxTriangleCount))).length

theorem filter_all_true {α : Type} {f : α → Bool} (xs : List α)
    (h : ∀ x ∈ xs, f x = true) : xs.filter f = xs := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    rw [List.filter_cons, if_pos (h a (by simp)),
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem triangleFrequency_all : triangleFrequency = verts.length := by
  unfold triangleFrequency
  suffices hh : verts.filter (fun v => decide (triangleCount v = maxTriangleCount)) = verts by rw [hh]
  apply filter_all_true
  intro x _
  rw [triangleCount_zero, maxTriangleCount_zero]
  rfl

/-- The exact original lower bound on the largest induced tree, cross-multiplied
by the positive floor of average degree. The largest tree meets a lower bound
iff some induced tree meets it. -/
def conjecture76ForThisGraph : Prop :=
  ∃ S, inducedTree S ∧ triangleFrequency ≤ (orderedEdges / verts.length) * orderOf S

theorem conjecture76_is_false : ¬ conjecture76ForThisGraph := by
  intro h
  obtain ⟨S,⟨_,hco,hac⟩,hnum⟩ := h
  rw [triangleFrequency_all] at hnum
  exact Nat.not_le_of_gt (certifiedViolation.2.2.2 S hco (acyclic_noSquare hac)) hnum

#print axioms conjecture76_is_false

end Graffiti76
