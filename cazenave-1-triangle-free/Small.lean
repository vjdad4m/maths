import MainLarge
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace CazenaveOne
open Finset SimpleGraph
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem walk_cross_edge {u v : V} (p : G.Walk u v) (s : Finset V)
    (hu : u ∈ s) (hv : v ∉ s) :
    ∃ a b, s(a,b) ∈ p.edges ∧ a ∈ s ∧ b ∉ s := by
  induction p with
  | nil => exact (hv hu).elim
  | @cons a b c hab p ih =>
      by_cases hb : b ∈ s
      · obtain ⟨i,j,hm,hi,hj⟩ := ih hb hv
        exact ⟨i,j,by simp [hm],hi,hj⟩
      · exact ⟨a,b,by simp,hu,hb⟩

private theorem edges_stay_side {S T : Finset V} (hST : Disjoint S T)
    {u v : V} (p : G.Walk u v) (hu : u ∈ S)
    (hp : ∀ e ∈ p.edges, e ∈ (restrict G S).edgeFinset ∪ (restrict G T).edgeFinset)
    (e : Sym2 V) (he : e ∈ p.edges) :
    e ∈ (restrict G S).edgeFinset := by
  induction p with
  | nil => simp at he
  | @cons a b c hab p ih =>
      have h : s(a,b) ∈ (restrict G S).edgeFinset := by
        rcases Finset.mem_union.mp (hp s(a,b) (by simp)) with hS | hT
        · exact hS
        · have hTa : a ∈ T := ((show (restrict G T).Adj a b from mem_edgeFinset.mp hT).2).1
          exact (Finset.disjoint_left.mp hST hu hTa).elim
      have hb : b ∈ S := ((show (restrict G S).Adj a b from mem_edgeFinset.mp h).2).2
      rcases List.mem_cons.mp he with rfl | he'
      · exact h
      · exact ih hb (fun e h => hp e (by simp [h])) he'



theorem support_cycle_slack (hc : G.Connected) (x : V → ℝ)
    (hx : ∃ v, 0<x v) (hx' : ∃ v, x v<0)
    (hcycle : ∃ u : V, ∃ q : G.Walk u u, q.IsCycle ∧ 4 ≤ q.length)
    (hsmallP : (restrict G (posSet x)).edgeFinset.card ≤ 3)
    (hsmallN : (restrict G (negSet x)).edgeFinset.card ≤ 3) :
    (restrict G (posSet x)).edgeFinset.card+(restrict G (negSet x)).edgeFinset.card+2 ≤
      G.edgeFinset.card := by
  classical
  obtain ⟨u,hu⟩ := hx
  obtain ⟨v,hv⟩ := hx'
  obtain ⟨p⟩ := hc.preconnected u v
  let P := posSet x
  let N := negSet x
  let PS := (restrict G P).edgeFinset
  let NS := (restrict G N).edgeFinset
  have dis : Disjoint PS NS := by
    apply Finset.disjoint_left.mpr
    intro e
    induction e using Sym2.inductionOn with
    | hf a b =>
      simp [PS,NS,SimpleGraph.mem_edgeFinset,restrict,P,N,posSet,negSet]
      intro had hp _ _ hn
      exact ((not_lt_of_ge hp.le) hn).elim
  obtain ⟨a,b,had,pa,npb⟩ := crossing_of_walk G p P
    (by simpa [P,posSet] using hu) (by simpa [P,posSet] using hv.le)
  have heb : s(a,b) ∈ G.edgeFinset := by simpa [SimpleGraph.mem_edgeFinset] using had
  have ho : s(a,b) ∉ PS ∪ NS := by
    simp [PS,NS,SimpleGraph.mem_edgeFinset,restrict,P,N,posSet,negSet]
    have pa' : 0<x a := by simpa [P,posSet] using pa
    have npb' : x b≤0 := by simpa [P,posSet,not_lt] using npb
    exact ⟨fun _ _ => npb',fun _ h => (not_lt_of_ge pa'.le h).elim⟩
  have hs : insert s(a,b) (PS ∪ NS) ⊆ G.edgeFinset := by
    intro e he
    rcases Finset.mem_insert.mp he with rfl | h
    · exact heb
    · rcases Finset.mem_union.mp h with h | h
      · exact mem_edgeFinset.mpr ((SimpleGraph.edgeSet_subset_edgeSet.mpr (restrict_le G P))
          (mem_edgeFinset.mp h))
      · exact mem_edgeFinset.mpr ((SimpleGraph.edgeSet_subset_edgeSet.mpr (restrict_le G N))
          (mem_edgeFinset.mp h))
  by_contra! hbad
  have hcard := Finset.card_le_card hs
  have heqcard : (insert s(a,b) (PS ∪ NS)).card = G.edgeFinset.card := by
    rw [Finset.card_insert_of_not_mem ho,Finset.card_union_of_disjoint dis] at hcard ⊢
    change PS.card + NS.card + 2 > G.edgeFinset.card at hbad
    omega
  have heq := Finset.eq_of_subset_of_card_le hs heqcard.ge
  have hbridge : G.IsBridge s(a,b) := by
    refine (isBridge_iff_adj_and_forall_walk_mem_edges).2 ⟨had,?_⟩
    intro w
    obtain ⟨i,j,hw,hi,hj⟩ := walk_cross_edge G w P pa npb
    have hm : s(i,j) ∈ G.edgeFinset := mem_edgeFinset.mpr (w.edges_subset_edgeSet hw)
    have hm' := Finset.mem_insert.mp (heq.symm ▸ hm)
    rcases hm' with h | h
    · rwa [h] at hw
    · rcases Finset.mem_union.mp h with hP | hN
      · exact (hj ((show (restrict G P).Adj i j from mem_edgeFinset.mp hP).2.2)).elim
      · have hn : x i<0 := by
          simpa [N,negSet] using ((show (restrict G N).Adj i j from mem_edgeFinset.mp hN).2.1)
        exact ((not_lt_of_ge (show 0≤x i from (show 0<x i by simpa [P,posSet] using hi).le)) hn).elim
  obtain ⟨z,q,hq,hq4⟩ := hcycle
  have hnot := (isBridge_iff_adj_and_forall_cycle_not_mem.mp hbridge).2 q hq
  have hgood (e : Sym2 V) (he : e ∈ q.edges) : e ∈ PS ∪ NS := by
    have hm : e ∈ G.edgeFinset := mem_edgeFinset.mpr (q.edges_subset_edgeSet he)
    rcases Finset.mem_insert.mp (heq.symm ▸ hm) with h | h
    · exact (hnot (h ▸ he)).elim
    · exact h
  have hstart : z ∈ P ∨ z ∈ N := by
    cases q with
    | nil => simp at hq4
    | @cons _ b hab p =>
      rcases Finset.mem_union.mp (hgood s(z,b) (by simp)) with hP | hN
      · exact Or.inl ((show (restrict G P).Adj z b from mem_edgeFinset.mp hP).2.1)
      · exact Or.inr ((show (restrict G N).Adj z b from mem_edgeFinset.mp hN).2.1)
  have dc : Disjoint P N := Finset.disjoint_left.mpr (by
    intro i hi hj
    simp [P,N,posSet,negSet] at hi hj
    exact (not_lt_of_ge hi.le) hj)
  have cq : q.edges.toFinset.card = q.length := by
    rw [List.toFinset_card_of_nodup hq.isCircuit.isTrail.edges_nodup, q.length_edges]
  rcases hstart with hp | hn
  · have hs₁ : q.edges.toFinset ⊆ PS := fun e h =>
      edges_stay_side G dc q hp hgood e (List.mem_toFinset.mp h)
    have := Finset.card_le_card hs₁
    change PS.card ≤ 3 at hsmallP
    omega
  · have hs₁ : q.edges.toFinset ⊆ NS := fun e h =>
      edges_stay_side G dc.symm q hn (fun i hi => by rw [Finset.union_comm]; exact hgood i hi)
        e (List.mem_toFinset.mp h)
    have := Finset.card_le_card hs₁
    change NS.card ≤ 3 at hsmallN
    omega

#print axioms support_cycle_slack

theorem triangleFree_orthogonal_cyclic (hf : TriangleFree G) (hc : G.Connected)
    (hcycle : ∃ u : V, ∃ q : G.Walk u u, q.IsCycle ∧ 4 ≤ q.length)
    {t L : ℝ} {x y : V → ℝ} (ht : t≤L) (he : AdjEigen G t x)
    (hE : AdjEigen G L y) (hx : ∃ v, x v≠0) (hy : ∃ v, y v≠0)
    (hort : (∑ v : V,x v*y v)=0) :
    t+1 ≤ randic G := by
  classical
  by_cases hm : 8 ≤ G.edgeFinset.card
  · exact triangleFree_orthogonal_ge8 G hf hc hm ht he hE hx hy hort
  obtain ⟨hp,hn⟩ := orthogonal_subordinate_signs G hc ht he hE hx hy hort
  have hm4 : 4 ≤ G.edgeFinset.card := by
    obtain ⟨u,q,hq,hq4⟩ := hcycle
    have hsub : q.edges.toFinset ⊆ G.edgeFinset := fun e he =>
      mem_edgeFinset.mpr (q.edges_subset_edgeSet (List.mem_toFinset.mp he))
    have hh := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hq.isCircuit.isTrail.edges_nodup, q.length_edges] at hh
    exact hq4.trans hh
  have hm4r : (4:ℝ)≤G.edgeFinset.card := by exact_mod_cast hm4
  apply le_trans ?_ (triangleFree_randic G hf)
  by_cases htp : 0<t
  · let p := (restrict G (posSet x)).edgeFinset.card
    let n := (restrict G (negSet x)).edgeFinset.card
    let m := G.edgeFinset.card
    change ¬ 8≤m at hm
    change 4≤m at hm4
    have hsp : t^2≤(p:ℝ) := positive_support_edges G hf t htp x he hp
    have hsn : t^2≤(n:ℝ) := negative_support_edges G hf t htp x he hn
    have hsum : p+n+1≤m := support_edge_budget G hc x hp hn
    have hsl (hp' : p≤3) (hn' : n≤3) : p+n+2≤m :=
      support_cycle_slack G hc x hp hn hcycle hp' hn'
    by_cases hm5 : m≤5
    · have hmin : p≤1 ∨ n≤1 := by
        by_contra! hh
        have hp' : p≤3 := by omega
        have hn' : n≤3 := by omega
        have h := hsl hp' hn'
        omega
      have ht1 : t^2≤1 := by
        rcases hmin with h | h
        · exact hsp.trans (by exact_mod_cast h)
        · exact hsn.trans (by exact_mod_cast h)
      have hh : t≤1 := by
        have hs := Real.le_sqrt_of_sq_le ht1
        rwa [Real.sqrt_one] at hs
      have hm2 : (2:ℝ)≤Real.sqrt (G.edgeFinset.card : ℝ) :=
        Real.le_sqrt_of_sq_le ((show (2:ℝ)^2≤4 by norm_num).trans hm4r)
      linarith only [hh,hm2]
    · have hm6 : (6:ℝ)≤G.edgeFinset.card := by
        exact_mod_cast (show 6≤m by omega)
      have hmin : p≤2 ∨ n≤2 := by
        by_contra! hh
        have hp' : p≤3 := by omega
        have hn' : n≤3 := by omega
        have h := hsl hp' hn'
        omega
      have ht2 : t^2≤2 := by
        rcases hmin with h | h
        · exact hsp.trans (by exact_mod_cast h)
        · exact hsn.trans (by exact_mod_cast h)
      have hh : t≤17/12 :=
        (Real.le_sqrt_of_sq_le ht2).trans (Real.sqrt_le_iff.2 ⟨by norm_num,by norm_num⟩)
      have hm3 : (29/12:ℝ)≤Real.sqrt (G.edgeFinset.card : ℝ) :=
        Real.le_sqrt_of_sq_le ((show (29/12:ℝ)^2≤6 by norm_num).trans hm6)
      linarith only [hh,hm3]
  · have hSqrt : (1:ℝ)≤Real.sqrt (G.edgeFinset.card : ℝ) :=
      Real.le_sqrt_of_sq_le ((show (1:ℝ)^2≤4 by norm_num).trans hm4r)
    linarith only [htp,hSqrt]

#print axioms triangleFree_orthogonal_cyclic

theorem triangleFree_cycle_ge4 (hf : TriangleFree G) {u : V} (q : G.Walk u u)
    (hq : q.IsCycle) : 4 ≤ q.length := by
  have h3 := hq.three_le_length
  by_contra! h
  have heq : q.length=3 := by omega
  cases q with
  | nil => simp at heq
  | cons hab p =>
    cases p with
    | nil => simp at heq
    | cons hbc p =>
      cases p with
      | nil => simp at heq
      | cons hcd p =>
        have hd := Walk.eq_of_length_eq_zero (p:=p) (by
          simp only [Walk.length_cons] at heq
          omega)
        rw [hd] at hcd
        exact hf _ _ _ hab hcd.symm hbc

theorem triangleFree_orthogonal_not_acyclic (hf : TriangleFree G) (hc : G.Connected)
    (hcycle : ¬ G.IsAcyclic)
    {t L : ℝ} {x y : V → ℝ} (ht : t≤L) (he : AdjEigen G t x)
    (hE : AdjEigen G L y) (hx : ∃ v, x v≠0) (hy : ∃ v, y v≠0)
    (hort : (∑ v : V,x v*y v)=0) :
    t+1 ≤ randic G := by
  unfold SimpleGraph.IsAcyclic at hcycle
  push_neg at hcycle
  obtain ⟨u,q,hq⟩ := hcycle
  exact triangleFree_orthogonal_cyclic G hf hc ⟨u,q,hq,triangleFree_cycle_ge4 G hf q hq⟩
    ht he hE hx hy hort

#print axioms triangleFree_orthogonal_not_acyclic
end CazenaveOne
