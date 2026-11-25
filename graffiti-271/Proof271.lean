/- Reproduce with Lean 4.19.0 and Mathlib v4.19.0: in a project pinned to that tag, run `lake env lean Proof271.lean`. -/

import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Order.Interval.Finset.Nat
import Lean.Elab.Tactic.Omega

open Finset
open scoped BigOperators

namespace Graffiti271

abbrev TotalDominates {V : Type*} (G : SimpleGraph V) (D : Finset V) : Prop :=
  ∀ v, ∃ u ∈ D, G.Adj v u

theorem sum_mono_nat {I : Type*} (s : Finset I) (f g : I → ℕ)
    (h : ∀ i ∈ s, f i ≤ g i) : ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact Nat.add_le_add (h a (Finset.mem_insert_self _ _))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

section General
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

omit [Fintype V] in
theorem dist_step (hc : G.Connected) {root u v : V} (h : G.Adj u v) :
    G.dist root v ≤ G.dist root u + 1 := by
  have hs : G.dist u v = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr h
  simpa [hs] using (hc.dist_triangle (u := root) (v := u) (w := v))

omit [Fintype V] in
theorem walk_intermediate (hc : G.Connected) {root u v : V} (p : G.Walk u v)
    {k : ℕ} (h1 : G.dist root u ≤ k) (h2 : k ≤ G.dist root v) :
    ∃ z : V, G.dist root z = k := by
  induction p with
  | nil => exact ⟨_, Nat.le_antisymm h1 h2⟩
  | @cons u w v adj p ih =>
    by_cases hl : G.dist root w ≤ k
    · exact ih hl h2
    · have hs := dist_step G hc (root := root) adj
      exact ⟨u, by omega⟩

theorem card_le_of_spread (S : Finset ℕ) (l : ℕ)
    (h : ∀ x ∈ S, ∀ y ∈ S, y ≤ x+l) : S.card ≤ l+1 := by
  by_cases hn : S.Nonempty
  · have hm := h (S.min' hn) (S.min'_mem hn) (S.max' hn) (S.max'_mem hn)
    have hs : S ⊆ Finset.Icc (S.min' hn) (S.max' hn) := by
      intro x hx
      exact Finset.mem_Icc.mpr ⟨S.min'_le x hx, S.le_max' x hx⟩
    have hc := Finset.card_le_card hs
    rw [Nat.card_Icc] at hc
    omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp hn]

omit [Fintype V] in
theorem component_distance (D : Finset V)
    (c : (G.induce (D : Set V)).ConnectedComponent) [Fintype c.supp]
    (u v : c.supp) :
    G.dist u.1.1 v.1.1 < Fintype.card c.supp := by
  classical
  obtain ⟨p, hp, hdist⟩ := c.connected_induce_supp.exists_path_of_dist u v
  let f := (SimpleGraph.Embedding.induce (G := G.induce (D : Set V)) c.supp).toHom
  let g := (SimpleGraph.Embedding.induce (G := G) (D : Set V)).toHom
  have hd := SimpleGraph.dist_le (p.map (g.comp f))
  have hl := hp.length_lt
  simp only [SimpleGraph.Walk.length_map] at hd
  exact hd.trans_lt hl

/-- If every vertex of a connected graph has a neighbor in D, its distance
    layers can be covered by the distance intervals of the components of D. -/
theorem dist_of_totalDominates (hc : G.Connected) (D : Finset V)
    (hD : TotalDominates G D) (r s : V) :
    G.dist r s + 1 ≤ D.card + 2*(D.card/2) := by
  classical
  let H := G.induce (D : Set V)
  let Q := H.ConnectedComponent
  letI : Finite Q := Finite.of_surjective H.connectedComponentMk (fun c => c.exists_rep)
  letI : Fintype Q := Fintype.ofFinite Q
  let fs (c : Q) : Finset (↥(D : Set V)) :=
    (Finset.univ : Finset (↥(D : Set V))).filter (fun u => H.connectedComponentMk u = c)
  let S (c : Q) : Finset ℕ :=
    (Finset.univ.filter (fun z : V => ∃ u : c.supp, G.Adj z u.1.1)).image (G.dist r)
  have card_eq (c : Q) : Fintype.card c.supp = (fs c).card := by
    apply Fintype.card_of_subtype
    intro u
    simp [fs, SimpleGraph.ConnectedComponent.mem_supp_iff]
  have cap (c : Q) : (S c).card ≤ (fs c).card+2 := by
    apply card_le_of_spread (S c) ((fs c).card+1)
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨u, hu⟩ := (Finset.mem_filter.mp ha).2
    obtain ⟨v, hv⟩ := (Finset.mem_filter.mp hb).2
    have h1 := dist_step G hc (root := r) hu
    have h2 := dist_step G hc (root := r) hv.symm
    have h3 := hc.dist_triangle (u := r) (v := u.1.1) (w := v.1.1)
    have h4 := component_distance G D c u v
    rw [card_eq] at h4
    omega
  have card_fibers : ∑ c : Q, (fs c).card = D.card := by
    symm
    simpa [fs] using
      (Finset.card_eq_sum_card_fiberwise
        (s := (Finset.univ : Finset (↥(D : Set V)))) (t := (Finset.univ : Finset Q))
        (f := H.connectedComponentMk) (fun _ _ => Finset.mem_univ _))
  have min_fiber (c : Q) : 2 ≤ (fs c).card := by
    obtain ⟨u, hu⟩ := c.exists_rep
    obtain ⟨v, hv, huv⟩ := hD u.1
    let v' : ↥(D : Set V) := ⟨v,hv⟩
    have hc' : H.connectedComponentMk v' = c := by
      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj (show H.Adj u v' from huv)).symm.trans hu
    have hu' : u ∈ fs c := by simpa [fs] using hu
    have hv' : v' ∈ fs c := by simpa [fs] using hc'
    exact Finset.one_lt_card.mpr ⟨u,hu',v',hv',fun h => huv.ne (congrArg Subtype.val h)⟩
  have qcap : 2 * Fintype.card Q ≤ D.card := by
    calc
      _ = ∑ _c : Q, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ c : Q, (fs c).card := sum_mono_nat _ _ _ (fun c _ => min_fiber c)
      _ = _ := card_fibers
  have cover : Finset.range (G.dist r s+1) ⊆ (Finset.univ : Finset Q).biUnion S := by
    intro d hd
    have hi : d ≤ G.dist r s := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
    obtain ⟨w, _⟩ := hc.exists_walk_length_eq_dist r s
    obtain ⟨z, hz⟩ := walk_intermediate G hc (root := r) w
      (by simp [SimpleGraph.dist_self]) hi
    obtain ⟨u, hu, hzu⟩ := hD z
    let u' : ↥(D : Set V) := ⟨u,hu⟩
    let c : Q := H.connectedComponentMk u'
    have hu' : u' ∈ c.supp := by simp [c, SimpleGraph.ConnectedComponent.mem_supp_iff]
    apply Finset.mem_biUnion.mpr
    refine ⟨c, Finset.mem_univ _, Finset.mem_image.mpr ⟨z, ?_, hz⟩⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨⟨u',hu'⟩,hzu⟩⟩
  calc
    G.dist r s+1 = (Finset.range (G.dist r s+1)).card := by simp
    _ ≤ ((Finset.univ : Finset Q).biUnion S).card := Finset.card_le_card cover
    _ ≤ ∑ c : Q, (S c).card := Finset.card_biUnion_le
    _ ≤ ∑ c : Q, ((fs c).card+2) := sum_mono_nat _ _ _ (fun c _ => cap c)
    _ = D.card+2*Fintype.card Q := by
      rw [Finset.sum_add_distrib, card_fibers]
      simp [Nat.mul_comm]
    _ ≤ _ := by omega

noncomputable def nbr (x : V) : Finset V := by
  classical
  exact Finset.univ.filter (G.Adj x)

@[simp] theorem mem_nbr {x y : V} : y ∈ nbr G x ↔ G.Adj x y := by
  classical
  simp [nbr]

def MaximumDegree (x : V) : Prop := ∀ y : V, (nbr G y).card ≤ (nbr G x).card

theorem max_degree_distance_pair (hc : G.Connected) (D : Finset V)
    (hD : TotalDominates G D) (h2 : D.card = 2)
    {x y : V} (hx : MaximumDegree G x) (hy : MaximumDegree G y) :
    G.dist x y ≤ 2 := by
  classical
  obtain ⟨u,v, _, rfl⟩ := Finset.card_eq_two.mp h2
  have hcover : nbr G u ∪ nbr G v = Finset.univ := by
    ext w
    simp only [Finset.mem_union, mem_nbr, Finset.mem_univ, iff_true]
    obtain ⟨z,hz,hwz⟩ := hD w
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact Or.inl hwz.symm
    · exact Or.inr hwz.symm
  have hnm : Fintype.card V ≤ (nbr G x).card + (nbr G y).card := by
    have he := Finset.card_union_le (s := nbr G u) (t := nbr G v)
    rw [hcover, Finset.card_univ] at he
    have h1 := hx u
    have h2' := hy v
    omega
  by_contra! hf
  have hxy : ¬ G.Adj x y := fun hx => by
    have hh := SimpleGraph.dist_eq_one_iff_adj.mpr hx
    omega
  have hdis : Disjoint (nbr G x) (nbr G y) := by
    apply Finset.disjoint_left.mpr
    intro z hzx hzy
    have h1 := SimpleGraph.dist_eq_one_iff_adj.mpr (mem_nbr G |>.mp hzx)
    have h2' := SimpleGraph.dist_eq_one_iff_adj.mpr (mem_nbr G |>.mp hzy).symm
    have ht := hc.dist_triangle (u := x) (v := z) (w := y)
    omega
  have hproper : nbr G x ∪ nbr G y ⊂ Finset.univ := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, ?_⟩
    intro he
    have hm : x ∈ nbr G x ∪ nbr G y := he ▸ Finset.mem_univ x
    have hn := Finset.mem_union.mp hm
    rcases hn with hn | hn
    · exact G.loopless x (mem_nbr G |>.mp hn)
    · exact hxy (mem_nbr G |>.mp hn).symm
  have hcd := Finset.card_lt_card hproper
  rw [Finset.card_union_of_disjoint hdis, Finset.card_univ] at hcd
  omega

theorem perDominatingSet (hc : G.Connected) (D : Finset V)
    (hD : TotalDominates G D) {x y : V} (hx : MaximumDegree G x)
    (hy : MaximumDegree G y) :
    2 * G.dist x y ≤ D.card^2 := by
  have ht : 2 ≤ D.card := by
    obtain ⟨u,hu,_⟩ := hD x
    obtain ⟨v,hv,huv⟩ := hD u
    exact Finset.one_lt_card.mpr ⟨u,hu,v,hv,huv.ne⟩
  have hd := dist_of_totalDominates G hc D hD x y
  by_cases h2 : D.card = 2
  · have h := max_degree_distance_pair G hc D hD h2 hx hy
    rw [h2]
    omega
  by_cases h3 : D.card = 3
  · rw [h3] at hd ⊢
    change 2 * G.dist x y ≤ 9
    omega
  let a := D.card-4
  have ha : D.card=a+4 := by dsimp [a]; omega
  calc
    2*G.dist x y ≤ 8*a+16 := by omega
    _ ≤ a*a+(8*a+16) := by omega
    _ = D.card^2 := by rw [ha, pow_two]; simp only [Nat.add_mul,Nat.mul_add]; omega

noncomputable def totalDominationNumber : ℕ :=
  sInf {k : ℕ | ∃ D : Finset V, TotalDominates G D ∧ D.card = k}

/-- Graffiti.pc #271, in integer form, pointwise over all pairs of maximum-degree vertices.
    For a finite graph this is equivalent to the maximum-distance form of the catalogue. -/
theorem graffiti271 (hc : G.Connected) (hV : 2 ≤ Fintype.card V)
    {x y : V} (hx : MaximumDegree G x) (hy : MaximumDegree G y) :
    2 * G.dist x y ≤ (totalDominationNumber G)^2 := by
  classical
  have hall : TotalDominates G Finset.univ := by
    intro v
    obtain ⟨w, hw⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card V) v
    obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist v w
    have hz : 0 < p.length := by
      rw [hp]
      exact hc.pos_dist_of_ne hw.symm
    exact ⟨p.getVert 1, Finset.mem_univ _, by simpa using p.adj_getVert_succ (i := 0) hz⟩
  have hnon : {k : ℕ | ∃ D : Finset V, TotalDominates G D ∧ D.card = k}.Nonempty :=
    ⟨Fintype.card V, Finset.univ, hall, Finset.card_univ⟩
  obtain ⟨D, hD, hcard⟩ := Nat.sInf_mem hnon
  rw [totalDominationNumber, ← hcard]
  exact perDominatingSet G hc D hD hx hy

/-- Maximum graph distance across the set of maximum-degree vertices. -/
noncomputable def maxDegreeDistance : ℕ := by
  classical
  let M := (Finset.univ : Finset V).filter (MaximumDegree G)
  exact (M.product M).sup (fun p => G.dist p.1 p.2)

theorem graffiti271_max_squared (hc : G.Connected) (hV : 2 ≤ Fintype.card V) :
    2 * maxDegreeDistance G ≤ (totalDominationNumber G)^2 := by
  classical
  have h : maxDegreeDistance G ≤ (totalDominationNumber G)^2 / 2 := by
    unfold maxDegreeDistance
    apply Finset.sup_le
    intro p hp
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
    have ht := graffiti271 G hc hV (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2
    omega
  omega

/-- The nonnegative integer ceiling of a square root, characterized by minimality. -/
noncomputable def ceilSqrt (n : ℕ) : ℕ :=
  Nat.find (show ∃ k : ℕ, n ≤ k^2 from ⟨n, by simpa [pow_two] using Nat.le_mul_self n⟩)

theorem ceilSqrt_spec (n : ℕ) : n ≤ (ceilSqrt n)^2 := by
  unfold ceilSqrt
  exact Nat.find_spec (p := fun k : ℕ => n ≤ k^2) _

theorem ceilSqrt_le {n k : ℕ} (h : n ≤ k^2) : ceilSqrt n ≤ k := Nat.find_le h

/-- The catalogue's exact maximum-and-ceiling form of Graffiti.pc #271. -/
theorem graffiti271_exact (hc : G.Connected) (hV : 2 ≤ Fintype.card V) :
    ceilSqrt (2 * maxDegreeDistance G) ≤ totalDominationNumber G :=
  ceilSqrt_le (graffiti271_max_squared G hc hV)

#print axioms dist_of_totalDominates
#print axioms graffiti271_exact

end General
end Graffiti271
