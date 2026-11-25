/- Reproduce with Lean 4.19.0 and Mathlib v4.19.0: run this source with lake env lean. -/
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Order.Interval.Finset.Nat
import Lean.Elab.Tactic.Omega
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Circulant

/- Proof module: Proof271 -/

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

/- Proof module: ConnectedCore -/

open Finset
open SimpleGraph
open Graffiti271

namespace GraffitiCore

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

private theorem finiteComponents {W : Type*} [Finite W] (H : SimpleGraph W) :
    Finite H.ConnectedComponent :=
  Finite.of_surjective H.connectedComponentMk (fun c => c.exists_rep)

noncomputable def componentCount (D : Finset V) : ℕ :=
  @Fintype.card _ (@Fintype.ofFinite _ (finiteComponents (G.induce (D : Set V))))

omit [Fintype V] in
theorem walk_has_change {K : Type*} (f : V → K) {x y : V}
    (p : G.Walk x y) (hxy : f x ≠ f y) :
    ∃ a b, G.Adj a b ∧ f a ≠ f b := by
  classical
  induction p with
  | nil => exact (hxy rfl).elim
  | @cons x z y hadj p ih =>
    by_cases h : f x = f z
    · exact ih (fun he => hxy (h.trans he))
    · exact ⟨x,z,hadj,h⟩

theorem components_le_half (D : Finset V) (hD : TotalDominates G D) :
    componentCount G D ≤ D.card / 2 := by
  classical
  let H := G.induce (D : Set V)
  letI := finiteComponents H
  letI : Fintype H.ConnectedComponent := Fintype.ofFinite _
  let fs (c : H.ConnectedComponent) : Finset (↥(D : Set V)) :=
    Finset.univ.filter (fun u => H.connectedComponentMk u = c)
  have card_fibers : ∑ c : H.ConnectedComponent, (fs c).card = D.card := by
    symm
    simpa [fs] using
      (Finset.card_eq_sum_card_fiberwise
        (s := (Finset.univ : Finset (↥(D : Set V)))) (t := Finset.univ)
        (f := H.connectedComponentMk) (fun _ _ => Finset.mem_univ _))
  have min_fiber (c : H.ConnectedComponent) : 2 ≤ (fs c).card := by
    obtain ⟨u, hu⟩ := c.exists_rep
    obtain ⟨v, hv, huv⟩ := hD u.1
    let v' : ↥(D : Set V) := ⟨v,hv⟩
    have hc' : H.connectedComponentMk v' = c :=
      (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        (show H.Adj u v' from huv)).symm.trans hu
    have hu' : u ∈ fs c := by simpa [fs] using hu
    have hv' : v' ∈ fs c := by simpa [fs] using hc'
    exact Finset.one_lt_card.mpr ⟨u,hu',v',hv',fun h => huv.ne (congrArg Subtype.val h)⟩
  have h : 2 * Fintype.card H.ConnectedComponent ≤ D.card := by
    calc
      _ = ∑ _c : H.ConnectedComponent, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ c : H.ConnectedComponent, (fs c).card :=
        sum_mono_nat _ _ _ (fun c _ => min_fiber c)
      _ = _ := card_fibers
  change Fintype.card H.ConnectedComponent ≤ _
  omega

theorem extend_one (hc : G.Connected) (D : Finset V) (hD : TotalDominates G D)
    (hq : 1 < componentCount G D) :
    ∃ E : Finset V, D ⊆ E ∧ E.card ≤ D.card+2 ∧
      componentCount G E < componentCount G D := by
  classical
  let H := G.induce (D : Set V)
  letI := finiteComponents H
  letI : Fintype H.ConnectedComponent := Fintype.ofFinite _
  have hn : 1 < Fintype.card H.ConnectedComponent := by
    simpa [componentCount, H] using hq
  obtain ⟨c, c', hne⟩ := Fintype.one_lt_card_iff.mp hn
  obtain ⟨x, hx⟩ := c.exists_rep
  obtain ⟨y, hy⟩ := c'.exists_rep
  let dom (v : V) : ↥(D : Set V) :=
    if h : v ∈ D then ⟨v,h⟩ else ⟨(hD v).choose, (hD v).choose_spec.1⟩
  have dom_mem (u : ↥(D : Set V)) : dom u.1 = u := by simp [dom, u.2]
  let cl (v : V) := H.connectedComponentMk (dom v)
  have hcl : cl x.1 ≠ cl y.1 := by
    change H.connectedComponentMk (dom x.1) ≠ H.connectedComponentMk (dom y.1)
    rw [dom_mem, dom_mem]
    change H.connectedComponentMk x = c at hx
    change H.connectedComponentMk y = c' at hy
    rw [hx,hy]
    exact hne
  obtain ⟨p⟩ := hc x.1 y.1
  obtain ⟨a,b,hab,hneq⟩ := walk_has_change G cl p hcl
  let E := insert a (insert b D)
  have hsub : D ⊆ E := by intro z hz; simp [E,hz]
  let J := G.induce (E : Set V)
  letI := finiteComponents J
  letI : Fintype J.ConnectedComponent := Fintype.ofFinite _
  let inc : H →g J := (G.induceHomOfLE (show (D : Set V) ≤ (E : Set V) from hsub)).toHom
  let f : H.ConnectedComponent → J.ConnectedComponent :=
    fun c0 => c0.map inc
  have hpath (v : ↥(E : Set V)) : J.Reachable (inc (dom v.1)) v := by
    by_cases hv : v.1 ∈ D
    · have he : inc (dom v.1) = v := by
        apply Subtype.ext
        change (dom v.1).1 = v.1
        simp [dom, hv]
      rw [he]
    · have hh : G.Adj (dom v.1).1 v.1 := by
        have h := (hD v.1).choose_spec.2.symm
        simpa [dom, hv] using h
      exact (show J.Adj (inc (dom v.1)) v from hh).reachable
  have hsurj : Function.Surjective f := by
    intro k
    obtain ⟨v, hv⟩ := k.exists_rep
    refine ⟨H.connectedComponentMk (dom v.1), ?_⟩
    change J.connectedComponentMk (inc (dom v.1)) = k
    exact (ConnectedComponent.sound (hpath v)).trans hv
  have ha : a ∈ E := by simp [E]
  have hb : b ∈ E := by simp [E]
  let ea : ↥(E : Set V) := ⟨a,ha⟩
  let eb : ↥(E : Set V) := ⟨b,hb⟩
  have hnoninj : ¬ Function.Injective f := by
    intro hi
    apply hneq
    apply hi
    change J.connectedComponentMk (inc (dom a)) = J.connectedComponentMk (inc (dom b))
    exact ConnectedComponent.sound ((hpath ea).trans
      ((show J.Adj ea eb from hab).reachable.trans (hpath eb).symm))
  have hlt := Fintype.card_lt_of_surjective_not_injective f hsurj hnoninj
  refine ⟨E, hsub, ?_, ?_⟩
  · have h1 := Finset.card_insert_le a (insert b D)
    have h2 := Finset.card_insert_le b D
    dsimp [E]
    omega
  · simpa [componentCount, J, H] using hlt

theorem induced_connected_of_componentCount_le_one (D : Finset V)
    (hn : D.Nonempty) (hq : componentCount G D ≤ 1) :
    (G.induce (D : Set V)).Connected := by
  classical
  let H := G.induce (D : Set V)
  letI := finiteComponents H
  letI : Fintype H.ConnectedComponent := Fintype.ofFinite _
  have h : Fintype.card H.ConnectedComponent ≤ 1 := by
    simpa [componentCount, H] using hq
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  obtain ⟨v, hv⟩ := hn
  refine ⟨⟨v,hv⟩, fun w => ConnectedComponent.exact ?_⟩
  exact (Fintype.card_le_one_iff.mp h) _ _

theorem exists_connected_core (hc : G.Connected) (D : Finset V)
    (hD : TotalDominates G D) :
    ∃ E : Finset V, D ⊆ E ∧ (G.induce (E : Set V)).Connected ∧
      E.card ≤ D.card + 2 * (componentCount G D - 1) := by
  classical
  generalize hq : componentCount G D = q
  induction q using Nat.strong_induction_on generalizing D with
  | h q ih =>
    have hn : D.Nonempty := by
      obtain ⟨v⟩ := hc.nonempty
      obtain ⟨u,hu,_⟩ := hD v
      exact ⟨u,hu⟩
    by_cases hsmall : q ≤ 1
    · exact ⟨D, Finset.Subset.refl _, induced_connected_of_componentCount_le_one
        G D hn (hq ▸ hsmall), by omega⟩
    · obtain ⟨E,hsub,hcard,hlt⟩ := extend_one G hc D hD (by omega)
      have hE : TotalDominates G E := by
        intro v
        obtain ⟨u,hu,hvu⟩ := hD v
        exact ⟨u,hsub hu,hvu⟩
      obtain ⟨F,hsubF,hcon,hcardF⟩ := ih _ (by omega) E hE rfl
      have hpos : 0 < componentCount G E := by
        let J := G.induce (E : Set V)
        letI := finiteComponents J
        obtain ⟨v,hv⟩ := hn
        letI : Nonempty J.ConnectedComponent := ⟨J.connectedComponentMk ⟨v,hsub hv⟩⟩
        letI : Fintype J.ConnectedComponent := Fintype.ofFinite _
        change 0 < Fintype.card J.ConnectedComponent
        exact Fintype.card_pos
      exact ⟨F, hsub.trans hsubF, hcon, by omega⟩

#print axioms exists_connected_core
end GraffitiCore

/- Proof module: LeavesCore -/

open Finset SimpleGraph Graffiti271 GraffitiCore
namespace GraffitiLeaves

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

noncomputable def leafSet (T : SimpleGraph V) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => (nbr T v).card = 1)

noncomputable def maxLeaves : ℕ := by
  classical
  exact ((Finset.univ : Finset (SimpleGraph V)).filter
    (fun T => T ≤ G ∧ T.IsTree)).sup (fun T => (leafSet T).card)

theorem leaf_card_le_maxLeaves {T : SimpleGraph V} (hle : T ≤ G) (hT : T.IsTree) :
    (leafSet T).card ≤ maxLeaves G := by
  classical
  unfold maxLeaves
  exact Finset.le_sup (f := fun T => (leafSet T).card) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hle,hT⟩)

omit [Fintype V] in
theorem adj_exists_of_connected {x y : V} (h : G.Connected) (hne : x ≠ y) :
    ∃ w : V, G.Adj x w := by
  obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist x y
  have hz : 0 < p.length := by rw [hp]; exact h.pos_dist_of_ne hne
  exact ⟨p.getVert 1, by simpa using p.adj_getVert_succ (i := 0) hz⟩

/-- Every vertex outside a connected dominating set can simultaneously be a leaf
    of a single spanning tree. -/
theorem complement_card_le_maxLeaves (D : Finset V)
    (hd : TotalDominates G D) (hD : (G.induce (D : Set V)).Connected) :
    Fintype.card V - D.card ≤ maxLeaves G := by
  classical
  let par (v : V) := (hd v).choose
  have hpar (v : V) : par v ∈ D ∧ G.Adj v (par v) := (hd v).choose_spec
  let H : SimpleGraph V :=
    { Adj := fun u v => G.Adj u v ∧
        ((u ∈ D ∧ v ∈ D) ∨ (u ∉ D ∧ par u = v) ∨ (v ∉ D ∧ par v = u))
      symm := by
        intro u v h
        obtain ⟨huv, h | h | h⟩ := h
        · exact ⟨huv.symm, Or.inl h.symm⟩
        · exact ⟨huv.symm, Or.inr (Or.inr h)⟩
        · exact ⟨huv.symm, Or.inr (Or.inl h)⟩
      loopless := fun u h => G.loopless u h.1 }
  let inc : G.induce (D : Set V) →g H :=
    ⟨fun v => v.1, fun {a b} h => ⟨h,Or.inl ⟨a.2,b.2⟩⟩⟩
  let lift (v : V) : ↥(D : Set V) :=
    if h : v ∈ D then ⟨v,h⟩ else ⟨par v,(hpar v).1⟩
  have reach (v : V) : H.Reachable v (lift v).1 := by
    by_cases h : v ∈ D
    · have he : (lift v).1 = v := by simp [lift,h]
      rw [he]
    · have he : (lift v).1 = par v := by simp [lift,h]
      rw [he]
      exact (show H.Adj v (par v) from ⟨(hpar v).2, Or.inr (Or.inl ⟨h,rfl⟩)⟩).reachable
  have hH : H.Connected := by
    have : Nonempty V := ⟨(Classical.choice hD.nonempty).1⟩
    refine ⟨fun u v => ?_⟩
    exact (reach u).trans (((hD (lift u) (lift v)).map inc).trans (reach v).symm)
  obtain ⟨T, hT, ht⟩ := hH.exists_isTree_le
  have hTG : T ≤ G := fun _ _ h => (hT h).1
  have hleaf : (Finset.univ : Finset V) \ D ⊆ leafSet T := by
    intro v hv
    have hn : v ∉ D := (Finset.mem_sdiff.mp hv).2
    have hpne : v ≠ par v := fun h => hn (h ▸ (hpar v).1)
    obtain ⟨z,hz⟩ := adj_exists_of_connected T ht.isConnected hpne
    have single {w : V} (h : T.Adj v w) : w = par v := by
      have h' := (hT h).2
      rcases h' with h' | h' | h'
      · exact (hn h'.1).elim
      · exact h'.2.symm
      · exact (hn (h'.2 ▸ (hpar w).1)).elim
    have hs : nbr T v = {par v} := by
      ext w
      simp only [mem_nbr, Finset.mem_singleton]
      refine ⟨single, fun h => ?_⟩
      rwa [h, ← single hz]
    simp [leafSet, hs]
  have hcount := Finset.card_le_card hleaf
  rw [Finset.card_sdiff (Finset.subset_univ _), Finset.card_univ] at hcount
  exact hcount.trans (leaf_card_le_maxLeaves G hTG ht)

theorem domination_leaves_bound
    (hc : G.Connected) (D : Finset V) (hd : TotalDominates G D) :
    Fintype.card V ≤ maxLeaves G + D.card + 2 * (D.card / 2 - 1) := by
  obtain ⟨E,hsub,hcon,hcard⟩ := exists_connected_core G hc D hd
  have he : TotalDominates G E := by
    intro v
    obtain ⟨u,hu,ha⟩ := hd v
    exact ⟨u,hsub hu,ha⟩
  have ht := complement_card_le_maxLeaves G E he hcon
  have hcc := components_le_half G D hd
  omega

#print axioms domination_leaves_bound
end GraffitiLeaves

/- Proof module: BFS -/

open Finset SimpleGraph Graffiti271 GraffitiLeaves
namespace GraffitiBFS
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

omit [Fintype V] in
theorem one_step_toward (hc : G.Connected) (r v : V) (h : v ≠ r) :
    ∃ z, G.Adj v z ∧ G.dist r z + 1 = G.dist r v := by
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist v r
  have hpos : 0 < p.length := by rw [hp]; exact hc.pos_dist_of_ne h
  have hn : ¬ p.Nil := SimpleGraph.Walk.not_nil_iff_lt_length.mpr hpos
  have h1 : G.Adj v (p.getVert 1) := by simpa using p.adj_getVert_succ (i := 0) hpos
  have h2 := SimpleGraph.dist_le p.tail
  rw [SimpleGraph.dist_comm] at h2
  change G.dist r (p.getVert 1) ≤ p.tail.length at h2
  have h3 := p.length_tail_add_one hn
  rw [hp, SimpleGraph.dist_comm] at h3
  have h4 := dist_step G hc (root := r) h1.symm
  exact ⟨_, h1, by omega⟩

/-- Rooted shortest-path parent relation, producing an actual spanning tree. -/
theorem exists_bfs_tree (hc : G.Connected) (r : V) :
    ∃ (par : V → V) (T : SimpleGraph V),
      T ≤ G ∧ T.IsTree ∧
      (∀ v, v ≠ r → G.dist r (par v) + 1 = G.dist r v) ∧
      (∀ u v, T.Adj u v ↔ (u ≠ r ∧ par u = v) ∨ (v ≠ r ∧ par v = u)) ∧
      nbr G r = nbr T r := by
  classical
  let par (v : V) : V :=
    if h : v = r then r else (one_step_toward G hc r v h).choose
  have props (v : V) (h : v ≠ r) :
      G.Adj v (par v) ∧ G.dist r (par v) + 1 = G.dist r v := by
    simpa [par, h] using (one_step_toward G hc r v h).choose_spec
  let T : SimpleGraph V :=
    { Adj := fun u v => (u ≠ r ∧ par u = v) ∨ (v ≠ r ∧ par v = u)
      symm := fun _ _ => Or.symm
      loopless := by
        intro v h
        have h := h.elim id id
        have e := (props v h.1).2
        rw [h.2] at e
        omega }
  have hsub : T ≤ G := by
    intro u v h
    change (u ≠ r ∧ par u = v) ∨ (v ≠ r ∧ par v = u) at h
    rcases h with ⟨h,e⟩ | ⟨h,e⟩
    · rw [← e]
      exact (props u h).1
    · rw [← e]
      exact (props v h).1.symm
  have treeReach : ∀ v, T.Reachable v r := by
    intro v
    generalize h : G.dist r v = d
    induction d using Nat.strong_induction_on generalizing v with
    | h d ih =>
      by_cases he : v = r
      · rw [he]
      · have hlt : G.dist r (par v) < d := by
          have hp := (props v he).2
          omega
        have had : T.Adj v (par v) := Or.inl ⟨he,rfl⟩
        exact had.reachable.trans (ih _ hlt _ rfl)
  have hconn : T.Connected := (connected_iff_exists_forall_reachable _).mpr
      ⟨r,fun v => (treeReach v).symm⟩
  have edgeImage : T.edgeFinset =
      ((Finset.univ : Finset V).erase r).image (fun v => s(v,par v)) := by
    ext e
    refine Sym2.inductionOn e (fun u v => ?_)
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    change ((u ≠ r ∧ par u = v) ∨ (v ≠ r ∧ par v = u)) ↔ _
    constructor
    · rintro (⟨hu,e⟩ | ⟨hv,e⟩)
      · exact Finset.mem_image.mpr ⟨u, by simp [hu], by rw [e]⟩
      · exact Finset.mem_image.mpr ⟨v, by simp [hv], by rw [e,Sym2.eq_swap]⟩
    · intro h
      obtain ⟨w, hw, he⟩ := Finset.mem_image.mp h
      have hne := (Finset.mem_erase.mp hw).1
      rcases Sym2.eq_iff.mp he with ⟨hu,hparEq⟩ | ⟨hv,hparEq⟩
      · exact Or.inl ⟨by simpa [hu] using hne, by simpa [hu] using hparEq⟩
      · exact Or.inr ⟨by simpa [hv] using hne, by simpa [hv] using hparEq⟩
  have edgeInj : Set.InjOn (fun v => s(v,par v)) (↑((Finset.univ : Finset V).erase r) : Set V) := by
    intro u hu v hv e
    have hu' := (Finset.mem_erase.mp hu).1
    have hv' := (Finset.mem_erase.mp hv).1
    rcases Sym2.eq_iff.mp e with ⟨h,_⟩ | ⟨h,j⟩
    · exact h
    · have p := (props u hu').2
      have q := (props v hv').2
      rw [← h] at q
      rw [j] at p
      omega
  have htree : T.IsTree := by
    apply isTree_iff_connected_and_card.mpr
    refine ⟨hconn, ?_⟩
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card,
      edgeImage, Finset.card_image_of_injOn edgeInj]
    have he := Finset.card_erase_add_one (Finset.mem_univ r)
    simpa using he
  have hnbr : nbr G r = nbr T r := by
    ext v
    simp only [mem_nbr]
    refine ⟨fun ha => ?_,fun h => hsub h⟩
    have hd : G.dist r v = 1 := dist_eq_one_iff_adj.mpr ha
    have he := (props v ha.ne.symm).2
    have hz : G.dist r (par v) = 0 := by omega
    exact Or.inr ⟨ha.ne.symm, (hc.dist_eq_zero_iff.mp hz).symm⟩
  exact ⟨par,T,hsub,htree,fun v h => (props v h).2,fun _ _ => Iff.rfl,hnbr⟩

#print axioms exists_bfs_tree
end GraffitiBFS

/- Proof module: DegreesLeaves -/

open Finset SimpleGraph Graffiti271 GraffitiLeaves GraffitiBFS
open scoped BigOperators
namespace GraffitiDegrees
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

theorem deg_pos (hc : G.Connected) (hn : 2 ≤ Fintype.card V) (v : V) :
    0 < (nbr G v).card := by
  obtain ⟨w,hw⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card V) v
  obtain ⟨z,hz⟩ := adj_exists_of_connected G hc hw.symm
  exact Finset.card_pos.mpr ⟨z, (mem_nbr G).mpr hz⟩

theorem handshaking_nbr [DecidableRel G.Adj] :
    (∑ v : V, (nbr G v).card) = 2 * G.edgeFinset.card := by
  classical
  have he (v : V) : (nbr G v).card = G.degree v := by
    change (nbr G v).card = (G.neighborFinset v).card
    rw [SimpleGraph.neighborFinset_eq_filter]
    congr 1
    ext w
    simp
  simp_rw [he]
  exact SimpleGraph.sum_degrees_eq_twice_card_edges G

theorem tree_count (hT : G.IsTree) (hn : 2 ≤ Fintype.card V) (r : V) :
    2 ≤ (leafSet G).card ∧ (nbr G r).card ≤ (leafSet G).card := by
  classical
  let extra (v : V) : ℕ := if v = r then (nbr G r).card-2 else 0
  let base (v : V) : ℕ := if (nbr G v).card = 1 then 1 else 2
  have hbase (v : V) : base v + extra v ≤ (nbr G v).card := by
    have hv := deg_pos G hT.isConnected hn v
    by_cases he : v = r
    · subst v
      by_cases hh : (nbr G r).card = 1
      · simp [base,extra,hh]
      · simp [base,extra,hh]
        omega
    · by_cases hh : (nbr G v).card = 1
      · simp [base,extra,he,hh]
      · simp [base,extra,he,hh]
        omega
  have extr : (∑ v : V, extra v) = (nbr G r).card-2 := by simp [extra]
  have bs (v : V) : base v = 1 + (if (nbr G v).card ≠ 1 then 1 else 0) := by
    by_cases h : (nbr G v).card = 1 <;> simp [base,h]
  have bfs : (∑ v : V, base v) =
      Fintype.card V + (Fintype.card V - (leafSet G).card) := by
    simp_rw [bs, Finset.sum_add_distrib, Finset.sum_const, Nat.nsmul_eq_mul, mul_one,
      Finset.card_univ, ← Finset.sum_filter]
    have hf : (Finset.univ.filter (fun v => (nbr G v).card ≠ 1)) =
        ((Finset.univ : Finset V) \ leafSet G) := by
      ext v
      simp [leafSet]
    rw [hf, Finset.sum_const, Nat.nsmul_eq_mul, mul_one,
      Finset.card_sdiff (Finset.subset_univ _), Finset.card_univ]
  have hsum : Fintype.card V + (Fintype.card V - (leafSet G).card)
      + ((nbr G r).card-2) ≤ 2 * G.edgeFinset.card := by
    rw [← bfs, ← extr, ← Finset.sum_add_distrib, ← handshaking_nbr G]
    exact sum_mono_nat _ _ _ (fun v _ => hbase v)
  have he := hT.card_edgeFinset
  have hls : (leafSet G).card ≤ Fintype.card V := Finset.card_le_univ _
  omega

theorem maxLeaves_ge_degree (hc : G.Connected) (hn : 2 ≤ Fintype.card V) (v : V) :
    (nbr G v).card ≤ maxLeaves G := by
  obtain ⟨par,T,hT,ht,_,_,hnbr⟩ := exists_bfs_tree G hc v
  rw [hnbr]
  exact (tree_count T ht hn v).2.trans (leaf_card_le_maxLeaves G hT ht)

theorem maxLeaves_ge_two (hc : G.Connected) (hn : 2 ≤ Fintype.card V) :
    2 ≤ maxLeaves G := by
  obtain ⟨v⟩ := hc.nonempty
  obtain ⟨T,hT,ht⟩ := hc.exists_isTree_le
  exact (tree_count T ht hn v).1.trans (leaf_card_le_maxLeaves G hT ht)

#print axioms maxLeaves_ge_degree
end GraffitiDegrees

/- Proof module: Periphery -/

open Finset SimpleGraph Graffiti271 GraffitiLeaves GraffitiDegrees
open scoped BigOperators
namespace GraffitiPeriphery

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

noncomputable def eccentricity (v : V) : ℕ :=
  (Finset.univ : Finset V).sup (G.dist v)

noncomputable def diameter : ℕ := (Finset.univ : Finset V).sup (eccentricity G)

noncomputable def peripheral : Finset V := by
  classical
  exact Finset.univ.filter (fun v => eccentricity G v = diameter G)

noncomputable def peripheralBoundary : Finset V := by
  classical
  exact ((peripheral G).biUnion (nbr G)) \ peripheral G

theorem ecc_bound (x y : V) : G.dist x y ≤ eccentricity G x :=
  Finset.le_sup (f := G.dist x) (Finset.mem_univ y)

theorem diam_bound (x : V) : eccentricity G x ≤ diameter G :=
  Finset.le_sup (f := eccentricity G) (Finset.mem_univ x)

@[simp] theorem mem_peripheral (v : V) :
    v ∈ peripheral G ↔ eccentricity G v = diameter G := by
  classical
  simp [peripheral]

theorem peripheral_card_ge_two (hc : G.Connected) (hn : 2 ≤ Fintype.card V) :
    2 ≤ (peripheral G).card := by
  classical
  obtain ⟨v⟩ := hc.nonempty
  have he : (Finset.univ : Finset V).Nonempty := ⟨v,Finset.mem_univ v⟩
  obtain ⟨x,_,hx⟩ := Finset.exists_mem_eq_sup _ he (eccentricity G)
  obtain ⟨y,_,hy⟩ := Finset.exists_mem_eq_sup _ he (G.dist x)
  have hx' : diameter G = eccentricity G x := hx
  have hy' : eccentricity G x = G.dist x y := hy
  have hxy : x ≠ y := by
    obtain ⟨w,hw⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card V) x
    have h1 := hc.pos_dist_of_ne hw.symm
    have h2 := ecc_bound G x w
    intro he
    have hs : G.dist x y = 0 := by rw [he,SimpleGraph.dist_self]
    omega
  have hD : diameter G ≤ eccentricity G y := by
    rw [hx',hy',SimpleGraph.dist_comm]
    exact ecc_bound G y x
  exact Finset.one_lt_card.mpr ⟨x,(mem_peripheral G x).mpr hx'.symm,
    y,(mem_peripheral G y).mpr (Nat.le_antisymm (diam_bound G y) hD),hxy⟩

theorem boundary_cap (d : ℕ) (hd : ∀ v, (nbr G v).card ≤ d) :
    (peripheralBoundary G).card ≤ d * (peripheral G).card := by
  classical
  have hsub : peripheralBoundary G ⊆ (peripheral G).biUnion (nbr G) := by
    exact Finset.sdiff_subset
  calc
    _ ≤ ((peripheral G).biUnion (nbr G)).card := Finset.card_le_card hsub
    _ ≤ ∑ v ∈ peripheral G, (nbr G v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ peripheral G, d := sum_mono_nat _ _ _ (fun v _ => hd v)
    _ = _ := by simp [Nat.mul_comm]

theorem boundary_disjoint_cap :
    (peripheralBoundary G).card + (peripheral G).card ≤ Fintype.card V := by
  classical
  have hsub : peripheralBoundary G ⊆ (Finset.univ : Finset V) \ peripheral G := by
    intro x hx
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hx).2⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_sdiff (Finset.subset_univ _), Finset.card_univ] at hcard
  have hc : (peripheral G).card ≤ Fintype.card V := Finset.card_le_univ _
  omega

omit [Fintype V] in
theorem tdcard_ge_two (D : Finset V) (hD : TotalDominates G D) (v : V) :
    2 ≤ D.card := by
  obtain ⟨u,hu,_⟩ := hD v
  obtain ⟨w,hw,huw⟩ := hD u
  exact Finset.one_lt_card.mpr ⟨u,hu,w,hw,huw.ne⟩

theorem periphery_for_D (hc : G.Connected) (hn : 2 ≤ Fintype.card V)
    (D : Finset V) (hD : TotalDominates G D)
    (smallDegreeCase : (∀ v, (nbr G v).card ≤ 2) → (peripheralBoundary G).card ≤ D.card) :
    2 * (peripheralBoundary G).card ≤ D.card * maxLeaves G := by
  obtain ⟨v⟩ := hc.nonempty
  have hcard := tdcard_ge_two G D hD v
  have hL := maxLeaves_ge_two G hc hn
  have hN := domination_leaves_bound G hc D hD
  have hB := peripheral_card_ge_two G hc hn
  have hX := boundary_disjoint_cap G
  by_cases he2 : maxLeaves G = 2
  · have hl : ∀ v, (nbr G v).card ≤ 2 := by
      intro v
      simpa [he2] using maxLeaves_ge_degree G hc hn v
    have := smallDegreeCase hl
    rw [he2]
    omega
  by_cases he3 : maxLeaves G = 3
  · have hl : ∀ v, (nbr G v).card ≤ 3 := by
      intro v
      simpa [he3] using maxLeaves_ge_degree G hc hn v
    have := boundary_cap G 3 hl
    rw [he3] at hN ⊢
    by_cases h : D.card % 2 = 0
    · have : D.card = 2*(D.card/2) := by omega
      omega
    · omega
  · let a := D.card-2
    let b := maxLeaves G-4
    have ha : D.card = a+2 := by dsimp [a]; omega
    have hb : maxLeaves G = b+4 := by dsimp [b]; omega
    calc
      2*(peripheralBoundary G).card ≤ 4*a+2*b+8 := by omega
      _ ≤ a*b + (4*a+2*b+8) := by omega
      _ = D.card * maxLeaves G := by rw [ha,hb]; simp only [Nat.add_mul,Nat.mul_add]; omega

theorem exists_min_td (hc : G.Connected) (hn : 2 ≤ Fintype.card V) :
    ∃ D : Finset V, TotalDominates G D ∧ D.card = totalDominationNumber G := by
  have hall : TotalDominates G Finset.univ := by
    intro v
    obtain ⟨w, hw⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card V) v
    obtain ⟨p, hp⟩ := adj_exists_of_connected G hc hw.symm
    exact ⟨p,Finset.mem_univ _,hp⟩
  have hnon : {k : ℕ | ∃ D : Finset V, TotalDominates G D ∧ D.card = k}.Nonempty :=
    ⟨Fintype.card V, Finset.univ, hall, Finset.card_univ⟩
  exact Nat.sInf_mem hnon

#print axioms periphery_for_D
end GraffitiPeriphery

/- Proof module: DegreeTwoClass -/

open Finset SimpleGraph Graffiti271 GraffitiLeaves GraffitiDegrees
namespace GraffitiDegreeTwo
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

omit [Fintype V] in
theorem mem_support_label {a b : V} (p : G.Walk a b) {x : V} (hx : x ∈ p.support) :
    ∃ i : ℕ, i ≤ p.length ∧ p.getVert i = x := by
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem hx
  have hc : i ≤ p.length := by rw [p.length_support] at hi; omega
  refine ⟨i,hc,?_⟩
  have h := p.getVert_eq_support_get? hc
  rw [List.getElem?_eq_getElem hi, he] at h
  exact Option.some.inj h

theorem internal_neighbors [DecidableEq V] {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    {i : ℕ} (hi₀ : 0 < i) (hi : i < p.length)
    (hdeg : (nbr G (p.getVert i)).card ≤ 2) :
    nbr G (p.getVert i) = {p.getVert (i-1),p.getVert (i+1)} := by
  classical
  have hleft : G.Adj (p.getVert i) (p.getVert (i-1)) := by
    have he : i-1+1 = i := by omega
    have h := p.adj_getVert_succ (i := i-1) (by omega)
    rw [he] at h
    exact h.symm
  have hright := p.adj_getVert_succ hi
  have hne : p.getVert (i-1) ≠ p.getVert (i+1) := fun he => by
    have hn := hp.getVert_injOn (by show i-1 ≤ p.length; omega)
      (by show i+1 ≤ p.length; omega) he
    omega
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact (mem_nbr G).mpr hleft
    · exact (mem_nbr G).mpr hright
  · rw [Finset.card_pair hne]
    exact hdeg

theorem degree_some {v w : V} (h : G.Adj v w) (hdeg : (nbr G v).card = 1) :
    nbr G v = {w} := by
  classical
  symm
  apply Finset.eq_of_subset_of_card_le
  · simpa using (mem_nbr G).mpr h
  · simp [hdeg]

private theorem support_closed_of_ends_leaves (T : SimpleGraph V)
    {a b : V} (hne : a ≠ b) (p : T.Walk a b) (hp : p.IsPath)
    (hda : (nbr T a).card = 1) (hdb : (nbr T b).card = 1)
    (hdeg : ∀ v, (nbr T v).card ≤ 2) :
    ∀ u ∈ p.support, ∀ v, T.Adj u v → v ∈ p.support := by
  classical
  have hpos : 0 < p.length := by
    cases p with
    | nil => exact (hne rfl).elim
    | cons => simp
  intro u hu v huv
  obtain ⟨i,hil,rfl⟩ := mem_support_label T p hu
  by_cases hi0 : i=0
  · subst i
    rw [p.getVert_zero] at huv
    have hadj : T.Adj a (p.getVert 1) := by simpa using p.adj_getVert_succ (i := 0) hpos
    have hm := (mem_nbr T).mpr huv
    rw [degree_some T hadj hda, Finset.mem_singleton] at hm
    rw [hm]; exact p.getVert_mem_support _
  by_cases hie : i=p.length
  · rw [hie,p.getVert_length] at huv
    have hadj : T.Adj b (p.getVert (p.length-1)) := by
      have h := p.adj_getVert_succ (i := p.length-1) (by omega)
      have hl : p.length-1+1=p.length := by omega
      rw [hl,p.getVert_length] at h
      exact h.symm
    have hm := (mem_nbr T).mpr huv
    rw [degree_some T hadj hdb, Finset.mem_singleton] at hm
    rw [hm]; exact p.getVert_mem_support _
  have hm := (mem_nbr T).mpr huv
  rw [internal_neighbors T p hp (by omega) (by omega) (hdeg _)] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl <;> exact p.getVert_mem_support _

private theorem path_span (T : SimpleGraph V) (hT : T.Connected)
    {a b : V} (hne : a ≠ b) (p : T.Walk a b) (hp : p.IsPath)
    (hda : (nbr T a).card = 1) (hdb : (nbr T b).card = 1)
    (hdeg : ∀ v, (nbr T v).card ≤ 2) :
    ∀ v, v ∈ p.support := by
  have hclose := support_closed_of_ends_leaves T hne p hp hda hdb hdeg
  have hpath : ∀ {u v : V}, T.Walk u v → u ∈ p.support → v ∈ p.support := by
    intro u v q
    induction q with
    | nil => exact id
    | cons hadj q ih =>
      intro h
      exact ih (hclose _ h _ hadj)
  intro v
  obtain ⟨q⟩ := hT a v
  apply hpath q
  have hh := p.getVert_mem_support 0
  rw [p.getVert_zero] at hh
  exact hh

/-- Exact indexed classification: a path with a possible closing edge. -/
theorem degree_two_indexed (hc : G.Connected) (hn : 2 ≤ Fintype.card V)
    (hd : ∀ v, (nbr G v).card ≤ 2) :
    ∃ (m : ℕ) (_h : 1 ≤ m) (e : Fin (m+1) ≃ V) (wrap : Prop),
      ∀ i j : Fin (m+1), G.Adj (e i) (e j) ↔
        i.val+1=j.val ∨ j.val+1=i.val ∨
        (wrap ∧ ((i.val=0 ∧ j.val=m) ∨ (j.val=0 ∧ i.val=m))) := by
  classical
  obtain ⟨T,hTG,hT⟩ := hc.exists_isTree_le
  obtain ⟨r⟩ := hc.nonempty
  have hl := (tree_count T hT hn r).1
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp hl
  have hda : (nbr T a).card = 1 := (Finset.mem_filter.mp ha).2
  have hdb : (nbr T b).card = 1 := (Finset.mem_filter.mp hb).2
  have hdt : ∀ v, (nbr T v).card ≤ 2 := by
    intro v
    apply le_trans (Finset.card_le_card (t := nbr G v) ?_) (hd v)
    intro u hu
    exact (mem_nbr G).mpr (hTG ((mem_nbr T).mp hu))
  obtain ⟨p,hp,heq⟩ := hT.isConnected.exists_path_of_dist a b
  have hpos : 0 < p.length := by rw [heq]; exact hT.isConnected.pos_dist_of_ne hab
  let f : Fin (p.length+1) → V := fun i => p.getVert i.val
  have hfi : Function.Injective f := by
    intro i j he
    apply Fin.ext
    exact hp.getVert_injOn (by show i.val ≤ p.length; omega)
      (by show j.val ≤ p.length; omega) he
  have hfs : Function.Surjective f := by
    intro v
    obtain ⟨i,hi,he⟩ :=
      mem_support_label T p (path_span T hT.isConnected hab p hp hda hdb hdt v)
    exact ⟨⟨i,by omega⟩,he⟩
  let e : Fin (p.length+1) ≃ V := Equiv.ofBijective f ⟨hfi,hfs⟩
  let wrap := G.Adj a b
  refine ⟨p.length,hpos,e,wrap,?_⟩
  intro i j
  change G.Adj (p.getVert i.val) (p.getVert j.val) ↔ _
  have hli : i.val ≤ p.length := by omega
  have hlj : j.val ≤ p.length := by omega
  have same {k l : ℕ} (hk : k ≤ p.length) (hl : l ≤ p.length)
      (he : p.getVert k = p.getVert l) : k = l := hp.getVert_injOn hk hl he
  have hcG : ∀ {k : ℕ}, k < p.length → G.Adj (p.getVert k) (p.getVert (k+1)) :=
    fun h => hTG (p.adj_getVert_succ h)
  have hv {k : ℕ} (hk : k ≤ p.length) (h0 : k ≠ 0) (hm : k ≠ p.length) {l : ℕ}
      (hl : l ≤ p.length) (ha : G.Adj (p.getVert k) (p.getVert l)) :
      k+1 = l ∨ l+1 = k := by
    have hleft : G.Adj (p.getVert k) (p.getVert (k-1)) := by
      have hh := hcG (k := k-1) (by omega)
      have he : k-1+1=k := by omega
      rw [he] at hh
      exact hh.symm
    have hright := hcG (k := k) (by omega)
    have hne : p.getVert (k-1) ≠ p.getVert (k+1) := fun he => by
      have ht := same (k := k-1) (l := k+1) (by omega) (by omega) he
      omega
    have hpair : nbr G (p.getVert k) = {p.getVert (k-1),p.getVert (k+1)} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro v hv
        simp only [Finset.mem_insert,Finset.mem_singleton] at hv
        rcases hv with rfl | rfl
        · exact (mem_nbr G).mpr hleft
        · exact (mem_nbr G).mpr hright
      · rw [Finset.card_pair hne]
        exact hd _
    have hmem := (mem_nbr G).mpr ha
    rw [hpair] at hmem
    simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · have he := same hl (l := k-1) (by omega) h
      omega
    · have he := same hl (l := k+1) (by omega) h
      omega
  constructor
  · intro ha
    by_cases hi : i.val=0 ∨ i.val=p.length
    · by_cases hj : j.val=0 ∨ j.val=p.length
      · rcases hi with hi | hi <;> rcases hj with hj | hj
        · rw [hi,hj] at ha
          exact (G.loopless _ ha).elim
        · rw [hi,hj,p.getVert_zero,p.getVert_length] at ha
          exact Or.inr (Or.inr ⟨ha,Or.inl ⟨hi,hj⟩⟩)
        · rw [hi,hj,p.getVert_zero,p.getVert_length] at ha
          exact Or.inr (Or.inr ⟨ha.symm,Or.inr ⟨hj,hi⟩⟩)
        · rw [hi,hj] at ha
          exact (G.loopless _ ha).elim
      · have hr := hv hlj (fun hh => hj (Or.inl hh)) (fun hh => hj (Or.inr hh)) hli ha.symm
        exact hr.symm.imp_right Or.inl
    · have hr := hv hli (fun hh => hi (Or.inl hh)) (fun hh => hi (Or.inr hh)) hlj ha
      exact hr.imp_right Or.inl
  · rintro (h | h | ⟨h,(⟨hi,hj⟩ | ⟨hj,hi⟩)⟩)
    · rw [← h]; exact hcG (by omega)
    · rw [← h]; exact (hcG (by omega)).symm
    · simpa [hi,hj,p.getVert_zero,p.getVert_length] using h
    · simpa [hi,hj,p.getVert_zero,p.getVert_length] using (show G.Adj a b from h).symm

private theorem cycle_adj_linear {m : ℕ} (hm : 1 ≤ m) (i j : Fin (m+1)) :
    (cycleGraph (m+1)).Adj i j ↔
      i.val+1=j.val ∨ j.val+1=i.val ∨
        ((i.val=0 ∧ j.val=m) ∨ (j.val=0 ∧ i.val=m)) := by
  wlog h : i.val ≤ j.val generalizing i j
  · rw [show (cycleGraph (m+1)).Adj i j ↔ (cycleGraph (m+1)).Adj j i from
          ⟨fun e => e.symm, fun e => e.symm⟩, this j i (by omega)]
    tauto
  by_cases he : i=j
  · subst j
    have hf : ¬(cycleGraph (m+1)).Adj i i := (cycleGraph (m+1)).loopless i
    simp only [hf, false_iff]
    omega
  have hne : i.val ≠ j.val := fun hp => he (Fin.ext hp)
  have hj : (j-i).val = j.val-i.val := Fin.sub_val_of_le (show i ≤ j from h)
  have hi : (i-j).val = m+1-j.val+i.val := by
    rw [Fin.sub_def]
    simp only
    apply Nat.mod_eq_of_lt
    omega
  rw [cycleGraph_adj',hi,hj]
  omega

theorem degree_two_path_or_cycle (hc : G.Connected) (hn : 2 ≤ Fintype.card V)
    (hd : ∀ v, (nbr G v).card ≤ 2) :
    ∃ m : ℕ, 1 ≤ m ∧
      (Nonempty (G ≃g pathGraph (m+1)) ∨ Nonempty (G ≃g cycleGraph (m+1))) := by
  classical
  obtain ⟨m,hm,e,w,he⟩ := degree_two_indexed G hc hn hd
  refine ⟨m,hm,?_⟩
  by_cases hw : w
  · right
    let iso : cycleGraph (m+1) ≃g G :=
      { toEquiv := e
        map_rel_iff' := by
          intro i j
          rw [he,cycle_adj_linear hm]
          simp [hw] }
    exact ⟨iso.symm⟩
  · left
    let iso : pathGraph (m+1) ≃g G :=
      { toEquiv := e
        map_rel_iff' := by
          intro i j
          rw [he,pathGraph_adj]
          simp [hw] }
    exact ⟨iso.symm⟩

#print axioms degree_two_path_or_cycle
end GraffitiDegreeTwo

/- Proof module: Formal259 -/

set_option warningAsError true
set_option linter.unusedSectionVars false
noncomputable section
open Finset SimpleGraph Graffiti271 GraffitiLeaves GraffitiDegrees
open scoped BigOperators
namespace Graffiti259
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

noncomputable def maxDegreeSet : Finset V := by
  classical
  exact Finset.univ.filter (MaximumDegree G)

@[simp] theorem mem_maxDegreeSet (v : V) :
    v ∈ maxDegreeSet G ↔ MaximumDegree G v := by
  classical
  simp [maxDegreeSet]

noncomputable def boundary : Finset V := by
  classical
  exact ((maxDegreeSet G).biUnion (nbr G)) \ maxDegreeSet G

theorem boundary_cap (d : ℕ) (hd : ∀ v, (nbr G v).card ≤ d) :
    (boundary G).card ≤ d * (maxDegreeSet G).card := by
  classical
  have hs : boundary G ⊆ (maxDegreeSet G).biUnion (nbr G) := Finset.sdiff_subset
  calc
    _ ≤ ((maxDegreeSet G).biUnion (nbr G)).card := Finset.card_le_card hs
    _ ≤ ∑ v ∈ maxDegreeSet G, (nbr G v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ maxDegreeSet G, d := sum_mono_nat _ _ _ (fun v _ => hd v)
    _ = _ := by simp [Nat.mul_comm]

theorem boundary_disjoint_cap :
    (boundary G).card + (maxDegreeSet G).card ≤ Fintype.card V := by
  classical
  have hs : boundary G ⊆ (Finset.univ : Finset V) \ maxDegreeSet G := by
    intro v hv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,(Finset.mem_sdiff.mp hv).2⟩
  have hX := Finset.card_le_card hs
  rw [Finset.card_sdiff (Finset.subset_univ _), Finset.card_univ] at hX
  have hM : (maxDegreeSet G).card ≤ Fintype.card V := Finset.card_le_univ _
  omega

theorem degree_iso {W : Type*} [Fintype W] {H : SimpleGraph W} (e : G ≃g H) (v : V) :
    (nbr H (e v)).card = (nbr G v).card := by
  apply Nat.le_antisymm
  · refine Finset.card_le_card_of_injOn (fun w => e.symm w) (fun w hw => ?_) (fun a _ b _ h => e.symm.injective h)
    have h := (mem_nbr H).mp hw
    apply (mem_nbr G).mpr
    apply e.map_adj_iff.mp
    simpa using h
  · refine Finset.card_le_card_of_injOn (fun w => e w) (fun w hw => ?_) (fun a _ b _ h => e.injective h)
    exact (mem_nbr H).mpr (e.map_adj_iff.mpr ((mem_nbr G).mp hw))

theorem inner_path_degree {n} (v : Fin n) (hlo : 0 < v.val) (hhi : v.val+1 < n) :
    2 ≤ (nbr (pathGraph n) v).card := by
  let a : Fin n := ⟨v.val-1, by omega⟩
  let b : Fin n := ⟨v.val+1, hhi⟩
  have ha : a.val = v.val-1 := rfl
  have hb : b.val = v.val+1 := rfl
  apply Finset.one_lt_card.mpr
  exact ⟨a,(mem_nbr _).mpr (pathGraph_adj.mpr (Or.inr (by omega))),
    b,(mem_nbr _).mpr (pathGraph_adj.mpr (Or.inl (by omega))),
    (fun h => by have hh := congrArg Fin.val h; omega)⟩

theorem cycle_degree_constant {n} (a b : Fin (n+1)) :
    (nbr (cycleGraph (n+1)) a).card = (nbr (cycleGraph (n+1)) b).card := by
  let d := b-a
  let e : cycleGraph (n+1) ≃g cycleGraph (n+1) :=
    { toEquiv := Equiv.addRight d
      map_rel_iff' := SimpleGraph.circulantGraph_adj_translate }
  have h : e a = b := by
    change a + (b-a) = b
    rw [add_comm a,sub_add_cancel]
  exact (by simpa only [h] using (degree_iso _ e a).symm)

theorem low_degree_boundary (hc : G.Connected) (hn : 2 ≤ Fintype.card V)
    (hd : ∀ v, (nbr G v).card ≤ 2) :
    (boundary G).card ≤ 2 := by
  classical
  obtain ⟨m,hm,hcase⟩ := GraffitiDegreeTwo.degree_two_path_or_cycle G hc hn hd
  rcases hcase with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · have hb : (boundary G).card ≤ ({0,m} : Finset ℕ).card := by
      apply Finset.card_le_card_of_injOn (fun v => (e v).val)
      · intro v hv
        have hnot := (Finset.mem_sdiff.mp hv).2
        by_cases h₀ : (e v).val=0
        · simp [h₀]
        · by_cases h₁ : (e v).val=m
          · simp [h₁]
          · have hv' := (e v).isLt
            have hm := inner_path_degree (e v) (by omega) (by omega)
            rw [degree_iso G e v] at hm
            have htop : MaximumDegree G v := fun w => (hd w).trans hm
            exact False.elim (hnot ((mem_maxDegreeSet G v).mpr htop))
      · intro v _ w _ hh
        exact e.injective (Fin.ext hh)
    exact hb.trans Finset.card_le_two
  · have hb : boundary G = ∅ := by
      ext v
      constructor
      · intro hv
        have hm : MaximumDegree G v := by
          intro w
          have he := cycle_degree_constant (e w) (e v)
          simpa only [degree_iso G e w, degree_iso G e v] using (Nat.le_of_eq he)
        exact False.elim ((Finset.mem_sdiff.mp hv).2 ((mem_maxDegreeSet G v).mpr hm))
      · simp
    simp [hb]

theorem boundary_bound_for_D (hc : G.Connected) (hn : 2 ≤ Fintype.card V)
    (D : Finset V) (hD : TotalDominates G D) :
    2 * (boundary G).card ≤ D.card * maxLeaves G := by
  obtain ⟨v⟩ := hc.nonempty
  have ht₂ := GraffitiPeriphery.tdcard_ge_two G D hD v
  have hL := maxLeaves_ge_two G hc hn
  have hN := domination_leaves_bound G hc D hD
  have hX := boundary_disjoint_cap G
  by_cases hSmall : (maxDegreeSet G).card ≤ 1
  · have hcap := boundary_cap G (maxLeaves G) (maxLeaves_ge_degree G hc hn)
    have hmul : maxLeaves G * (maxDegreeSet G).card ≤ maxLeaves G := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left (maxLeaves G) hSmall
    have hXL := hcap.trans hmul
    exact Nat.mul_le_mul ht₂ hXL
  · by_cases h₂ : maxLeaves G = 2
    · have hl : ∀ v, (nbr G v).card ≤ 2 := by
        intro v
        simpa [h₂] using maxLeaves_ge_degree G hc hn v
      have hB := low_degree_boundary G hc hn hl
      rw [h₂]
      omega
    by_cases h₃ : maxLeaves G = 3
    · have hl : ∀ v, (nbr G v).card ≤ 3 := by
        intro v
        simpa [h₃] using maxLeaves_ge_degree G hc hn v
      have hB := boundary_cap G 3 hl
      rw [h₃] at hN ⊢
      by_cases h : D.card % 2 = 0
      · have : D.card = 2*(D.card/2) := by omega
        omega
      · omega
    · let a := D.card - 2
      let b := maxLeaves G - 4
      have ha : D.card = a+2 := by dsimp [a]; omega
      have hb : maxLeaves G = b+4 := by dsimp [b]; omega
      calc
        2 * (boundary G).card ≤ 4*a+2*b+8 := by omega
        _ ≤ a*b + (4*a+2*b+8) := by omega
        _ = D.card * maxLeaves G := by rw [ha,hb]; simp only [Nat.add_mul,Nat.mul_add]; omega

/-- The exact catalogue inequality after clearing the positive denominator
L, which is the largest number of leaves of any spanning tree. -/
theorem conjecture259 (hc : G.Connected) (hn : 2 ≤ Fintype.card V) :
    2 * (boundary G).card ≤ totalDominationNumber G * maxLeaves G := by
  obtain ⟨D,hD,hmin⟩ := GraffitiPeriphery.exists_min_td G hc hn
  rw [← hmin]
  exact boundary_bound_for_D G hc hn D hD

#print axioms conjecture259
end Graffiti259

/- Proof module: Formal261 -/
set_option warningAsError true
set_option linter.unusedSectionVars false
noncomputable section
open Finset SimpleGraph Graffiti271 GraffitiLeaves GraffitiDegrees
open Graffiti259 (degree_iso inner_path_degree cycle_degree_constant)
open scoped BigOperators
namespace Graffiti261
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

noncomputable def degreeTwoSet : Finset V := by
  classical
  exact Finset.univ.filter ((fun v => (nbr G v).card = 2))

@[simp] theorem mem_degreeTwoSet (v : V) :
    v ∈ degreeTwoSet G ↔ (nbr G v).card = 2 := by
  classical
  simp [degreeTwoSet]

noncomputable def boundary : Finset V := by
  classical
  exact ((degreeTwoSet G).biUnion (nbr G)) \ degreeTwoSet G

theorem boundary_cap :
    (boundary G).card ≤ 2 * (degreeTwoSet G).card := by
  classical
  have hs : boundary G ⊆ (degreeTwoSet G).biUnion (nbr G) := Finset.sdiff_subset
  calc
    _ ≤ ((degreeTwoSet G).biUnion (nbr G)).card := Finset.card_le_card hs
    _ ≤ ∑ v ∈ degreeTwoSet G, (nbr G v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ degreeTwoSet G, (2 : ℕ) := sum_mono_nat _ _ _ (fun v hv => Nat.le_of_eq ((mem_degreeTwoSet G v).mp hv))
    _ = _ := by simp [Nat.mul_comm]

theorem boundary_disjoint_cap :
    (boundary G).card + (degreeTwoSet G).card ≤ Fintype.card V := by
  classical
  have hs : boundary G ⊆ (Finset.univ : Finset V) \ degreeTwoSet G := by
    intro v hv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,(Finset.mem_sdiff.mp hv).2⟩
  have hX := Finset.card_le_card hs
  rw [Finset.card_sdiff (Finset.subset_univ _), Finset.card_univ] at hX
  have hM : (degreeTwoSet G).card ≤ Fintype.card V := Finset.card_le_univ _
  omega

theorem low_degree_boundary (hc : G.Connected) (hn : 2 ≤ Fintype.card V)
    (hd : ∀ v, (nbr G v).card ≤ 2) :
    (boundary G).card ≤ 2 := by
  classical
  obtain ⟨m,hm,hcase⟩ := GraffitiDegreeTwo.degree_two_path_or_cycle G hc hn hd
  rcases hcase with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · have hb : (boundary G).card ≤ ({0,m} : Finset ℕ).card := by
      apply Finset.card_le_card_of_injOn (fun v => (e v).val)
      · intro v hv
        have hnot := (Finset.mem_sdiff.mp hv).2
        by_cases h₀ : (e v).val=0
        · simp [h₀]
        · by_cases h₁ : (e v).val=m
          · simp [h₁]
          · have hv' := (e v).isLt
            have hm := inner_path_degree (e v) (by omega) (by omega)
            rw [degree_iso G e v] at hm
            have htop : (nbr G v).card = 2 := Nat.le_antisymm (hd v) hm
            exact False.elim (hnot ((mem_degreeTwoSet G v).mpr htop))
      · intro v _ w _ hh
        exact e.injective (Fin.ext hh)
    exact hb.trans Finset.card_le_two
  · have hb : boundary G = ∅ := by
      ext v
      constructor
      · intro hv
        obtain ⟨w,hw,_⟩ := Finset.mem_biUnion.mp (Finset.mem_sdiff.mp hv).1
        have hw' := (mem_degreeTwoSet G w).mp hw
        have he := cycle_degree_constant (e w) (e v)
        rw [degree_iso G e w, degree_iso G e v, hw'] at he
        exact False.elim ((Finset.mem_sdiff.mp hv).2 ((mem_degreeTwoSet G v).mpr he.symm))
      · simp
    simp [hb]

theorem boundary_bound_for_D (hc : G.Connected) (hn : 2 ≤ Fintype.card V)
    (D : Finset V) (hD : TotalDominates G D) :
    2 * (boundary G).card ≤ D.card * maxLeaves G := by
  obtain ⟨v⟩ := hc.nonempty
  have ht₂ := GraffitiPeriphery.tdcard_ge_two G D hD v
  have hL := maxLeaves_ge_two G hc hn
  have hN := domination_leaves_bound G hc D hD
  have hX := boundary_disjoint_cap G
  have hcap := boundary_cap G
  by_cases hSmall : (degreeTwoSet G).card ≤ 1
  · have hXL : (boundary G).card ≤ maxLeaves G := by omega
    exact Nat.mul_le_mul ht₂ hXL
  · by_cases h₂ : maxLeaves G = 2
    · have hl : ∀ v, (nbr G v).card ≤ 2 := by
        intro v
        simpa [h₂] using maxLeaves_ge_degree G hc hn v
      have hB := low_degree_boundary G hc hn hl
      rw [h₂]
      omega
    by_cases h₃ : maxLeaves G = 3
    · rw [h₃] at hN ⊢
      by_cases h : D.card ≤ 3
      · omega
      · omega
    · let a := D.card - 2
      let b := maxLeaves G - 4
      have ha : D.card = a+2 := by dsimp [a]; omega
      have hb : maxLeaves G = b+4 := by dsimp [b]; omega
      calc
        2 * (boundary G).card ≤ 4*a+2*b+8 := by omega
        _ ≤ a*b + (4*a+2*b+8) := by omega
        _ = D.card * maxLeaves G := by rw [ha,hb]; simp only [Nat.add_mul,Nat.mul_add]; omega

/-- The exact catalogue inequality after clearing the positive denominator
L, which is the largest number of leaves of any spanning tree. -/
theorem conjecture261 (hc : G.Connected) (hn : 2 ≤ Fintype.card V) :
    2 * (boundary G).card ≤ totalDominationNumber G * maxLeaves G := by
  obtain ⟨D,hD,hmin⟩ := GraffitiPeriphery.exists_min_td G hc hn
  rw [← hmin]
  exact boundary_bound_for_D G hc hn D hD

#print axioms conjecture261
end Graffiti261
