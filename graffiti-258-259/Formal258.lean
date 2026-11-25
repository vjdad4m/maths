/- Reproduce with Lean 4.19.0 and Mathlib v4.19.0: run this source with lake env lean. -/
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Order.Interval.Finset.Nat
import Lean.Elab.Tactic.Omega
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

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

/- Proof module: Verify258 -/

set_option warningAsError true
set_option linter.unusedSectionVars false
noncomputable section
open Finset SimpleGraph Graffiti271 GraffitiLeaves GraffitiBFS GraffitiDegrees
open scoped BigOperators

namespace Graffiti258Exact

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

def E (r : V) : Finset V := Finset.univ.filter (fun v => G.dist r v % 2 = 0)
def O (r : V) : Finset V := Finset.univ.filter (fun v => G.dist r v % 2 ≠ 0)

theorem mem_E {r v : V} : v ∈ E G r ↔ G.dist r v % 2 = 0 := by simp [E]
theorem mem_O {r v : V} : v ∈ O G r ↔ G.dist r v % 2 ≠ 0 := by simp [O]
theorem E_root (r : V) : r ∈ E G r := by simp [E,SimpleGraph.dist_self]

theorem parity_partition (r : V) : (E G r).card + (O G r).card = Fintype.card V := by
  simpa [E,O] using Finset.filter_card_add_filter_neg_card_eq_card
    (s := (Finset.univ : Finset V)) (fun v => G.dist r v % 2 = 0)

theorem even_le_n_sub_one (hc : G.Connected) (hn : 2 ≤ Fintype.card V) (r : V) :
    (E G r).card + 1 ≤ Fintype.card V := by
  obtain ⟨y, hy⟩ := Finset.card_pos.mp (deg_pos G hc hn r)
  have hd := SimpleGraph.dist_eq_one_iff_adj.mpr ((mem_nbr G).mp hy)
  have ho : 0 < (O G r).card := Finset.card_pos.mpr ⟨y, by simp [O,hd]⟩
  have hh := parity_partition G r
  omega

theorem tight_even_leaves (hc : G.Connected) (hn : 2 ≤ Fintype.card V) (r : V)
    (hE : (E G r).card + 1 = Fintype.card V) :
    (E G r).card ≤ maxLeaves G := by
  classical
  have hp := parity_partition G r
  have hodd : (O G r).card = 1 := by omega
  obtain ⟨y,hy⟩ := Finset.card_eq_one.mp hodd
  obtain ⟨par,T,hsub,hT,hlevels,hadj,_⟩ := exists_bfs_tree G hc r
  have ery : G.Adj r y := by
    obtain ⟨z,hz⟩ := Finset.card_pos.mp (deg_pos G hc hn r)
    have hAdj := (mem_nbr G).mp hz
    have hdist := SimpleGraph.dist_eq_one_iff_adj.mpr hAdj
    have hzo : z ∈ O G r := by simp [O,hdist]
    rw [hy,Finset.mem_singleton] at hzo
    rwa [hzo] at hAdj
  have huniv : ∀ v, v ≠ y → G.Adj y v := by
    intro v hv
    by_cases hvr : v=r
    · simpa [hvr] using ery.symm
    · have he : G.dist r v % 2 = 0 := by
        by_cases he : G.dist r v % 2 = 0
        · exact he
        · exfalso
          have hm := (mem_O G).mpr he
          rw [hy,Finset.mem_singleton] at hm
          exact hv hm
      have hl := hlevels v hvr
      have hoff : G.dist r (par v) % 2 ≠ 0 := by omega
      have hm := (mem_O G).mpr hoff
      rw [hy,Finset.mem_singleton] at hm
      exact hsub ((hadj y v).mpr (Or.inr ⟨hvr,hm⟩))
  have hcard : (nbr G y).card = Fintype.card V - 1 := by
    have hs : nbr G y = Finset.univ.erase y := by
      ext v
      simp only [mem_nbr,Finset.mem_erase,Finset.mem_univ,and_true]
      exact ⟨fun h => h.ne.symm, huniv _⟩
    rw [hs,Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ]
  have hl := maxLeaves_ge_degree G hc hn y
  omega

/-- Inject even vertices with children to their selected odd children. Even
vertices without children are non-root leaves, which supplies the leftover. -/
theorem even_count_tree_bound (hc : G.Connected) (hn : 2 ≤ Fintype.card V) (r : V) :
    2 * (E G r).card ≤ Fintype.card V + maxLeaves G := by
  classical
  obtain ⟨par,T,hsub,hT,hlevels,hadj,_⟩ := exists_bfs_tree G hc r
  let child (v : V) : Prop := ∃ u, u ≠ r ∧ par u = v
  let f (v : V) : V := if h : child v then h.choose else r
  have f_pr (v : V) (h : child v) : f v ≠ r ∧ par (f v) = v := by
    simpa [f,h] using h.choose_spec
  let EC := (E G r).filter child
  let EL := (E G r).filter (fun v => ¬ child v)
  have hcardC : EC.card ≤ (O G r).card := by
    apply Finset.card_le_card_of_injOn f
    · intro x hx
      have hh := Finset.mem_filter.mp hx
      have h1 := f_pr x hh.2
      have hf := hlevels (f x) h1.1
      rw [h1.2] at hf
      have hp := (mem_E G).mp hh.1
      apply (mem_O G).mpr
      omega
    · intro x hx y hy he
      have hx' := f_pr x (Finset.mem_filter.mp hx).2
      have hy' := f_pr y (Finset.mem_filter.mp hy).2
      rw [he] at hx'
      exact hx'.2.symm.trans hy'.2
  have hrootC : child r := by
    obtain ⟨z,hz⟩ := Finset.card_pos.mp (deg_pos T hT.isConnected hn r)
    have e := (hadj r z).mp ((mem_nbr T).mp hz)
    rcases e with ⟨h,_⟩ | h
    · exact False.elim (h rfl)
    · exact ⟨z,h⟩
  have hleaf : EL ⊆ leafSet T := by
    intro v hv
    have hno : ¬ child v := (Finset.mem_filter.mp hv).2
    have hne : v ≠ r := by intro he; subst v; exact hno hrootC
    have hnb : nbr T v = {par v} := by
      ext w
      simp only [mem_nbr,Finset.mem_singleton]
      constructor
      · intro e
        rcases (hadj v w).mp e with ⟨_,he⟩ | he
        · exact he.symm
        · exact False.elim (hno ⟨w,he⟩)
      · intro h
        exact (hadj v w).mpr (Or.inl ⟨hne,h.symm⟩)
    simp [leafSet,hnb]
  have hcardL := (Finset.card_le_card hleaf).trans (leaf_card_le_maxLeaves G hsub hT)
  have hp := parity_partition G r
  have hh : EC.card + EL.card = (E G r).card :=
    Finset.filter_card_add_filter_neg_card_eq_card child
  omega

/-- No classification of paths and cycles is required: when degrees are at
most two a non-root breadth-first vertex can have at most one child. -/
theorem even_low_degree (hc : G.Connected) (r : V)
    (hΔ : ∀ v, (nbr G v).card ≤ 2) :
    2 * (E G r).card ≤ Fintype.card V + 1 := by
  classical
  obtain ⟨par,T,hsub,hT,hlevels,hadj,_⟩ := exists_bfs_tree G hc r
  let A := (E G r).erase r
  have hto (x : V) (hx : x ∈ A) : par x ∈ O G r := by
    have h := Finset.mem_erase.mp hx
    have hl := hlevels x h.1
    have hp := (mem_E G).mp h.2
    apply (mem_O G).mpr
    omega
  have hInj : Set.InjOn par (↑A : Set V) := by
    intro a ha b hb hab
    by_contra! hne
    have haA := Finset.mem_erase.mp ha
    have hbA := Finset.mem_erase.mp hb
    have hodd := (mem_O G).mp (hto a ha)
    have hpar_ne : par a ≠ r := by intro e; rw [e,SimpleGraph.dist_self] at hodd; simp at hodd
    have hla := hlevels a haA.1
    have hlb := hlevels b hbA.1
    rw [← hab] at hlb
    have hlp := hlevels (par a) hpar_ne
    have hza : par (par a) ≠ a := by intro e; rw [e] at hlp; omega
    have hzb : par (par a) ≠ b := by intro e; rw [e] at hlp; omega
    have hSub : ({a,b,par (par a)} : Finset V) ⊆ nbr G (par a) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      apply (mem_nbr G).mpr
      rcases hx with he|he|he
      · rw [he]
        exact hsub ((hadj (par a) a).mpr (Or.inr ⟨haA.1,rfl⟩))
      · rw [he]
        exact hsub ((hadj (par a) b).mpr (Or.inr ⟨hbA.1,hab.symm⟩))
      · rw [he]
        exact hsub ((hadj (par a) (par (par a))).mpr (Or.inl ⟨hpar_ne,rfl⟩))
    have h3 := Finset.card_le_card hSub
    have hcard : ({a,b,par (par a)} : Finset V).card = 3 := by
      rw [Finset.card_insert_of_not_mem,Finset.card_insert_of_not_mem,Finset.card_singleton]
      · simp [Ne.symm hzb]
      · simp [hne,Ne.symm hza]
    rw [hcard] at h3
    have hd := hΔ (par a)
    omega
  have hA : A.card ≤ (O G r).card := Finset.card_le_card_of_injOn par hto hInj
  have hpart := parity_partition G r
  have hsize : A.card + 1 = (E G r).card := Finset.card_erase_add_one (E_root G r)
  omega

theorem low_degree_dom (D : Finset V) (hD : TotalDominates G D)
    (hΔ : ∀ v, (nbr G v).card ≤ 2) :
    Fintype.card V ≤ 2 * D.card := by
  classical
  have hs : (Finset.univ : Finset V) ⊆ D.biUnion (nbr G) := by
    intro v _
    obtain ⟨x,hx,hvx⟩ := hD v
    exact Finset.mem_biUnion.mpr ⟨x,hx,(mem_nbr G).mpr hvx.symm⟩
  have h := Finset.card_le_card hs
  rw [Finset.card_univ] at h
  have hz : (∑ v ∈ D, (nbr G v).card) ≤ D.card * 2 := by
    calc
      _ ≤ ∑ _v ∈ D, (2 : ℕ) := sum_mono_nat _ _ _ (fun v _ => hΔ v)
      _ = D.card * 2 := by simp
  have hm := (h.trans Finset.card_biUnion_le).trans hz
  omega

theorem any_total_dom_at_least_two (hc : G.Connected) (D : Finset V)
    (hD : TotalDominates G D) : 2 ≤ D.card := by
  obtain ⟨v⟩ := hc.nonempty
  obtain ⟨u,hu,_⟩ := hD v
  obtain ⟨w,hw,he⟩ := hD u
  exact Finset.one_lt_card.mpr ⟨u,hu,w,hw,he.ne⟩

/-- Pointwise shell bound at any root and for any total dominating set. -/
theorem pointwise_258 (hc : G.Connected) (hn : 2 ≤ Fintype.card V)
    (D : Finset V) (hD : TotalDominates G D) (r : V) :
    2 * (E G r).card ≤ D.card * maxLeaves G := by
  let n := Fintype.card V
  let e := (E G r).card
  let L := maxLeaves G
  let t := D.card
  change 2*e ≤ t*L
  have ht : 2 ≤ t := any_total_dom_at_least_two G hc D hD
  have hL : 2 ≤ L := maxLeaves_ge_two G hc hn
  have hnE : e+1 ≤ n := even_le_n_sub_one G hc hn r
  by_cases hEq : e+1=n
  · have hEL : e ≤ L := tight_even_leaves G hc hn r hEq
    exact Nat.mul_le_mul ht hEL
  have he2 : e+2≤n := by omega
  by_cases h2 : L=2
  · have hΔ : ∀ v, (nbr G v).card ≤ 2 := by
      intro v
      exact (maxLeaves_ge_degree G hc hn v).trans (by rw [← h2])
    have hA : 2*e ≤ n+1 := even_low_degree G hc r hΔ
    have hB : n ≤ 2*t := low_degree_dom G D hD hΔ
    rw [h2]
    omega
  have hcD : n ≤ L+t+2*(t/2-1) := domination_leaves_bound G hc D hD
  by_cases h3 : L=3
  · rw [h3]
    by_cases hs : t≤3
    · omega
    · have ha : 2*e ≤ n+L := even_count_tree_bound G hc hn r
      omega
  · let a := t-2
    let b := L-4
    have ha : t=a+2 := by dsimp [a]; omega
    have hb : L=b+4 := by dsimp [b]; omega
    calc
      2*e ≤ 2*b+4*a+8 := by omega
      _ ≤ a*b+(2*b+4*a+8) := by omega
      _ = t*L := by rw [ha,hb]; simp only [Nat.add_mul,Nat.mul_add]; omega

def evenMax : Nat := (Finset.univ : Finset V).sup (fun r => (E G r).card)

theorem exists_min (hc : G.Connected) (hn : 2 ≤ Fintype.card V) :
    ∃ D : Finset V, TotalDominates G D ∧ D.card = totalDominationNumber G := by
  have hnon : {k : ℕ | ∃ D : Finset V, TotalDominates G D ∧ D.card = k}.Nonempty := by
    refine ⟨Fintype.card V,Finset.univ,?_,Finset.card_univ⟩
    intro v
    obtain ⟨w,hw⟩ := Finset.card_pos.mp (deg_pos G hc hn v)
    exact ⟨w,Finset.mem_univ _,(mem_nbr G).mp hw⟩
  unfold totalDominationNumber
  exact Nat.sInf_mem hnon

/-- Graffiti.pc #258, with the positive spanning-tree leaf number cleared
from the denominator. The distance-zero root is included in the even shell. -/
theorem conjecture258 (hc : G.Connected) (hn : 2 ≤ Fintype.card V) :
    2 * evenMax G ≤ totalDominationNumber G * maxLeaves G := by
  classical
  letI : Nonempty V := hc.nonempty
  obtain ⟨r,_,hr⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset V) Finset.univ_nonempty
    (fun r => (E G r).card)
  obtain ⟨D,hD,hmin⟩ := exists_min G hc hn
  unfold evenMax
  rw [hr,← hmin]
  exact pointwise_258 G hc hn D hD r

#print axioms conjecture258
end Graffiti258Exact
