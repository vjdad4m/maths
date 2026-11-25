/- Reproduce with Lean 4.19.0 and Mathlib v4.19.0: run this source with lake env lean. -/
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Order.Interval.Finset.Nat
import Lean.Elab.Tactic.Omega
import Mathlib.Combinatorics.SimpleGraph.Acyclic

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

/- Proof module: Tree232 -/
set_option warningAsError true
set_option linter.unusedSectionVars false
namespace Graffiti232Tree
universe u

variable {V : Type u} [DecidableEq V]

structure Graph (V : Type u) where
  verts : List V
  nodup : verts.Nodup
  complete : ∀ v, v ∈ verts
  edge : V → V → Bool
  symm : ∀ v w, edge v w = true → edge w v = true
  loopless : ∀ v, edge v v = false

def Adj (G : Graph V) (v w : V) : Prop := G.edge v w = true

inductive Walk (G : Graph V) : V → V → Prop
  | nil {v} : Walk G v v
  | cons {u v w} : Adj G u v → Walk G v w → Walk G u w

def Connected (G : Graph V) : Prop := ∀ v w, Walk G v w

def cardinal (G : Graph V) (P : V → Bool) : Nat := (G.verts.filter P).length
def nbrs (G : Graph V) (P : V → Bool) (v : V) : List V :=
  G.verts.filter (fun w => G.edge v w && P w)
def degree (G : Graph V) (v : V) : Nat := (nbrs G (fun _ => true) v).length
def minimumDegreeSet (G : Graph V) (v : V) : Bool :=
  G.verts.all (fun w => decide (degree G v ≤ degree G w))
def leaf (G : Graph V) (v : V) : Bool := decide (degree G v = 1)
def leafNeighbors (G : Graph V) (v : V) : List V := nbrs G (leaf G) v
def support (G : Graph V) (v : V) : Bool := decide (0 < (leafNeighbors G v).length)
def privateNeighbor (G : Graph V) (A : V → Bool) (v : V) : Bool :=
  decide ((nbrs G A v).length = 1)
def TwoIndependent (G : Graph V) (I : V → Bool) : Prop :=
  ∀ v, I v = true → (nbrs G I v).length ≤ 1

theorem choose_le_length (xs ys : List V) (R : V → V → Prop)
    (hnx : xs.Nodup) (hny : ys.Nodup)
    (h : ∀ x ∈ xs, ∃ y ∈ ys, R x y)
    (hu : ∀ x x' y, R x y → R x' y → x = x') : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => exact Nat.zero_le _
  | cons a as ih =>
    obtain ⟨y,hy,hay⟩ := h a (List.mem_cons_self ..)
    have htail := (List.nodup_cons.mp hnx)
    have next : ∀ x ∈ as, ∃ z ∈ ys.erase y, R x z := by
      intro x hx
      obtain ⟨z,hz,hxz⟩ := h x (List.mem_cons_of_mem _ hx)
      have hzy : z ≠ y := by
        intro e; subst z
        have e' := hu a x y hay hxz
        exact htail.1 (e' ▸ hx)
      exact ⟨z,(hny.mem_erase_iff).2 ⟨hzy,hz⟩,hxz⟩
    have ih' := ih (ys.erase y) htail.2 (hny.erase y) next
    rw [List.length_erase_of_mem hy] at ih'
    have hpos : 0 < ys.length := by
      cases ys with
      | nil => simp at hy
      | cons _ _ => simp
    simp only [List.length_cons]
    omega

theorem subset_le_length {xs ys : List V}
    (hnx : xs.Nodup) (hny : ys.Nodup) (h : xs ⊆ ys) : xs.length ≤ ys.length := by
  exact choose_le_length xs ys Eq hnx hny
    (fun x hx => ⟨x,h hx,rfl⟩) (fun _ _ _ u v => u.trans v.symm)

theorem count_filter_split (l : List V) (P Q : V → Bool) :
    (l.filter P).length = (l.filter (fun v => P v && Q v)).length
      + (l.filter (fun v => P v && !Q v)).length := by
  simpa only [List.countP_eq_length_filter, List.filter_filter] using
    List.countP_eq_countP_filter_add l P Q

theorem count_filter_comm (l : List V) (P Q : V → Bool) :
    (l.filter (fun v => P v && Q v)).length = (l.filter (fun v => Q v && P v)).length := by
  simp [Bool.and_comm]

theorem filter_nodup {xs : List V} (h : xs.Nodup) (P : V → Bool) :
    (xs.filter P).Nodup := List.filter_sublist.nodup h

theorem two_members {xs : List V} (hd : xs.Nodup) (h : 2 ≤ xs.length) :
    ∃ x ∈ xs, ∃ y ∈ xs, x ≠ y := by
  cases xs with
  | nil => simp at h
  | cons x tail =>
    cases tail with
    | nil => simp at h
    | cons y ys =>
      refine ⟨x,by simp,y,by simp,?_⟩
      intro e; subst y
      exact (List.nodup_cons.mp hd).1 (by simp)

theorem singleton_unique {xs : List V}
    (h : xs.length ≤ 1) {u v} (hu : u ∈ xs) (hv : v ∈ xs) : u = v := by
  cases xs with
  | nil => simp at hu
  | cons a tail =>
    cases tail with
    | nil =>
      have hu' : u = a := by simpa using hu
      have hv' : v = a := by simpa using hv
      exact hu'.trans hv'.symm
    | cons b bs => simp at h

theorem positive_member {xs : List V} (h : 0 < xs.length) : ∃ x, x ∈ xs := by
  cases xs with
  | nil => simp at h
  | cons a tail => exact ⟨a,by simp⟩

theorem member_positive {xs : List V} {x : V} (h : x ∈ xs) : 0 < xs.length := by
  cases xs with
  | nil => simp at h
  | cons a tail => simp

theorem mem_nbrs {G : Graph V} {P : V → Bool} {v w} :
    w ∈ nbrs G P v ↔ Adj G v w ∧ P w = true := by
  simp [nbrs, Adj, G.complete]

theorem leaf_degree {G : Graph V} {v} : leaf G v = true ↔ degree G v = 1 := by
  simp [leaf]

theorem support_has_leaf {G : Graph V} {v} (h : support G v = true) :
    ∃ w, Adj G v w ∧ leaf G w = true := by
  obtain ⟨w,hw⟩ := positive_member (of_decide_eq_true h)
  exact ⟨w,mem_nbrs.mp hw⟩

theorem leaf_unique_neighbor {G : Graph V} {v w z}
    (h : leaf G v = true) (hw : Adj G v w) (hz : Adj G v z) : w = z := by
  have hv : (nbrs G (fun _ => true) v).length = 1 := leaf_degree.mp h
  have hle : (nbrs G (fun _ => true) v).length ≤ 1 := by omega
  exact singleton_unique hle
    (mem_nbrs.mpr ⟨hw,rfl⟩) (mem_nbrs.mpr ⟨hz,rfl⟩)

theorem walk_has_first {G : Graph V} {v w} (h : Walk G v w) (hne : v ≠ w) :
    ∃ z, Adj G v z := by
  cases h with
  | nil => exact False.elim (hne rfl)
  | cons e _ => exact ⟨_,e⟩

theorem degree_pos {G : Graph V} (hcon : Connected G) (hn : 2 < G.verts.length) (v : V) :
    0 < degree G v := by
  obtain ⟨x,_,y,_,hxy⟩ := two_members G.nodup (by omega)
  have hother : ∃ w, v ≠ w := by
    by_cases e : v=x
    · exact ⟨y,e ▸ hxy⟩
    · exact ⟨x,e⟩
  obtain ⟨w,hw⟩ := hother
  obtain ⟨z,hz⟩ := walk_has_first (hcon v w) hw
  exact member_positive (mem_nbrs.mpr ⟨hz,rfl⟩)

theorem leaf_pair_traps_walk {G : Graph V} {x y v w}
    (hx : leaf G x = true) (hy : leaf G y = true) (hxy : Adj G x y)
    (hw : Walk G v w) (hv : v=x ∨ v=y) : w=x ∨ w=y := by
  induction hw with
  | nil => exact hv
  | cons e _ ih =>
    apply ih
    rcases hv with rfl|rfl
    · exact Or.inr (leaf_unique_neighbor hx e hxy)
    · exact Or.inl (leaf_unique_neighbor hy e (G.symm _ _ hxy))

theorem leaf_not_support {G : Graph V} (hcon : Connected G)
    (hn : 2 < G.verts.length) {v} (hl : leaf G v = true) : support G v = false := by
  apply Bool.eq_false_iff.mpr
  intro hs
  obtain ⟨w,hvw,hw⟩ := support_has_leaf hs
  have hne : v ≠ w := by
    intro e; subst w
    have he := G.loopless v
    simp [Adj,he] at hvw
  have hall : G.verts ⊆ [v,w] := by
    intro z _
    have hh := leaf_pair_traps_walk hl hw hvw (hcon v z) (Or.inl rfl)
    simpa using hh
  have hsmall := subset_le_length G.nodup (by simp [List.nodup_cons,hne]) hall
  simp at hsmall
  omega


/-- A simple path recorded by the successive vertices after its start. -/
inductive PathTo (G : Graph V) : V → List V → V → Prop
  | nil {u} : PathTo G u [] u
  | cons {u x v p} : Adj G u x → u ∉ x :: p →
      PathTo G x p v → PathTo G u (x :: p) v

theorem path_single {G : Graph V} {u v} (h : Adj G u v) : PathTo G u [v] v := by
  apply PathTo.cons h _ PathTo.nil
  intro hd
  have he : u = v := by simpa using hd
  subst v
  have hh := G.loopless u
  simp [Adj,hh] at h

theorem path_nodup {G : Graph V} {u p v} (h : PathTo G u p v) :
    (u::p).Nodup := by
  induction h with
  | nil => simp
  | cons _ h _ ih => exact List.nodup_cons.mpr ⟨h,ih⟩

theorem path_endpoint {G : Graph V} {u p v} (h : PathTo G u p v) : v ∈ u::p := by
  induction h with
  | nil => simp
  | cons _ _ _ ih => exact List.mem_cons_of_mem _ ih

theorem path_endpoint_tail {G : Graph V} {u p v} (h : PathTo G u p v) (hne : u≠v) :
    v ∈ p := by
  have hm := path_endpoint h
  exact (List.mem_cons.mp hm).resolve_left (fun he => hne he.symm)

theorem path_empty_endpoint {G : Graph V} {u v} (h : PathTo G u [] v) : u=v := by
  cases h
  rfl

theorem path_to_walk {G : Graph V} {u p v} (h : PathTo G u p v) : Walk G u v := by
  induction h with
  | nil => exact .nil
  | cons e _ _ ih => exact .cons e ih

theorem path_append {G : Graph V} {u p v q w}
    (h : PathTo G u p v) (h' : PathTo G v q w)
    (hd : ∀ t ∈ u::p, t ∉ q) : PathTo G u (p++q) w := by
  induction h with
  | nil => exact h'
  | @cons a x b ps he hu hps ih =>
    apply PathTo.cons he
    · intro hh
      have hh' : a ∈ (x::ps) ++ q := hh
      rcases List.mem_append.mp hh' with hpre|hpost
      · exact hu hpre
      · exact hd a (List.mem_cons_self ..) hpost
    · exact ih h' (fun t ht => hd t (List.mem_cons_of_mem _ ht))

theorem path_reverse {G : Graph V} {u p v} (h : PathTo G u p v) :
    ∃ q, PathTo G v q u ∧ q.length = p.length ∧ ∀ a∈v::q, a∈u::p := by
  induction h with
  | nil => exact ⟨[],.nil,rfl,fun _ h => h⟩
  | @cons a x b ps he hu hps ih =>
    obtain ⟨q,hq,hlen,hsub⟩ := ih
    refine ⟨q++[a],path_append hq (path_single (G.symm _ _ he)) ?_, ?_, ?_⟩
    · intro z hz hm
      have heq : z=a := by simpa using hm
      subst z
      exact hu (hsub _ hz)
    · simp [hlen]
    · intro t ht
      have hmem : t∈(b::q) ++ [a] := ht
      rcases List.mem_append.mp hmem with hmem|hmem
      · exact List.mem_cons_of_mem _ (hsub t hmem)
      · have heq : t=a := by simpa using hmem
        subst t
        simp

theorem path_prefix {G : Graph V} {u p v} (h : PathTo G u p v) {w}
    (hw : w ∈ u::p) : ∃ pre suf, p = pre ++ suf ∧ PathTo G u pre w := by
  induction h with
  | @nil a =>
    have heq : w=a := by simpa using hw
    subst w
    exact ⟨[],[],rfl,.nil⟩
  | @cons a x b ps he hu hps ih =>
    rcases List.mem_cons.mp hw with e|hw'
    · subst w; exact ⟨[],x::ps,rfl,.nil⟩
    · obtain ⟨pre,suf,hcat,hroute⟩ := ih hw'
      refine ⟨x::pre,suf,by simp [hcat],PathTo.cons he ?_ hroute⟩
      intro hmem
      apply hu
      rw [hcat]
      exact List.mem_append_left suf hmem

/-- The classical unique-simple-path presentation of a finite tree. This is
equivalent to a connected undirected simple graph with no cycle. -/
structure Tree (V : Type u) where
  graph : Graph V
  existsPath : ∀ a b : V, ∃ p, PathTo graph a p b
  uniquePath : ∀ a b p q, PathTo graph a p b → PathTo graph a q b → p=q

def TPath (T : Tree V) := PathTo T.graph

noncomputable def chosen (T : Tree V) (a b : V) : List V :=
  Classical.choose (T.existsPath a b)

theorem chosen_path (T : Tree V) (a b : V) : TPath T a (chosen T a b) b :=
  Classical.choose_spec (T.existsPath a b)

theorem tree_connected (T : Tree V) : Connected T.graph := fun a b =>
  path_to_walk (chosen_path T a b)

noncomputable def dist (T : Tree V) (a b : V) : Nat := (chosen T a b).length

theorem dist_eq {T : Tree V} {a p b} (h : TPath T a p b) : dist T a b = p.length := by
  unfold dist
  rw [T.uniquePath _ _ _ _ (chosen_path T _ _) h]

theorem dist_self (T : Tree V) (a : V) : dist T a a = 0 :=
  dist_eq (PathTo.nil : TPath T a [] a)

theorem dist_adj {T : Tree V} {a b} (h : Adj T.graph a b) : dist T a b = 1 :=
  dist_eq (path_single h)

theorem dist_pos {T : Tree V} {a b} (h : a≠b) : 0 < dist T a b := by
  unfold dist
  cases he : chosen T a b with
  | nil =>
    have hi := chosen_path T a b
    rw [he] at hi
    exact False.elim (h (path_empty_endpoint hi))
  | cons x xs => simp

theorem path_different_branches_disjoint {T : Tree V} {u z z' p q a b}
    (hp : TPath T u (z::p) a) (hq : TPath T u (z'::q) b) (hd : z≠z') :
    ∀ w ∈ z::p, w ∉ z'::q := by
  intro w hw hw'
  obtain ⟨pre,suf,hcat,hroute⟩ := path_prefix hp (List.mem_cons_of_mem _ hw)
  obtain ⟨pre',suf',hcat',hroute'⟩ := path_prefix hq (List.mem_cons_of_mem _ hw')
  have he := T.uniquePath _ _ _ _ hroute hroute'
  have hn := (List.nodup_cons.mp (path_nodup hp)).1
  cases hne : pre with
  | nil =>
    rw [hne] at hroute
    have heq := path_empty_endpoint hroute
    subst w
    exact hn hw
  | cons x xs =>
    have heq : z=x := by
      rw [hne] at hcat
      exact (List.cons.inj hcat).1
    rw [← he,hne] at hcat'
    have heq' : z'=x := (List.cons.inj hcat').1
    exact hd (heq.trans heq'.symm)

theorem path_starts_iff_contains_neighbor {T : Tree V} {u z p v}
    (e : Adj T.graph u z) (h : TPath T u p v) (hz : z ∈ p) :
    ∃ q, p = z::q := by
  obtain ⟨pre,suf,hp,hroute⟩ := path_prefix h (List.mem_cons_of_mem _ hz)
  have he := T.uniquePath _ _ _ _ hroute (path_single e)
  rw [he] at hp
  exact ⟨suf,hp⟩

theorem dist_other_branch {T : Tree V} {u z p v x}
    (h : TPath T u (z::p) v)
    (hx : z ∉ chosen T u x) : dist T v x = dist T v u + dist T u x := by
  obtain ⟨q,hq,_,hsub⟩ := path_reverse h
  have hux := chosen_path T u x
  have hdis : ∀ a∈v::q, a∉chosen T u x := by
    intro a ha ham
    have has := hsub a ha
    rcases List.mem_cons.mp has with he|hahas
    · subst a
      exact (List.nodup_cons.mp (path_nodup hux)).1 ham
    · cases hcomp : chosen T u x with
      | nil => rw [hcomp] at ham; contradiction
      | cons w ws =>
        have hh := hux
        rw [hcomp] at hh
        have hzw : z≠w := by
          intro e; subst w
          apply hx; rw [hcomp]; simp
        exact path_different_branches_disjoint h hh hzw _ hahas (hcomp ▸ ham)
  have he := dist_eq (path_append hq hux hdis)
  rw [List.length_append, ← dist_eq hq] at he
  exact he

def maxList (xs : List Nat) : Nat := xs.foldr max 0

theorem maxList_upper {xs : List Nat} {x : Nat} (h : x∈xs) : x≤maxList xs := by
  induction xs with
  | nil => contradiction
  | cons a as ih =>
    rcases List.mem_cons.mp h with e|h
    · subst x; exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem maxList_attains {xs : List Nat} (h : xs≠[]) : maxList xs ∈ xs := by
  induction xs with
  | nil => contradiction
  | cons a as ih =>
    cases as with
    | nil => simp [maxList]
    | cons b bs =>
      have hf := ih (by simp)
      change max a (maxList (b::bs)) ∈ a::b::bs
      by_cases he : a ≤ maxList (b::bs)
      · rw [Nat.max_eq_right he]
        exact List.mem_cons_of_mem _ hf
      · rw [Nat.max_eq_left (by omega)]
        simp

noncomputable def eccentricity (T : Tree V) (v : V) : Nat :=
  maxList (T.graph.verts.map (dist T v))

noncomputable def center (T : Tree V) (v : V) : Bool :=
  T.graph.verts.all (fun w => decide (eccentricity T v ≤ eccentricity T w))

theorem ecc_upper (T : Tree V) (v w : V) : dist T v w ≤ eccentricity T v := by
  unfold eccentricity
  exact maxList_upper (List.mem_map.mpr ⟨w,T.graph.complete _,rfl⟩)

theorem ecc_attains (T : Tree V) (v : V) : ∃ w, dist T v w = eccentricity T v := by
  have hn : T.graph.verts.map (dist T v) ≠ [] := by
    intro he
    have he' : dist T v v ∈ T.graph.verts.map (dist T v) :=
      List.mem_map.mpr ⟨v,T.graph.complete _,rfl⟩
    rw [he] at he'; contradiction
  obtain ⟨w,_,hw⟩ := List.mem_map.mp (maxList_attains hn)
  exact ⟨w,hw⟩

theorem center_char {T : Tree V} {v} : center T v = true ↔
    ∀ w, eccentricity T v ≤ eccentricity T w := by
  unfold center
  simp [List.all_eq_true,T.graph.complete]

theorem dist_symm (T : Tree V) (a b : V) : dist T a b = dist T b a := by
  obtain ⟨q,hq,hqLen,_⟩ := path_reverse (chosen_path T a b)
  rw [dist_eq hq,hqLen]
  rfl

theorem distStep {T : Tree V} {u v w} (e : Adj T.graph u v) :
    dist T u w ≤ 1 + dist T v w := by
  by_cases hv : v ∈ chosen T u w
  · obtain ⟨q,hq⟩ := path_starts_iff_contains_neighbor e (chosen_path T u w) hv
    have hp := chosen_path T u w
    rw [hq] at hp
    have htail : TPath T v q w := by cases hp with | cons _ _ h => exact h
    rw [dist_eq hp, dist_eq htail]
    simp [Nat.add_comm]
  · have he := dist_other_branch (path_single e) hv
    rw [dist_adj (T.graph.symm _ _ e)] at he
    omega

theorem distPathTriangle {T : Tree V} {u v p} (hp : TPath T u p v) (w : V) :
    dist T u w ≤ p.length + dist T v w := by
  induction hp with
  | nil => simp
  | @cons u z v p he _ h ih =>
    have hs := distStep (w:=w) he
    simp only [List.length_cons]
    omega

theorem distTriangle (T : Tree V) (u v w : V) :
    dist T u w ≤ dist T u v + dist T v w :=
  distPathTriangle (chosen_path T u v) w

noncomputable def radius (T : Tree V) : Nat :=
  T.graph.verts.foldr (fun u r => min (eccentricity T u) r)
    (maxList (T.graph.verts.map (eccentricity T)))

theorem radiusAttains (T : Tree V) (h : 0 < T.graph.verts.length) :
    (∃ u, eccentricity T u = radius T) ∧ ∀ u, radius T ≤ eccentricity T u := by
  let m := maxList (T.graph.verts.map (eccentricity T))
  have allLe : ∀ u, eccentricity T u ≤ m :=
    fun u => maxList_upper (List.mem_map.mpr ⟨u,T.graph.complete _,rfl⟩)
  have aux : ∀ l : List V, ∀ {a : Nat} (ha : ∃ u, eccentricity T u = a),
      (∃ u, eccentricity T u = l.foldr (fun u r => min (eccentricity T u) r) a) ∧
      (∀ u ∈ l, l.foldr (fun u r => min (eccentricity T u) r) a ≤ eccentricity T u) := by
    intro l
    induction l with
    | nil => intro a ha; exact ⟨ha, by simp⟩
    | cons v l ih =>
      intro a ha
      obtain ⟨⟨w,hw⟩,hb⟩ := ih ha
      constructor
      · by_cases hv : eccentricity T v ≤ l.foldr (fun u r => min (eccentricity T u) r) a
        · exact ⟨v,(Nat.min_eq_left hv).symm⟩
        · exact ⟨w,hw.trans (Nat.min_eq_right (by omega)).symm⟩
      · intro u hu
        cases List.mem_cons.mp hu with
        | inl e => subst u; exact Nat.min_le_left _ _
        | inr e => exact Nat.le_trans (Nat.min_le_right _ _) (hb _ e)
  have hv : T.graph.verts.map (eccentricity T) ≠ [] := by
    obtain ⟨u,hu⟩ := positive_member h
    have hx : eccentricity T u ∈ T.graph.verts.map (eccentricity T) := List.mem_map.mpr ⟨u,hu,rfl⟩
    intro e
    rw [e] at hx
    exact List.not_mem_nil hx
  obtain ⟨u,_,hu⟩ := List.mem_map.mp (maxList_attains hv)
  obtain ⟨he,hp⟩ := aux T.graph.verts ⟨u,hu⟩
  exact ⟨he,fun u => hp u (T.graph.complete u)⟩

theorem longPath (T : Tree V) (h : 0 < T.graph.verts.length) (hr : 0 < radius T) :
    ∃ a b p, TPath T a p b ∧ 2*radius T ≤ p.length+1 := by
  obtain ⟨⟨u,hu⟩,hmin⟩ := radiusAttains T h
  obtain ⟨a,ha⟩ := ecc_attains T u
  have hp := chosen_path T u a
  cases hpa : chosen T u a with
  | nil =>
    have he : dist T u a = 0 := by simp [dist,hpa]
    omega
  | cons z p =>
    rw [hpa] at hp
    have hz : Adj T.graph u z := by cases hp with | cons e _ _ => exact e
    obtain ⟨b,hb⟩ := ecc_attains T z
    have hbase := hmin z
    have haway : z ∉ chosen T u b := by
      intro hzmem
      obtain ⟨q,hq⟩ := path_starts_iff_contains_neighbor hz (chosen_path T u b) hzmem
      have hw := chosen_path T u b
      rw [hq] at hw
      have htail : TPath T z q b := by cases hw with | cons _ _ hh => exact hh
      have h1 := dist_eq hw
      have h2 := dist_eq htail
      have h3 := ecc_upper T u b
      simp only [List.length_cons] at h1
      omega
    have hfar := dist_other_branch hp haway
    have e0 := distStep (w:=b) (T.graph.symm _ _ hz)
    have e1 := dist_symm T a u
    have e2 : dist T a b = (chosen T a b).length := rfl
    exact ⟨a,b,chosen T a b,chosen_path T a b,by omega⟩



open SimpleGraph

noncomputable def fromSimple [Fintype V] (G : SimpleGraph V) : Graph V := by
  classical
  exact {
    verts := Finset.univ.toList,
    nodup := Finset.nodup_toList _,
    complete := by simp,
    edge := fun a b => decide (G.Adj a b),
    symm := by intro a b h; exact decide_eq_true (G.symm (of_decide_eq_true h)),
    loopless := by intro a; simp
  }

theorem adj_iff_simple {G : SimpleGraph V} [Fintype V] {a b} :
    Adj (fromSimple G) a b ↔ G.Adj a b := by
  classical
  simp [Adj,fromSimple]

theorem mapWalk {G : SimpleGraph V} [Fintype V] {a b} (p : G.Walk a b) (h : p.IsPath) :
    PathTo (fromSimple G) a p.support.tail b := by
  induction p with
  | nil => exact .nil
  | @cons a x b e p ih =>
    have hn := (List.nodup_cons.mp h.support_nodup).1
    have ht := h.of_cons
    have he := adj_iff_simple.mpr e
    have htail := ih ht
    have eq : p.support = x :: p.support.tail := by cases p <;> rfl
    change PathTo (fromSimple G) a p.support b
    rw [eq] at hn ⊢
    exact .cons he hn htail

theorem liftWalk {G : SimpleGraph V} [Fintype V] {a p b} (h : PathTo (fromSimple G) a p b) :
    ∃ w : G.Walk a b, w.support = a::p ∧ w.length = p.length ∧ w.IsPath := by
  induction h with
  | nil => exact ⟨.nil,rfl,rfl,by simp⟩
  | @cons a x b p e hn hroute ih =>
    obtain ⟨w,hs,hlen,hp⟩ := ih
    refine ⟨.cons (adj_iff_simple.mp e) w, ?_, ?_, ?_⟩
    · simp [hs]
    · simp [hlen]
    · apply (SimpleGraph.Walk.isPath_def _).mpr
      simp only [Walk.support_cons,hs]
      exact List.nodup_cons.mpr ⟨hn,path_nodup hroute⟩

noncomputable def fromSimpleTree [Fintype V] (G : SimpleGraph V) (h : G.IsTree) : Tree V where
  graph := fromSimple G
  existsPath := fun a b => by
    obtain ⟨w,hw,_⟩ := h.existsUnique_path a b
    exact ⟨w.support.tail,mapWalk w hw⟩
  uniquePath := fun a b p q hp hq => by
    obtain ⟨wp,hwp,_,hpathp⟩ := liftWalk hp
    obtain ⟨wq,hwq,_,hpathq⟩ := liftWalk hq
    obtain ⟨w,_,hw⟩ := h.existsUnique_path a b
    have he := (hw wp hpathp).trans (hw wq hpathq).symm
    rw [he,hwq] at hwp
    exact (List.cons.inj hwp).2.symm

theorem dist_compat [Fintype V] {G : SimpleGraph V} (h : G.IsTree) (a b : V) :
    dist (fromSimpleTree G h) a b = G.dist a b := by
  obtain ⟨p,hp,hl⟩ := h.isConnected.exists_path_of_dist a b
  have hw : TPath (fromSimpleTree G h) a p.support.tail b := mapWalk p hp
  rw [dist_eq hw, List.length_tail, Walk.length_support]
  omega

theorem path_union_support [Fintype V] {G : SimpleGraph V} (h : G.IsTree)
    (r a b : V) :
    ∀ x ∈ a :: chosen (fromSimpleTree G h) a b,
      x ∈ r :: chosen (fromSimpleTree G h) r a ∨
      x ∈ r :: chosen (fromSimpleTree G h) r b := by
  classical
  let T := fromSimpleTree G h
  obtain ⟨wa,hwa,_,_⟩ := liftWalk (chosen_path T r a)
  obtain ⟨wb,hwb,_,_⟩ := liftWalk (chosen_path T r b)
  obtain ⟨wc,hwc,_,hpc⟩ := liftWalk (chosen_path T a b)
  let many := wa.reverse.append wb
  obtain ⟨w,_,hw⟩ := h.existsUnique_path a b
  have he := (hw wc hpc).trans (hw many.bypass many.bypass_isPath).symm
  intro x hx
  change x∈a::chosen T a b at hx
  rw [← hwc,he] at hx
  have hm := many.support_bypass_subset hx
  dsimp [many] at hm
  rw [Walk.support_append, Walk.support_reverse] at hm
  rcases List.mem_append.mp hm with hm|hm
  · left
    rw [← hwa,← List.mem_reverse]
    exact hm
  · right
    rw [← hwb]
    exact List.mem_of_mem_tail hm


theorem path_split {G : Graph V} {a p b} (hp : PathTo G a p b)
    (i : Nat) (hi : i ≤ p.length) :
    ∃ c l r, PathTo G a l c ∧ PathTo G c r b ∧ p=l++r ∧ l.length=i := by
  induction hp generalizing i with
  | @nil a =>
    have h0 : i=0 := by simpa using hi
    exact ⟨a,[],[],.nil,.nil,rfl,h0.symm⟩
  | @cons a x b p e hn hpath ih =>
    cases i with
    | zero => exact ⟨a,[],x::p,.nil,.cons e hn hpath,rfl,rfl⟩
    | succ i =>
      have hi' : i ≤ p.length := by simpa using hi
      obtain ⟨c,l,r,hL,hR,e',hl⟩ := ih i hi'
      have hna : a∉x::l := by
        intro h
        apply hn
        rw [e']
        exact List.mem_append_left r h
      exact ⟨c,x::l,r,.cons e hna hL,hR,by simp [e'],by simp [hl]⟩

theorem reverse_full {G : Graph V} {a p b} (h : PathTo G a p b) :
    ∃ q, PathTo G b q a ∧ b::q = (a::p).reverse := by
  induction h with
  | nil => exact ⟨[],.nil,rfl⟩
  | @cons a x b p e hn hpath ih =>
    obtain ⟨q,hq,hrev⟩ := ih
    have hna : a ∉ b::q := by rw [hrev,List.mem_reverse]; exact hn
    have hs : ∀ w∈b::q, w∉[a] := by
      intro w hw hwa
      have e : w=a := by simpa using hwa
      subst w
      exact hna hw
    refine ⟨q++[a],path_append hq (path_single (G.symm _ _ e)) hs,?_⟩
    change (b::q)++[a] = (a::x::p).reverse
    rw [hrev]
    simp

theorem avoid_opposite_branch {T : Tree V} {r z b p x}
    (h : TPath T r (z::p) b) (hx : z ∉ chosen T r x) :
    ∀ w ∈ r :: chosen T r x, w ∉ z::p := by
  intro w hw
  rcases List.mem_cons.mp hw with e|hmem
  · subst w
    exact (List.nodup_cons.mp (path_nodup h)).1
  · have hP := chosen_path T r x
    cases hQ : chosen T r x with
    | nil =>
      rw [hQ] at hmem
      contradiction
    | cons z' p' =>
      rw [hQ] at hP hmem
      have hne : z' ≠ z := by
        intro e
        subst z'
        exact hx (hQ ▸ List.mem_cons_self ..)
      exact path_different_branches_disjoint hP h hne _ hmem

theorem disjoint_nodup_length_le_card [Fintype V] {xs ys : List V}
    (hx : xs.Nodup) (hy : ys.Nodup) (hd : xs.Disjoint ys) :
    xs.length + ys.length ≤ Fintype.card V := by
  have hh : Disjoint xs.toFinset ys.toFinset := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact hd (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb)
  have h := Finset.card_le_univ (xs.toFinset ∪ ys.toFinset)
  rwa [Finset.card_union_of_disjoint hh,List.toFinset_card_of_nodup hx,
    List.toFinset_card_of_nodup hy] at h

theorem opposite_block_bound [Fintype V] {G : SimpleGraph V} (hG : G.IsTree)
    {r z b : V} {p : List V} {x y : V}
    (h : TPath (fromSimpleTree G hG) r (z::p) b)
    (hx : z ∉ chosen (fromSimpleTree G hG) r x)
    (hy : z ∉ chosen (fromSimpleTree G hG) r y) :
    G.dist x y + (z::p).length + 1 ≤ Fintype.card V := by
  let T := fromSimpleTree G hG
  have hex : (z::p).Nodup := (List.nodup_cons.mp (path_nodup h)).2
  have hpath := path_nodup (chosen_path T x y)
  have hdis : (x::chosen T x y).Disjoint (z::p) := by
    intro w hw
    rcases path_union_support hG r x y w hw with hh|hh
    · exact avoid_opposite_branch h hx _ hh
    · exact avoid_opposite_branch h hy _ hh
  have hsum := disjoint_nodup_length_le_card hpath hex hdis
  have hd : (chosen T x y).length = G.dist x y := dist_compat hG x y
  simp only [List.length_cons] at hsum ⊢
  omega

theorem three_two_same (A B C : Prop) :
    (A ∧ B) ∨ (¬ A ∧ ¬ B) ∨ (A ∧ C) ∨ (¬ A ∧ ¬ C) ∨
    (B ∧ C) ∨ (¬B ∧ ¬C) := by
  classical
  by_cases hA : A <;> by_cases hB : B <;> by_cases hC : C <;>
    simp [hA,hB,hC]

/-- Packing lemma for trees: choose a radius minimizer and among three
marked vertices find a pair whose distance plus the radius is at most
the order minus one. Uses a path with at least 2r−1 edges and the two sides
of its central cut. -/
theorem treePacking {W : Type*} [Fintype W] (G : SimpleGraph W) (hG : G.IsTree)
    (a b z : W) : ∃ c : W, ∃ M : Nat, (∀ x, G.dist c x ≤ M) ∧
      M + min (G.dist a b) (min (G.dist a z) (G.dist b z)) + 1 ≤ Fintype.card W := by
  classical
  let T := fromSimpleTree G hG
  have hCard : T.graph.verts.length = Fintype.card W := by
    change (Finset.univ : Finset W).toList.length = Fintype.card W
    simp
  have hN : 0 < T.graph.verts.length := by
    letI : Nonempty W := ⟨a⟩
    rw [hCard]
    exact Fintype.card_pos
  obtain ⟨⟨c,hc⟩,_⟩ := radiusAttains T hN
  refine ⟨c,radius T,?_,?_⟩
  · intro w
    have hd := ecc_upper T c w
    rw [hc,dist_compat hG c w] at hd
    exact hd
  · by_cases hr : 0 < radius T
    · obtain ⟨l,r,p,hp,hq⟩ := longPath T hN hr
      obtain ⟨v,L,R,hL,hR,hLR,hLen⟩ := path_split hp (p.length/2) (by omega)
      have hp1 : 1 ≤ p.length := by omega
      have hLength := congrArg List.length hLR
      rw [List.length_append] at hLength
      cases hhR : R with
      | nil =>
        rw [hhR] at hLength
        simp at hLength
        omega
      | cons w Q =>
        rw [hhR] at hR hLR hLength
        have evw : Adj T.graph v w := by cases hR with | cons e _ _ => exact e
        obtain ⟨L',hL',hRev⟩ := reverse_full hL
        have hBoth : ((l::L)++w::Q).Nodup := by
          have h := path_nodup hp
          rw [hLR] at h
          exact h
        have hwNot : w ∉ v::L' := by
          rw [hRev,List.mem_reverse]
          intro h
          exact (List.nodup_append.mp hBoth).2.2 h (List.mem_cons_self ..)
        have hBack : TPath T w (v::L') l := PathTo.cons (T.graph.symm _ _ evw) hwNot hL'
        have hLL : (v::L').length = L.length+1 := by
          rw [hRev,List.length_reverse]
          rfl
        have right_excludes_left (x : W) (hx : w∈chosen T v x) : v∉chosen T w x := by
          obtain ⟨q,hq⟩ := path_starts_iff_contains_neighbor evw (chosen_path T v x) hx
          have hvx := chosen_path T v x
          rw [hq] at hvx
          have tail : TPath T w q x := by cases hvx with | cons _ _ h => exact h
          have he := T.uniquePath _ _ _ _ (chosen_path T w x) tail
          rw [he]
          intro hv
          exact (List.nodup_cons.mp (path_nodup hvx)).1 (List.mem_cons_of_mem _ hv)
        have bound (x y : W) (he : (w∈chosen T v x ∧ w∈chosen T v y) ∨
                                 (w∉chosen T v x ∧ w∉chosen T v y)) :
            radius T + G.dist x y + 1 ≤ Fintype.card W := by
          rcases he with ht|ht
          · have hd := opposite_block_bound hG hBack
                (right_excludes_left x ht.1) (right_excludes_left y ht.2)
            rw [hLL] at hd
            omega
          · have hd := opposite_block_bound hG hR ht.1 ht.2
            simp only [List.length_cons] at hLength hd
            omega
        rcases three_two_same (w∈chosen T v a) (w∈chosen T v b) (w∈chosen T v z) with
          h|h|h|h|h|h
        · have hb := bound a b (Or.inl h)
          have hm := Nat.min_le_left (G.dist a b) (min (G.dist a z) (G.dist b z))
          omega
        · have hb := bound a b (Or.inr h)
          have hm := Nat.min_le_left (G.dist a b) (min (G.dist a z) (G.dist b z))
          omega
        · have hb := bound a z (Or.inl h)
          have hm := Nat.le_trans (Nat.min_le_right (G.dist a b) (min (G.dist a z) (G.dist b z)))
            (Nat.min_le_left (G.dist a z) (G.dist b z))
          omega
        · have hb := bound a z (Or.inr h)
          have hm := Nat.le_trans (Nat.min_le_right (G.dist a b) (min (G.dist a z) (G.dist b z)))
            (Nat.min_le_left (G.dist a z) (G.dist b z))
          omega
        · have hb := bound b z (Or.inl h)
          have hm := Nat.le_trans (Nat.min_le_right (G.dist a b) (min (G.dist a z) (G.dist b z)))
            (Nat.min_le_right (G.dist a z) (G.dist b z))
          omega
        · have hb := bound b z (Or.inr h)
          have hm := Nat.le_trans (Nat.min_le_right (G.dist a b) (min (G.dist a z) (G.dist b z)))
            (Nat.min_le_right (G.dist a z) (G.dist b z))
          omega
    · have hr0 : radius T = 0 := by omega
      have hb := ecc_upper T c b
      have ha := ecc_upper T c a
      have ht := distTriangle T a c b
      rw [dist_symm T a c] at ht
      rw [hc,hr0] at ha hb
      have hd := dist_compat hG a b
      change dist T a b = G.dist a b at hd
      have hb0 : G.dist a b = 0 := by omega
      rw [hr0,hb0,Nat.zero_min]
      omega

#print axioms treePacking
end Graffiti232Tree

/- Proof module: Verify232 -/
set_option warningAsError true
set_option linter.unusedSectionVars false
noncomputable section
open Finset
namespace Graffiti232
universe u
variable {V : Type u} [Fintype V]

def ecc (G : SimpleGraph V) (v : V) : ℕ := Finset.univ.sup (G.dist v)
def diam (G : SimpleGraph V) : ℕ := Finset.univ.sup (ecc G)
def rad (G : SimpleGraph V) : ℕ := sInf (Set.range (ecc G))
def Periph (G : SimpleGraph V) : Set V := {v | ecc G v = diam G}

def dP (G : SimpleGraph V) (v : V) : ℕ :=
  sInf {k : ℕ | ∃ p ∈ Periph G, G.dist v p = k}

def eccP (G : SimpleGraph V) : ℕ := Finset.univ.sup (dP G)

theorem exists_ecc (G : SimpleGraph V) [Nonempty V] (v : V) :
    ∃ w, G.dist v w = ecc G v := by
  obtain ⟨w,_,hw⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset V) Finset.univ_nonempty (G.dist v)
  exact ⟨w,hw.symm⟩

theorem exists_diam (G : SimpleGraph V) [Nonempty V] :
    ∃ a b, a ∈ Periph G ∧ b ∈ Periph G ∧ G.dist a b = diam G := by
  obtain ⟨a,_,ha⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset V) Finset.univ_nonempty (ecc G)
  obtain ⟨b,hb⟩ := exists_ecc G a
  have hde : G.dist a b = diam G := hb.trans ha.symm
  have hb' : ecc G b = diam G := by
    apply Nat.le_antisymm
    · exact Finset.le_sup (f := ecc G) (Finset.mem_univ b)
    · calc
        diam G = G.dist b a := hde.symm.trans SimpleGraph.dist_comm
        _ ≤ ecc G b := Finset.le_sup (f := G.dist b) (Finset.mem_univ a)
  exact ⟨a,b,ha.symm,hb',hde⟩

theorem exists_farthest (G : SimpleGraph V) [Nonempty V] :
    ∃ z, dP G z = eccP G := by
  obtain ⟨z,_,hz⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset V) Finset.univ_nonempty (dP G)
  exact ⟨z,hz.symm⟩

theorem dP_le (G : SimpleGraph V) (v p : V) (hp : p ∈ Periph G) :
    dP G v ≤ G.dist v p := Nat.sInf_le ⟨p,hp,rfl⟩

theorem connected_has_neighbor (G : SimpleGraph V) (hc : G.Connected)
    (hn : 1 < Fintype.card V) (v : V) : ∃ w, G.Adj v w := by
  obtain ⟨w,hw⟩ := Fintype.exists_ne_of_one_lt_card hn v
  obtain ⟨p⟩ := hc v w
  cases p with
  | nil => exact False.elim (hw rfl)
  | cons =>
    rename_i w h p
    exact ⟨_,h⟩

theorem exists_tdom_min (G : SimpleGraph V) (hc : G.Connected)
    (hn : 1 < Fintype.card V) :
    ∃ D : Finset V, Graffiti271.TotalDominates G D ∧ D.card = Graffiti271.totalDominationNumber G := by
  have hall : Graffiti271.TotalDominates G Finset.univ := by
    intro v
    obtain ⟨w,hw⟩ := connected_has_neighbor G hc hn v
    exact ⟨w,Finset.mem_univ _,hw⟩
  have hnon : {k : ℕ | ∃ D : Finset V, Graffiti271.TotalDominates G D ∧ D.card = k}.Nonempty :=
    ⟨Fintype.card V, Finset.univ,hall,Finset.card_univ⟩
  unfold Graffiti271.totalDominationNumber
  exact Nat.sInf_mem hnon

theorem dist_lift_induced (G : SimpleGraph V)
    (C : Finset V) (T : SimpleGraph ↑(C : Set V))
    (hsub : T ≤ G.induce (C : Set V)) (hc : T.Connected)
    (x y : ↑(C : Set V)) :
    G.dist x.1 y.1 ≤ T.dist x y := by
  let f : T →g G :=
    ⟨Subtype.val, fun h => hsub h⟩
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist x y
  have hh := G.dist_le (p.map f)
  rw [SimpleGraph.Walk.length_map, hp] at hh
  exact hh

/-- Intermediate connector: all catalogue graph-metric content other than the
separate finite-tree packing theorem. -/
theorem outer
    (treePacking : ∀ {W : Type u} [Fintype W] (T : SimpleGraph W), T.IsTree →
      ∀ a b z : W, ∃ (c : W) (M : ℕ), (∀ x, T.dist c x ≤ M) ∧
        M + min (T.dist a b) (min (T.dist a z) (T.dist b z)) + 1 ≤ Fintype.card W)
    (G : SimpleGraph V) (hc : G.Connected) (hn : 1 < Fintype.card V) :
    rad G + eccP G ≤ 2 * Graffiti271.totalDominationNumber G := by
  classical
  letI : Nonempty V := hc.nonempty
  obtain ⟨D,hD,ht⟩ := exists_tdom_min G hc hn
  obtain ⟨C,hDC,hCI,hC⟩ := GraffitiCore.exists_connected_core G hc D hD
  have hcomp := GraffitiCore.components_le_half G D hD
  have ht₂ : 2 ≤ D.card := by
    let v : V := Classical.choice hc.nonempty
    obtain ⟨u,hu,_⟩ := hD v
    obtain ⟨w,hw,huw⟩ := hD u
    exact Finset.one_lt_card.mpr ⟨u,hu,w,hw,huw.ne⟩
  have hC₂ : C.card + 2 ≤ 2 * Graffiti271.totalDominationNumber G := by omega
  obtain ⟨T,hT,hTree⟩ := hCI.exists_isTree_le
  let f (v : V) : ↑(C : Set V) :=
    ⟨Classical.choose (hD v), hDC (Classical.choose_spec (hD v)).1⟩
  have hf (v : V) : G.dist v (f v).1 = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr (Classical.choose_spec (hD v)).2
  have hcompare (v w : V) : G.dist v w ≤ T.dist (f v) (f w) + 2 := by
    have h₁ := hc.dist_triangle (u:=v) (v:=(f v).1) (w:=w)
    have h₂ := hc.dist_triangle (u:=(f v).1) (v:=(f w).1) (w:=w)
    have h₃ := dist_lift_induced G C T hT hTree.isConnected (f v) (f w)
    have h₄ : G.dist (f w).1 w = 1 := SimpleGraph.dist_comm.trans (hf w)
    rw [hf] at h₁
    rw [h₄] at h₂
    omega
  have hrad (c : ↑(C : Set V)) (M : ℕ) (hM : ∀ x, T.dist c x ≤ M) : rad G ≤ M+1 := by
    have hle : rad G ≤ ecc G c.1 := by
      unfold rad
      apply Nat.sInf_le
      exact ⟨c.1,rfl⟩
    apply Nat.le_trans hle
    unfold ecc
    apply Finset.sup_le
    intro v _
    have h₁ := hc.dist_triangle (u:=c.1) (v:=(f v).1) (w:=v)
    have h₂ := dist_lift_induced G C T hT hTree.isConnected c (f v)
    have h₃ : G.dist (f v).1 v = 1 := SimpleGraph.dist_comm.trans (hf v)
    rw [h₃] at h₁
    have h₄ := hM (f v)
    omega
  obtain ⟨a,b,ha,hb,hab⟩ := exists_diam G
  obtain ⟨z,hz⟩ := exists_farthest G
  have heab : eccP G ≤ G.dist a b := by
    rw [← hz, hab]
    exact (dP_le G z a ha).trans (le_trans (Finset.le_sup (f := G.dist z) (Finset.mem_univ a))
      (Finset.le_sup (f := ecc G) (Finset.mem_univ z)))
  have heaz : eccP G ≤ G.dist a z := by
    rw [SimpleGraph.dist_comm, ← hz]
    exact dP_le G z a ha
  have hebz : eccP G ≤ G.dist b z := by
    rw [SimpleGraph.dist_comm, ← hz]
    exact dP_le G z b hb
  obtain ⟨c,M,hM,hPack⟩ := treePacking T hTree (f a) (f b) (f z)
  have hPack' : M + min (T.dist (f a) (f b)) (min (T.dist (f a) (f z)) (T.dist (f b) (f z))) + 1 ≤ C.card := by
    have hcardEq : Fintype.card (↑(C : Set V)) = C.card := Fintype.card_coe C
    rwa [hcardEq] at hPack
  have hePack : eccP G ≤ min (T.dist (f a) (f b)) (min (T.dist (f a) (f z)) (T.dist (f b) (f z))) + 2 := by
    have h₁ := hcompare a b
    have h₂ := hcompare a z
    have h₃ := hcompare b z
    omega
  have hr := hrad c M hM
  omega

/-- Exact Graffiti.pc #232, with a zero eccentricity when all vertices are peripheral. -/
theorem conjecture232 (G : SimpleGraph V) (hc : G.Connected)
    (hn : 1 < Fintype.card V) : rad G + eccP G ≤
      2 * Graffiti271.totalDominationNumber G :=
  outer (fun T hT a b z => Graffiti232Tree.treePacking T hT a b z) G hc hn

#print axioms conjecture232
end Graffiti232
