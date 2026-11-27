import Proof271

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
