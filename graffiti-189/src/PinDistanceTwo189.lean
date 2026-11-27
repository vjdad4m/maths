import Rigidity189

namespace Graffiti189LongestPath.Rigidity
open SimpleGraph SimpleGraph.Walk Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
private theorem path_d2_mem (hc : G.Connected) {a b u v w : V}
    {p : G.Walk a b} (hw : w ∈ p.support) (hne : u ≠ w)
    (hn : ¬ G.Adj u w) (uv : G.Adj u v) (vw : G.Adj v w) :
    w ∈ (DistanceTwo G u).filter (· ∈ p.support) := by
  have lower := hc.one_lt_dist_of_ne_of_not_adj hne hn
  have upper := G.dist_le (Walk.cons uv (Walk.cons vw .nil))
  simp only [length_cons,length_nil] at upper
  have eq : G.dist u w = 2 := by omega
  classical
  simp [DistanceTwo,hw,eq]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem endpoint_neighbors_on_path {a b z : V} {p : G.Walk a b} (hp : IsLongest p)
    (hz : G.Adj a z ∨ G.Adj b z) : z ∈ p.support := by
  by_contra hm
  rcases hz with e|e
  · have m := hp.2 z b (.cons e.symm p) (hp.1.cons hm)
    simp at m
  · have path : (Walk.cons e.symm p.reverse).reverse.IsPath :=
      (hp.1.reverse.cons (by simpa using hm)).reverse
    have m := hp.2 a z _ path
    simp at m

private theorem atLeastTwo_from_endpoint (hc : G.Connected)
    {a b v e : V} {p : G.Walk a b} (hp : IsLongest p) (he : e = a ∨ e = b)
    (degree : 3 ≤ G.degree e) (adj : G.Adj e v)
    (no : ∀ z, G.Adj e z → z ≠ v → ¬G.Adj v z) :
    2 ≤ ((DistanceTwo G v).filter (· ∈ p.support)).card := by
  let S := (G.neighborFinset e).erase v
  have hv : v ∈ G.neighborFinset e := (G.mem_neighborFinset _ _).mpr adj
  have ns : 2 ≤ S.card := by
    rw [show S.card = (G.neighborFinset e).card-1 from card_erase_of_mem hv,
      card_neighborFinset_eq_degree]
    omega
  apply ns.trans (Finset.card_le_card ?_)
  intro z hz
  obtain ⟨hn,hm⟩ := mem_erase.mp hz
  have ez := (G.mem_neighborFinset _ _).mp hm
  have zpath := endpoint_neighbors_on_path hp (he.elim (fun h => Or.inl (h ▸ ez))
    (fun h => Or.inr (h ▸ ez)))
  exact path_d2_mem hc zpath (Ne.symm hn) (no z ez hn) adj.symm ez

/-- When no path neighbor of a pin is available beyond the two flanks and
well-separated additional pins, there are at least two path vertices at
distance two from this pin, even if a flank is a path endpoint. -/
theorem pin_has_two_on_path (hc : G.Connected)
    (bound : ∀ x, (EvenFrom G x).card ≤ 4)
    (conn : ∀ S : Finset V, S.card < 2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V, u ≠ v → 3 ≤ G.degree u ∨ 3 ≤ G.degree v)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (ha : 3 ≤ G.degree a) (hb : 3 ≤ G.degree b)
    {x : V} (hx : x ∉ p.support) {i : ℕ} (hi : i ∈ Pins p x)
    (hN : ∀ j ≤ p.length, G.Adj (p.getVert i) (p.getVert j) →
      j=i-1 ∨ j=i+1 ∨ ∃ y ∉ p.support, j∈Pins p y ∧ (i+3≤j ∨ j+3≤i)) :
    2 ≤ ((DistanceTwo G (p.getVert i)).filter (· ∈ p.support)).card := by
  have hil : i < p.length := mem_range.mp (mem_filter.mp hi).1
  have hip : 0 < i := by
    by_contra! h
    have eq : i=0 := by omega
    have e : G.Adj x (p.getVert i) := (mem_filter.mp hi).2
    rw [eq,getVert_zero] at e
    exact hx (endpoint_neighbors_on_path hp (Or.inl e.symm))
  by_cases left : i = 1
  · have ei : G.Adj a (p.getVert i) := by
      have e := p.adj_getVert_succ (i:=0) (by omega)
      rw [getVert_zero] at e
      rwa [left]
    apply atLeastTwo_from_endpoint hc hp (Or.inl rfl) ha ei
    intro z ez nez ep
    have zpath := endpoint_neighbors_on_path hp (Or.inl ez)
    obtain ⟨j,ej,hj⟩ := mem_support_iff_exists_getVert.mp zpath
    rcases hN j hj (ej.symm ▸ ep) with eq|eq|⟨y,hy,yp,hgap⟩
    · have j0 : j=0 := by omega
      rw [j0,getVert_zero] at ej
      exact ez.ne ej
    · exact start_not_adj_pin_successor hp hx hi (by rwa [← eq,ej])
    · exact start_not_adj_pin_of_two_le hc 2 bound conn degree hp hy yp (by omega) (by rwa [ej])
  by_cases right : i+1 = p.length
  · have ei : G.Adj b (p.getVert i) := by
      have e := p.adj_getVert_succ (i:=i) hil
      rw [right,getVert_length] at e
      exact e.symm
    apply atLeastTwo_from_endpoint hc hp (Or.inr rfl) hb ei
    intro z ez nez ep
    have zpath := endpoint_neighbors_on_path hp (Or.inr ez)
    obtain ⟨j,ej,hj⟩ := mem_support_iff_exists_getVert.mp zpath
    rcases hN j hj (ej.symm ▸ ep) with eq|eq|⟨y,hy,yp,hgap⟩
    · exact end_not_adj_pin_predecessor hp hx hi (by rwa [← eq,ej])
    · rw [eq,right,getVert_length] at ej
      exact ez.ne ej
    · exact end_not_adj_pin_of_two_le hc 2 bound conn degree hp hy yp (by omega) (by rwa [ej])
  have ineq : 2 ≤ i := by omega
  have istep : i+2 ≤ p.length := by omega
  have e₀ (j : ℕ) (hj : j ≤ p.length) (hne : i ≠ j) : p.getVert i ≠ p.getVert j :=
    fun h => hne (hp.1.getVert_injOn hil.le hj h)
  have hnot₁ : ¬ G.Adj (p.getVert i) (p.getVert (i-2)) := by
    intro e
    rcases hN (i-2) (by omega) e with h|h|⟨_,_,_,h⟩ <;> omega
  have hnot₂ : ¬ G.Adj (p.getVert i) (p.getVert (i+2)) := by
    intro e
    rcases hN (i+2) istep e with h|h|⟨_,_,_,h⟩ <;> omega
  have eprev : G.Adj (p.getVert (i-1)) (p.getVert i) := by
    have e := p.adj_getVert_succ (i:=i-1) (by omega)
    have eq : i-1+1=i := by omega
    rwa [eq] at e
  have eprev₂ : G.Adj (p.getVert (i-2)) (p.getVert (i-1)) := by
    have e := p.adj_getVert_succ (i:=i-2) (by omega)
    have eq : i-2+1=i-1 := by omega
    rwa [eq] at e
  have D₁ := path_d2_mem hc (p.getVert_mem_support (i-2))
    (e₀ (i-2) (by omega) (by omega)) hnot₁ eprev.symm eprev₂.symm
  have D₂ := path_d2_mem hc (p.getVert_mem_support (i+2))
    (e₀ (i+2) istep (by omega)) hnot₂
    (p.adj_getVert_succ hil) (p.adj_getVert_succ (by omega : i+1 < p.length))
  have distinct : p.getVert (i-2) ≠ p.getVert (i+2) := by
    intro h
    have he := hp.1.getVert_injOn (by omega : i-2≤p.length) istep h
    omega
  have sub : {p.getVert (i-2),p.getVert (i+2)} ⊆
      (DistanceTwo G (p.getVert i)).filter (· ∈ p.support) := by
    simp [insert_subset,D₁,D₂]
  have cnt := Finset.card_le_card sub
  simpa [distinct] using cnt

#print axioms pin_has_two_on_path
end Graffiti189LongestPath.Rigidity
