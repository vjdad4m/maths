import Normalize189
open SimpleGraph SimpleGraph.Walk Finset Graffiti189LongestPath
open Graffiti189LongestPath.Normalize Graffiti189LongestPath.OneSlack Graffiti189LongestPath.Rigidity
open private Graffiti189LongestPath.outside_edge Graffiti189LongestPath.boundary_card_of_connectivity
  Graffiti189LongestPath.pin_data from SmallSeparator189
open private Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem from OneSlack189
set_option warningAsError true
set_option linter.unusedSectionVars false

namespace Graffiti189LongestPath.HighDichotomy
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- No longest path can have just one omitted vertex in the first slack regime:
all longest paths would have just one, so all satisfy the old outside-edge tie breaker. -/
theorem not_one_omitted (hc : G.Connected) (k : Nat) (hk : 3 ≤ k)
    (cap : ∀ v, (EvenFrom G v).card ≤ k+3)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (deg : ∀ u v : V, u ≠ v → k+2 ≤ G.degree u ∨ k+2 ≤ G.degree v)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    {x : V} (hx : x ∉ p.support) :
    ∃ y, y ∉ p.support ∧ y ≠ x := by
  classical
  by_contra hn
  have alone {y : V} (hy : y ∉ p.support) : y = x :=
    Classical.byContradiction (fun ne => hn ⟨y,hy,ne⟩)
  let rem {u v : V} (q : G.Walk u v) : Finset V := univ \ q.support.toFinset
  have hrem : rem p = {x} := by
    ext y
    simp only [rem,mem_sdiff,mem_univ,true_and,List.mem_toFinset,mem_singleton]
    exact ⟨alone,fun e => e.symm ▸ hx⟩
  have cnt {u v : V} {q : G.Walk u v} (h : IsLongest q) : (rem q).card = 1 := by
    have hl := Nat.le_antisymm (hp.2 u v q h.1) (h.2 a b p hp.1)
    have ep := List.toFinset_card_of_nodup hp.1.support_nodup
    have eq := List.toFinset_card_of_nodup h.1.support_nodup
    rw [length_support] at ep eq
    have ha := card_sdiff_add_card_eq_card (subset_univ p.support.toFinset)
    have hb := card_sdiff_add_card_eq_card (subset_univ q.support.toFinset)
    change (rem p).card + p.support.toFinset.card = _ at ha
    change (rem q).card + q.support.toFinset.card = _ at hb
    rw [hrem,card_singleton] at ha
    omega
  have eo : EdgeOptimal p := by
    refine ⟨hp,fun u v q hq => ?_⟩
    have hn : (OmittedEdges q).card = 0 := by
      apply card_eq_zero.mpr
      apply eq_empty_iff_forall_not_mem.mpr
      intro yz hz
      have hz := (mem_filter.mp hz).2
      have hy : yz.1 ∈ rem q := by simpa [rem] using hz.1
      have hw : yz.2 ∈ rem q := by simpa [rem] using hz.2.1
      have h := card_le_one.mp (show (rem q).card ≤ 1 by rw [cnt hq]) _ hy _ hw
      exact hz.2.2.ne h
    rw [hn]
    exact Nat.zero_le _
  have hn : ∀ y, G.Adj x y → y ∈ p.support := by
    intro y e
    apply Classical.byContradiction
    intro h
    exact e.ne (alone h).symm
  have he := (at_most_two_pins_one_slack hc k (by omega)
    (fun v => distanceTwo_le_of_even (k+2) v (cap v)) conn deg eo hx).2 hn
  omega

/-- A nonspanning longest path in the first slack regime always has a
high-degree omitted vertex that directly attaches to the path. -/
theorem has_high_active (hc : G.Connected) (k : Nat) (hk : 3 ≤ k)
    (cap : ∀ v, (EvenFrom G v).card ≤ k+3)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (deg : ∀ u v : V, u ≠ v → k+2 ≤ G.degree u ∨ k+2 ≤ G.degree v)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (nonspan : ∃ x, x ∉ p.support) :
    ∃ x, x ∉ p.support ∧ k+2 ≤ G.degree x ∧ (Pins p x).Nonempty := by
  classical
  obtain ⟨x,hx,y,hy,ex⟩ := Graffiti189LongestPath.outside_edge p hc nonspan
  by_contra hNo
  have low {u v : V} (hu : u ∉ p.support) (hv : v ∈ p.support) (e : G.Adj u v) :
      G.degree u < k+2 := by
    by_contra! h
    obtain ⟨i,hi,_⟩ := Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem hp hu hv e
    exact hNo ⟨u,hu,h,i,hi⟩
  have lowx := low hx hy ex
  obtain ⟨z,hz,ne⟩ := not_one_omitted hc k hk cap conn deg hp hx
  let A : Finset V := univ.filter (fun u => u ∉ p.support ∧ u ≠ x)
  have ha (u : V) : u ∈ A ↔ u ∉ p.support ∧ u ≠ x := by simp [A]
  have zal : z ∈ A := (ha z).mpr ⟨hz,ne⟩
  have aa : a ∉ A := fun h => ((ha _).mp h).1 p.start_mem_support
  have ab : a ∉ ({x}:Finset V) := by
    rw [mem_singleton]
    exact fun e => hx (e ▸ p.start_mem_support)
  have dis : Disjoint A ({x}:Finset V) := disjoint_left.mpr (fun u hu hv =>
    ((ha u).mp hu).2 (mem_singleton.mp hv))
  have bnd : ∀ u ∈ A, ∀ v ∉ A, G.Adj u v → v ∈ ({x}:Finset V) := by
    intro u hu v hv e
    by_cases h : v = x
    · exact mem_singleton.mpr h
    have vOn : v ∈ p.support := by
      by_contra hn
      exact hv ((ha v).mpr ⟨hn,h⟩)
    have hLow := low ((ha u).mp hu).1 vOn e
    rcases deg u x ((ha u).mp hu).2 with h|h <;> omega
  have hc' := Graffiti189LongestPath.boundary_card_of_connectivity k conn zal aa ab dis bnd
  simp at hc'
  omega

#print axioms not_one_omitted
#print axioms has_high_active
end Graffiti189LongestPath.HighDichotomy

namespace Graffiti189LongestPath.HighDichotomy
open Graffiti189LongestPath.PinRun
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Exact remaining alternatives for a high omitted attachment on the normalized
longest path at connectivity at least d−2 (here d=k+2≥5). -/
theorem normalized_attachment_dichotomy
    (hc : G.Connected) (k : Nat) (hk : 3 ≤ k)
    (cap : ∀ v, (EvenFrom G v).card ≤ k+3)
    (conn : ∀ S : Finset V, S.card<k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (deg : ∀ u v : V, u ≠ v → k+2≤G.degree u ∨ k+2≤G.degree v)
    (nontrace : ¬∃ (a b : V) (p : G.Walk a b), p.IsPath ∧ ∀ v, v ∈ p.support) :
    ∃ (a b : V) (p : G.Walk a b) (x : V), EdgeMinAvoid (k+2) p ∧ x ∉ p.support ∧
      k+2≤G.degree x ∧
      (((Pins p x).card = 1 ∧ (Shell G x 4).card≤1 ∧ ∀ z, G.dist x z≤4) ∨
       ((Pins p x).card = 2 ∧ PairedPins p x = ∅ ∧ (DistanceTwo G x).card = k+2 ∧
          (External G (OmittedStar p x)).card = k ∧ ∀ z, G.dist x z≤3)) := by
  classical
  have cap' : ∀ v, (EvenFrom G v).card ≤ (k+2)+1 := by
    intro v
    exact cap v
  obtain ⟨a,b,p,hp⟩ := exists_edgeMinAvoid hc (k+2) deg
  have nonspan : ∃ x, x ∉ p.support := by
    by_contra! hh
    exact nontrace ⟨a,b,p,hp.1.1.1,hh⟩
  obtain ⟨x,hx,hd,i,hi⟩ := has_high_active hc k hk cap conn deg hp.1.1 nonspan
  refine ⟨a,b,p,x,hp,hx,hd,?_⟩
  have hN := normalized_high_omission hc (k+2) k (by omega) le_rfl cap' conn hp hx hd i hi
  have ci : 0 < (Pins p x).card := card_pos.mpr ⟨i,hi⟩
  have ex := (Graffiti189LongestPath.pin_data hi).2
  by_cases h : (Pins p x).card = 1
  · left
    refine ⟨h,by omega,fun z => ?_⟩
    by_contra! hf
    have lower := shell_card_of_far hc k conn (x:=x) (y:=z) (i:=4) (by decide) (by omega)
    omega
  · right
    have d2 : (Pins p x).card = 2 := by omega
    have none : PairedPins p x = ∅ := eq_empty_iff_forall_not_mem.mpr (by
      intro j hj
      obtain ⟨hj,q,hq,eq|eq⟩ := mem_filter.mp hj
      · exact (normalized_high_omission hc (k+2) k (by omega) le_rfl cap' conn hp hx hd q hq).2
          (eq.symm ▸ hj)
      · exact (normalized_high_omission hc (k+2) k (by omega) le_rfl cap' conn hp hx hd j hj).2
          (eq.symm ▸ hq))
    obtain ⟨w,ew,hw⟩ := omitted_has_omitted_neighbor hc hp.1.1 hx hd ⟨_,ex⟩
      (distanceTwo_le_of_even _ _ (cap x))
    obtain ⟨hD,hE,hB⟩ := double_porter_saturated_one_slack hc k hp.1.1 hx d2 (cap x) conn hw ew
    have hb : (External G (OmittedStar p x)).card = k := by
      rcases hB with hB|hB
      · exact hB.2
      · simp [none] at hB
    exact ⟨d2,none,hD,hb,hE⟩

#print axioms normalized_attachment_dichotomy
end Graffiti189LongestPath.HighDichotomy
