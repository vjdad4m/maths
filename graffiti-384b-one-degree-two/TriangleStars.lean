import FrontierTwentyNine384b

namespace Graffiti384b.QuotaEar
open Finset SimpleGraph LowSample
open private Repair.triangles_le_choose from Repair384b
open private Prune.links Prune.outside_zero from Prune384b
open private LowSample.two_degree from LowSample384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Keep all triangle edges and every edge incident to a prescribed vertex. -/
def triangleStars (pins : Finset V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ ((∃ z,G.Adj x z ∧ G.Adj y z) ∨ x∈pins ∨ y∈pins)
  symm := by
    intro x y h
    refine ⟨h.1.symm,?_⟩
    rcases h.2 with ⟨z,xz,yz⟩|xp|yp
    · exact Or.inl ⟨z,yz,xz⟩
    all_goals tauto
  loopless := fun _ h => h.1.ne rfl

instance (pins : Finset V) : DecidableRel (triangleStars G pins).Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

theorem scores (pins : Finset V) (x : V) : trianglesAt (triangleStars G pins) x=trianglesAt G x := by
  let J := triangleStars G pins
  change (Prune.links J x).card=(Prune.links G x).card
  congr 1
  ext p
  simp only [Prune.links,mem_filter,mem_powersetCard]
  constructor
  · rintro ⟨⟨sub,sz⟩,cl⟩
    exact ⟨⟨fun v vm => (G.mem_neighborFinset ..).mpr ((J.mem_neighborFinset ..).mp (sub vm)).1,sz⟩,
      fun a am b bm ne => (cl a am b bm ne).1⟩
  · rintro ⟨⟨sub,sz⟩,cl⟩
    have edge {v : V} (vm : v∈p) := (G.mem_neighborFinset ..).mp (sub vm)
    refine ⟨⟨?_,sz⟩,?_⟩
    · intro v vm
      obtain ⟨w,wm,wv⟩ := exists_ne_of_one_lt_card (by omega : 1<p.card) v
      exact (J.mem_neighborFinset ..).mpr ⟨edge vm,Or.inl ⟨w,edge wm,cl _ vm _ wm wv.symm⟩⟩
    · intro a am b bm ne
      exact ⟨cl a am b bm ne,Or.inl ⟨x,(edge am).symm,(edge bm).symm⟩⟩


theorem star_degree {pins : Finset V} {v : V} (vm : v∈pins) : (triangleStars G pins).degree v=G.degree v := by
  let J := triangleStars G pins
  have eq : J.neighborFinset v=G.neighborFinset v := by
    ext w; simp only [mem_neighborFinset]
    exact ⟨And.left,fun edge => ⟨edge,Or.inr (Or.inl vm)⟩⟩
  simpa only [card_neighborFinset_eq_degree] using congrArg Finset.card eq

theorem degree_le (pins : Finset V) (v : V) : (triangleStars G pins).degree v≤G.degree v := by
  let J := triangleStars G pins
  simpa only [card_neighborFinset_eq_degree] using card_le_card
    (show J.neighborFinset v⊆G.neighborFinset v from fun w wm =>
      (G.mem_neighborFinset ..).mpr ((J.mem_neighborFinset ..).mp wm).1)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem triangle_away {pins : Finset V} {x y : V} (xp : x∉pins) (yp : y∉pins)
    (edge : (triangleStars G pins).Adj x y) :
    ∃z,(triangleStars G pins).Adj x z ∧ (triangleStars G pins).Adj y z := by
  obtain ⟨xy,tr⟩ := edge
  obtain ⟨z,xz,yz⟩ := tr.resolve_right (fun h => h.elim xp yp)
  exact ⟨z,⟨xz,Or.inl ⟨y,xy,yz.symm⟩⟩,⟨yz,Or.inl ⟨x,xy.symm,xz.symm⟩⟩⟩

theorem high_of_score {pins : Finset V} {v : V} (lo : 2≤trianglesAt G v) : v∈high (triangleStars G pins) := by
  let J := triangleStars G pins
  have bd := Repair.triangles_le_choose J v
  rw [show trianglesAt J v=trianglesAt G v from scores G pins v] at bd
  apply mem_filter.mpr ⟨mem_univ _,?_⟩
  change 3≤J.degree v
  by_contra! low
  have lim := Nat.choose_le_choose 2 (show J.degree v≤2 by omega)
  rw [Nat.choose_self] at lim; omega

theorem transfers (pins : Finset V) (sol : gamma (triangleStars G pins)≤bound (triangleStars G pins)) :
    gamma G≤bound G := by
  let J := triangleStars G pins
  have same : types J=types G := congrArg (fun g : V→ℕ => univ.image g) (funext (scores G pins))
  obtain ⟨D,dom,sz⟩ := Nat.sInf_mem (show {k : ℕ | ∃ d,TwoDominates J d ∧ d.card=k}.Nonempty from
    ⟨_,univ,fun _ out => (out (mem_univ _)).elim,rfl⟩)
  have dg : TwoDominates G D := fun v out => (dom v out).trans (card_le_card
    (show D.filter (J.Adj v)⊆D.filter (G.Adj v) from fun _ m => mem_filter.mpr ⟨(mem_filter.mp m).1,(mem_filter.mp m).2.1⟩))
  exact (show gamma G≤gamma J from Nat.sInf_le ⟨D,dg,sz⟩).trans (by change gamma J≤bound J at sol; simpa only [bound,same] using sol)

end Graffiti384b.QuotaEar
#print axioms Graffiti384b.QuotaEar.scores
#print axioms Graffiti384b.QuotaEar.triangle_away
#print axioms Graffiti384b.QuotaEar.transfers
#print axioms Graffiti384b.QuotaEar.star_degree
#print axioms Graffiti384b.QuotaEar.degree_le
#print axioms Graffiti384b.QuotaEar.high_of_score
