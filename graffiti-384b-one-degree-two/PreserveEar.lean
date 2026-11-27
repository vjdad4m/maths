import SingleTip
import TriangleStars

namespace Graffiti384b.QuotaEar
open Finset SimpleGraph LowSample
open private Repair.triangles_le_choose from Repair384b
open private Prune.links Prune.outside_zero from Prune384b
open private LowSample.two_degree from LowSample384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- An arbitrary finite graph with one ear meets the catalogue bound if
all high vertices except possibly one lie on at least two triangles. -/
theorem one_low_high {e f : V} (only : twos G={e}) (q : (types G).card≤(nonleaves G).card)
    (rich : ∀ v∈high G,v≠f → 2≤trianglesAt G v) : gamma G≤bound G := by
  classical
  let pins : Finset V := {e,f}
  let J := triangleStars G pins
  have sc : ∀ x,trianglesAt J x=trianglesAt G x := scores G pins
  have same : types J=types G := congrArg (fun g : V→ℕ => univ.image g) (funext sc)
  have special {v : V} (p : v=e ∨ v=f) : J.degree v=G.degree v := by
    apply star_degree G (pins:=pins)
    simpa [pins] using p
  have mono (v : V) : J.degree v≤G.degree v := degree_le G pins v
  have highEq : high J=high G := by
    ext v; simp only [high,mem_filter,mem_univ,true_and]
    refine ⟨fun h => h.trans (mono v),fun h => ?_⟩
    by_cases vf : v=f
    · rwa [special (Or.inr vf)]
    · exact (mem_filter.mp (high_of_score G (pins:=pins) (rich v (mem_filter.mpr ⟨mem_univ _,h⟩) vf))).2
  have et : e∈twos G := only ▸ mem_singleton_self _
  have de := LowSample.two_degree G et
  have non : nonleaves J=nonleaves G := by
    ext v; constructor
    · intro vm; exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp vm).2.trans (mono v)⟩
    · intro vm
      by_cases vh : v∈high G
      · have m := (mem_filter.mp (highEq ▸ vh : v∈high J)).2
        exact mem_filter.mpr ⟨mem_univ _,by omega⟩
      · have vt : v∈twos G := mem_sdiff.mpr ⟨vm,vh⟩
        obtain rfl := mem_singleton.mp (only ▸ vt)
        exact mem_filter.mpr ⟨mem_univ _,by rw [special (Or.inl rfl),de]⟩
  have jt : twos J={e} := by change nonleaves J\high J=_; rw [non,highEq]; exact only
  have js := one_exception J (f:=f) jt (by rwa [same,non]) (by
    intro u v ue ve uf vf h
    exact triangle_away G (pins:=pins) (by simp [pins,ue,uf]) (by simp [pins,ve,vf]) h)
  exact transfers G pins js

/-- At equal diversity and nonleaf count, the collection of nonleaves
on at most one triangle has at most two vertices. -/
theorem low_scores (equal : (types G).card=(nonleaves G).card) :
    ((nonleaves G).filter (fun v => trianglesAt G v≤1)).card≤2 := by
  let S := (nonleaves G).filter (fun v => trianglesAt G v≤1)
  have sub : types G⊆((nonleaves G)\S).image (trianglesAt G)∪range 2 := by
    intro z zm
    obtain ⟨v,_,rfl⟩ := mem_image.mp zm
    by_cases low : trianglesAt G v≤1
    · exact mem_union_right _ (mem_range.mpr (by omega))
    · have vm : v∈nonleaves G := Classical.byContradiction (fun out => low (by rw [Prune.outside_zero G out]; decide))
      exact mem_union_left _ (mem_image.mpr ⟨v,mem_sdiff.mpr ⟨vm,fun h => low (mem_filter.mp h).2⟩,rfl⟩)
  have pool := card_sdiff_add_card_eq_card (filter_subset (fun v => trianglesAt G v≤1) (nonleaves G))
  change ((nonleaves G)\S).card+S.card=_ at pool
  have bound := (card_le_card sub).trans (card_union_le ..)
  have im := card_image_le (s:=(nonleaves G)\S) (f:=trianglesAt G)
  rw [card_range,equal] at bound
  change S.card≤2; omega

/-- Every finite simple graph with equally many nonleaves and triangle
counts, and exactly one degree-two vertex, satisfies the catalogue bound. -/
theorem equal_quota (equal : (types G).card=(nonleaves G).card)
    (one : (twos G).card=1) : gamma G≤bound G := by
  classical
  obtain ⟨e,only⟩ := card_eq_one.mp one
  let S := (nonleaves G).filter (fun v => trianglesAt G v≤1)
  have et : e∈twos G := only ▸ mem_singleton_self _
  have de := LowSample.two_degree G et
  have cap := Repair.triangles_le_choose G e
  rw [de,Nat.choose_self] at cap
  have em : e∈S := mem_filter.mpr ⟨(mem_sdiff.mp et).1,cap⟩
  have size : (S.erase e).card≤1 := by
    rw [card_erase_of_mem em]; have := low_scores G equal; change S.card≤2 at this; omega
  by_cases non : (S.erase e).Nonempty
  · obtain ⟨f,fm⟩ := non
    apply one_low_high G (f:=f) only equal.le
    intro v vh vf
    by_contra! low
    have vne : v≠e := fun eq => (mem_sdiff.mp et).2 (eq ▸ vh)
    have vn : v∈nonleaves G := mem_filter.mpr ⟨mem_univ _,by have := (mem_filter.mp vh).2; omega⟩
    exact vf (card_le_one.mp size _ (mem_erase.mpr ⟨vne,mem_filter.mpr ⟨vn,by omega⟩⟩) _ fm)
  · apply one_low_high G (f:=e) only equal.le
    intro v vh ve
    by_contra! low
    have vn : v∈nonleaves G := mem_filter.mpr ⟨mem_univ _,by have := (mem_filter.mp vh).2; omega⟩
    exact non ⟨v,mem_erase.mpr ⟨ve,mem_filter.mpr ⟨vn,by omega⟩⟩⟩
/-- At most one vertex of degree two suffices whenever there are
at least as many nonleaves as distinct triangle counts. -/
theorem at_most_one (q : (types G).card≤(nonleaves G).card) (few : (twos G).card≤1) :
    gamma G≤bound G := by
  have sub : high G⊆nonleaves G := fun v vm => mem_filter.mpr ⟨mem_univ _,by have := (mem_filter.mp vm).2; omega⟩
  have n : (twos G).card+(high G).card=(nonleaves G).card := card_sdiff_add_card_eq_card sub
  by_cases enough : (types G).card≤(high G).card
  · exact exact_of_high G (by omega)
  exact equal_quota G (by omega) (by omega)

/-- At even diversity the single-ear conclusion holds at every nonleaf quota. -/
theorem even_at_most_one (even : (types G).card%2=0) (few : (twos G).card≤1) : gamma G≤bound G := by
  by_cases enough : (types G).card≤(nonleaves G).card
  · exact at_most_one G enough few
  · exact EvenQuota.exact_of_fewer_nonleaves G even (Nat.lt_of_not_ge enough)

end Graffiti384b.QuotaEar
#print axioms Graffiti384b.QuotaEar.one_low_high
#print axioms Graffiti384b.QuotaEar.low_scores
#print axioms Graffiti384b.QuotaEar.equal_quota
#print axioms Graffiti384b.QuotaEar.at_most_one
#print axioms Graffiti384b.QuotaEar.even_at_most_one
