import PreserveEar
import QuotaCap

namespace Graffiti384b.Remaining29
open Finset SimpleGraph LowSample QuotaEar
open private Prune.outside_zero from Prune384b
open private LowSample.two_degree from LowSample384b
open private TrianglePrune.triangle_iff from TrianglePrune384b
open private OneEar.deg2 from OneEarFinish384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem account : (twos G).card+(high G).card=(nonleaves G).card :=
  card_sdiff_add_card_eq_card (fun v (vh : v∈high G) => mem_filter.mpr
    ⟨mem_univ _,by have := (mem_filter.mp vh).2; omega⟩)

/-- The fifteenth omission at every order, including both intermediate
nonleaf quotas, when at least twenty-eight vertices have degree at least three. -/
theorem exact_above_minimum (t : (types G).card=29) (q : 29≤(nonleaves G).card)
    (h : 28≤(high G).card) : gamma G≤Fintype.card V-15 := by
  suffices sol : gamma G≤bound G by simpa only [bound,t] using sol
  by_cases big : 29≤(high G).card
  · exact exact_of_high G (by omega)
  have hi : (high G).card=28 := by omega
  by_cases many : 30≤(nonleaves G).card
  · exact PivotQuota.exact_high28 G t many hi
  · have card := account G
    exact equal_quota G (by omega) (by omega)

/-- All remaining failures above the minimum quota have 27 high vertices
of distinct scores at least two and either two or three degree-two vertices. -/
theorem residual (t : (types G).card=29) (q : 29≤(nonleaves G).card) (fail : bound G<gamma G) :
    (high G).card=27 ∧ ((nonleaves G).card=29 ∧ (twos G).card=2 ∨
      (nonleaves G).card=30 ∧ (twos G).card=3) ∧
      Set.InjOn (trianglesAt G) (high G) ∧ (∀v∈high G,2≤trianglesAt G v) ∧
      0∈types G ∧ 1∈types G := by
  have old := Quota29.residual G t fail
  have small : (high G).card<28 := Nat.lt_of_not_ge (fun ge => (not_lt_of_ge
    (show gamma G≤bound G by simpa only [bound,t] using exact_above_minimum G t q ge)) fail)
  have hs : (high G).card=27 := by omega
  have count := account G
  exact ⟨hs,by omega,Repair.maximal_diversity G (by omega)⟩

/-- Delete every edge outside triangles except those incident with a
triangle-free ear. The spanning graph preserves the three vertex classes,
all triangle counts, and a failure. At q = 29 at most one such ear is needed;
at q = 30 at most two are needed. -/
theorem sparse_stars (t : (types G).card=29) (q : 29≤(nonleaves G).card) (fail : bound G<gamma G) :
    let S := (twos G).filter (fun v => trianglesAt G v=0)
    let J := triangleStars G S
    S.card+28≤(nonleaves G).card ∧ high J=high G ∧ nonleaves J=nonleaves G ∧
      (∀v,trianglesAt J v=trianglesAt G v) ∧ bound J<gamma J ∧
      (∀u v,u∉S → v∉S → J.Adj u v → ∃w,J.Adj u w ∧ J.Adj v w) := by
  classical
  let S := (twos G).filter (fun v => trianglesAt G v=0)
  let J := triangleStars G S
  change S.card+28≤(nonleaves G).card ∧ high J=high G ∧ nonleaves J=nonleaves G ∧ _
  obtain ⟨hs,_,_,rich,_,one⟩ := residual G t q fail
  obtain ⟨e,_,oe⟩ := mem_image.mp one
  have eh : e∉high G := fun h => by have := rich e h; omega
  have en : e∈nonleaves G := Classical.byContradiction (fun out => by have := Prune.outside_zero G out; omega)
  have et : e∈twos G := mem_sdiff.mpr ⟨en,eh⟩
  have small := card_le_card (show S⊆(twos G).erase e from fun v vm => mem_erase.mpr
    ⟨fun eq => by have z := (mem_filter.mp vm).2; rw [eq,oe] at z; contradiction,(mem_filter.mp vm).1⟩)
  rw [card_erase_of_mem et] at small
  have count := account G
  have size := card_pos.mpr ⟨e,et⟩
  have mono (v : V) : J.degree v≤G.degree v := degree_le G S v
  have highEq : high J=high G := by
    ext v; exact ⟨fun h => mem_filter.mpr ⟨mem_univ _,(mem_filter.mp h).2.trans (mono v)⟩,
      fun h => high_of_score G (rich v h)⟩
  have non : nonleaves J=nonleaves G := by
    ext v; constructor
    · exact fun h => mem_filter.mpr ⟨mem_univ _,(mem_filter.mp h).2.trans (mono v)⟩
    · intro h
      by_cases vh : v∈high G
      · have ge := (mem_filter.mp (highEq ▸ vh : v∈high J)).2
        exact mem_filter.mpr ⟨mem_univ _,by omega⟩
      have vt : v∈twos G := mem_sdiff.mpr ⟨h,vh⟩
      by_cases zero : trianglesAt G v=0
      · have same := star_degree G (show v∈S from mem_filter.mpr ⟨vt,zero⟩)
        exact mem_filter.mpr ⟨mem_univ _,by change 2≤(triangleStars G S).degree v; rw [same]; exact (mem_filter.mp h).2⟩
      · have p : 0<trianglesAt J v := by rw [show trianglesAt J v=trianglesAt G v from scores G S v]; omega
        obtain ⟨a,b,va,vb,ab⟩ := (TrianglePrune.triangle_iff J v).mp p
        exact mem_filter.mpr ⟨mem_univ _,OneEar.deg2 J ab.ne va vb⟩
  exact ⟨by omega,highEq,non,scores G S,Nat.lt_of_not_ge (fun sol => (not_lt_of_ge (transfers G S sol)) fail),
    fun _ _ up vp edge => triangle_away G up vp edge⟩

end Graffiti384b.Remaining29
#print axioms Graffiti384b.Remaining29.exact_above_minimum
#print axioms Graffiti384b.Remaining29.residual
#print axioms Graffiti384b.Remaining29.sparse_stars
