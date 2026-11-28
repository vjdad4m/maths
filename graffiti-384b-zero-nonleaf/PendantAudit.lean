import TriangleBlocks

namespace Graffiti384b.OddStars.PendantAudit
open Finset SimpleGraph PositivePalette
open private TrianglePrune.triangle_iff from TrianglePrune384b
open private OddStars.true_ear from TriangleBlocks
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- In the upper of the two skeletal high-count branches each positive
vertex is high in the skeleton, positive scores are pairwise distinct, and
every zero has original degree at most one. -/
theorem upper_branch (bad : bound G<gamma G) (size : (high (patch G ∅)).card+1=(types G).card) :
    (∀v,0<trianglesAt G v → v∈high (patch G ∅)) ∧
    Set.InjOn (trianglesAt G) {v | 0<trianglesAt G v} ∧
    (∀z,trianglesAt G z=0 → G.degree z≤1) := by
  classical
  let J := patch G ∅
  have lift (v : V) : J.degree v ≤ G.degree v := by
    rw [←card_neighborFinset_eq_degree,←card_neighborFinset_eq_degree]
    exact card_le_card (fun _ m => (G.mem_neighborFinset ..).mpr ((J.mem_neighborFinset ..).mp m).1)
  have pos {v : V} (s : 0<trianglesAt G v) : v∈high J := by
    by_contra low
    obtain ⟨a,b,va,vb,ab⟩ := (TrianglePrune.triangle_iff J v).mp (by rwa [patch_scores G ∅])
    have ge := Prerequisites.deg2 J ab.ne va vb
    have smaller : J.degree v≤2 := by
      apply Nat.le_of_not_gt; intro large; exact low (mem_filter.mpr ⟨mem_univ _,large⟩)
    have cut := cover_two G (c:=v) (e:=v) (empty_subset _) (le_antisymm smaller ge)
    have bound' := count_covered G (covered_mono G (J:=J) (fun _ _ h => h.1) cut)
    rw [card_insert_of_not_mem low] at bound'
    have cap : (types G).card≤Fintype.card V := card_image_le.trans_eq card_univ
    change (high J).card+1=(types G).card at size
    unfold bound at bad; omega
  refine ⟨fun _ h => pos h,?_,?_⟩
  · intro x xp y _ eq
    change 0<trianglesAt G x at xp
    by_cases one : trianglesAt G x=1
    · exact rich_one_unique G bad ((mem_filter.mp (pos xp)).2.trans (lift x)) one (eq ▸ one)
    · exact distinct_rich G bad (by omega) eq
  · intro z zero
    have lo := zero_degree G bad zero
    apply Nat.le_of_not_gt
    intro high
    obtain ⟨has,ones⟩ := zero_two_forces_ears G bad zero (by omega : G.degree z=2)
    obtain ⟨f,_,sf⟩ := mem_image.mp has
    have h := (mem_filter.mp (pos (v:=f) (by omega))).2.trans (lift f)
    have := ones f sf; omega

omit [Fintype V] [DecidableEq V] in
private theorem confined {J : SimpleGraph V} {R : Finset V}
    (step : ∀{a b},J.Adj a b → a∈R → b∈R) {a b : V} (h : J.Reachable a b) (m : a∈R) : b∈R := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact m
  | cons e _ ih => exact ih (step e m)

/-- Two adjacent degree-two triangular ears in an original failure exhaust
the entire population of count-one vertices. -/
theorem pendant_pair_exhausts (bad : bound G<gamma G) {x y : V} (xy : G.Adj x y)
    (dx : G.degree x=2) (dy : G.degree y=2) (sx : trianglesAt G x=1) :
    ∀v,trianglesAt G v=1 → v=x ∨ v=y := by
  classical
  obtain ⟨a,b,nb,xa,xb,ab⟩ := Prerequisites.ear_pair G dx (by omega : 0<trianglesAt G x)
  have m := (G.mem_neighborFinset ..).mpr xy
  rw [nb,mem_insert,mem_singleton] at m
  obtain ⟨c,xc,yc,nx⟩ : ∃c,G.Adj x c ∧ G.Adj y c ∧ G.neighborFinset x={y,c} := by
    rcases m with rfl|rfl
    · exact ⟨_,xb,ab,nb⟩
    · exact ⟨_,xa,ab.symm,by simpa [pair_comm] using nb⟩
  have ny : G.neighborFinset y={x,c} := (eq_of_subset_of_card_le
    (insert_subset ((G.mem_neighborFinset ..).mpr xy.symm) (singleton_subset_iff.mpr ((G.mem_neighborFinset ..).mpr yc)))
    (by rw [card_pair xc.ne,card_neighborFinset_eq_degree,dy])).symm
  let J := patch G ∅
  have far (v : V) (sv : trianglesAt G v=1) (vc : v≠c) (vx : v≠x) (vy : v≠y) : False := by
    have path := one_ears_in_block G bad vx.symm sx sv xc.ne vc
    let R : Finset V := {x,y}
    have close {a b : V} (edge : (inside J ({c}ᶜ)).Adj a b) (am : a∈R) : b∈R := by
      have bc : b≠c := fun h => mem_compl.mp edge.2.2 (mem_singleton.mpr h)
      have bm := (G.mem_neighborFinset ..).mpr edge.1.1
      rcases mem_insert.mp am with rfl|m
      · rw [nx,mem_insert,mem_singleton] at bm
        exact mem_insert_of_mem (mem_singleton.mpr (bm.resolve_right bc))
      · obtain rfl := mem_singleton.mp m
        rw [ny,mem_insert,mem_singleton] at bm
        exact mem_insert.mpr (Or.inl (bm.resolve_right bc))
    have vm := confined (R:=R) (fun edge am => close edge am) path (mem_insert_self ..)
    exact (mem_insert.mp vm).elim vx (fun h => vy (mem_singleton.mp h))
  have anchor : trianglesAt G c≠1 := by
    intro sc
    have ge := Prerequisites.deg2 G xy.ne xc.symm yc.symm
    have dc : G.degree c=2 := by
      by_contra! ne
      exact xc.ne (rich_one_unique G bad (by omega) sc sx).symm
    have nc : G.neighborFinset c={x,y} := (eq_of_subset_of_card_le
      (insert_subset ((G.mem_neighborFinset ..).mpr xc.symm) (singleton_subset_iff.mpr ((G.mem_neighborFinset ..).mpr yc.symm)))
      (by rw [card_pair xy.ne,card_neighborFinset_eq_degree,dc])).symm
    let R : Finset V := {x,y,c}
    let W := insert x (high J)
    have nbrs {a : V} (am : a∈R) : G.neighborFinset a ⊆ R := by
      rcases mem_insert.mp am with rfl|m
      · rw [nx]; exact insert_subset (by simp [R]) (singleton_subset_iff.mpr (by simp [R]))
      rcases mem_insert.mp m with rfl|m
      · rw [ny]; exact insert_subset (by simp [R]) (singleton_subset_iff.mpr (by simp [R]))
      obtain rfl := mem_singleton.mp m
      rw [nc]; exact insert_subset (by simp [R]) (singleton_subset_iff.mpr (by simp [R]))
    have region' : region J R := fun {a b} edge =>
      ⟨fun m => nbrs m ((G.mem_neighborFinset ..).mpr edge.1),fun m => nbrs m ((G.mem_neighborFinset ..).mpr edge.1.symm)⟩
    have cut := cover_two G (c:=x) (e:=x) (empty_subset _) (OddStars.true_ear G sx dx ∅)
    have rep := represents_of_high G (S:=∅) (W:=W) (subset_insert ..) (fun _ => ⟨x,mem_insert_self ..,sx⟩)
    have same := (rigid G (J:=J) (fun _ _ h => h.1) rep cut bad).2.2
    have even := region_even G (J:=J) (fun _ _ h => h.1) same cut region'
    have low {a : V} (am : a∈R) : a∉high J := by
      have da : G.degree a=2 := by
        rcases mem_insert.mp am with rfl|m
        · exact dx
        rcases mem_insert.mp m with rfl|m
        · exact dy
        obtain rfl := mem_singleton.mp m; exact dc
      intro h
      have inc : J.neighborFinset a ⊆ G.neighborFinset a := fun _ m =>
        (G.mem_neighborFinset ..).mpr ((J.mem_neighborFinset ..).mp m).1
      have deg := card_le_card inc
      simp only [card_neighborFinset_eq_degree] at deg
      have := (mem_filter.mp h).2; omega
    have eq : W∩R={x} := by
      ext v
      constructor
      · intro m
        exact mem_singleton.mpr ((mem_insert.mp (mem_inter.mp m).1).resolve_right (low (mem_inter.mp m).2))
      · intro m; obtain rfl := mem_singleton.mp m; simp [W,R]
    rw [eq,card_singleton] at even
    omega
  intro v sv
  by_contra! h
  by_cases vc : v=c
  · exact anchor (vc ▸ sv)
  · exact far v sv vc h.1 h.2

end Graffiti384b.OddStars.PendantAudit
#print axioms Graffiti384b.OddStars.PendantAudit.upper_branch
#print axioms Graffiti384b.OddStars.PendantAudit.pendant_pair_exhausts