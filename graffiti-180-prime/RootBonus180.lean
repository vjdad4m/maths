import TrueChart180

set_option warningAsError true
namespace Minimal180.Substitution
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
open Classical
variable {V B : Type*} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]
variable {H : SimpleGraph V} {G : SimpleGraph B} {f : V→B} {s : B→V} {r : V}

/-- A bipartite witness receives one extra unit if the chosen root has
no neighbor in that witness. -/
noncomputable def bonus (G : SimpleGraph B) (a : B) (Z : Finset B) : ℕ :=
  if ∀ i∈Z,¬G.Adj a i then 1 else 0

/-- The additional test on the prime graph itself, with r in the
independent marking and with odd distance parity. -/
def OddRootTest (G : SimpleGraph B) (a : B) (I : Finset B) : Prop :=
  let Q := parity G a true
  ∃ Z,TwoColor G Z ∧ insert a (I∩Q)⊆Z ∧
    1+I.card+Q.card≤weightedLeaves G (eligible I Q a)+Z.card+bonus G a Z

omit [Fintype V] in
theorem TrueChart.colorUp (h : TrueChart H G f s r) {Z : Finset B} (col : TwoColor G Z) :
    ∃ Y,TwoColor H Y ∧ Z.image s⊆Y ∧ Z.card+bonus G (f r) Z≤Y.card := by
  classical
  obtain ⟨c,good⟩ := (color_function ..).mp col
  have base : TwoColor H (Z.image s) := by
    apply (color_function ..).mpr
    refine ⟨fun v => c (f v),?_⟩
    rintro _ xm _ ym edge
    obtain ⟨i,im,rfl⟩ := mem_image.mp xm
    obtain ⟨j,jm,rfl⟩ := mem_image.mp ym
    simpa only [h.sec _] using good i im j jm (h.oldAdj.mp edge)
  by_cases iso : ∀ i∈Z,¬G.Adj (f r) i
  · let d (v : V) := if v=r then !(c (f r)) else c (f v)
    have extra : TwoColor H (insert r (Z.image s)) := by
      apply (color_function ..).mpr
      refine ⟨d,fun x xm y ym edge => ?_⟩
      rcases mem_insert.mp xm with xr|zx <;> rcases mem_insert.mp ym with yr|zy
      · exact (edge.ne (xr.trans yr.symm)).elim
      · subst x; obtain ⟨j,jm,rfl⟩ := mem_image.mp zy
        have eq := (h.newAdj.mp edge).resolve_right (iso j jm)
        subst j; simp [d,h.out,h.sec _]
      · subst y; obtain ⟨i,im,rfl⟩ := mem_image.mp zx
        have eq := (h.newAdj.mp edge.symm).resolve_right (iso i im)
        subst i; simp [d,h.out,h.sec _]
      · obtain ⟨i,im,rfl⟩ := mem_image.mp zx
        obtain ⟨j,jm,rfl⟩ := mem_image.mp zy
        simpa [d,h.out i,h.out j,h.sec i,h.sec j] using good _ im _ jm (h.oldAdj.mp edge)
    have miss : r∉Z.image s := by rintro m; obtain ⟨i,_,eq⟩ := mem_image.mp m; exact h.out i eq
    exact ⟨_,extra,subset_insert ..,by rw [bonus,if_pos iso,card_insert_of_not_mem miss,card_image_of_injective _ h.sec.injective]⟩
  · exact ⟨_,base,Subset.rfl,by simp [bonus,iso,card_image_of_injective _ h.sec.injective]⟩

omit [Fintype V] in
theorem TrueChart.colorCap (h : TrueChart H G f s r) {Y : Finset V} (col : TwoColor H Y)
    (mate : s (f r)∈Y) : Y.card≤(pull s Y).card+bonus G (f r) (pull s Y) := by
  classical
  let Z := pull s Y
  have count := section_count s h.sec.injective Y
  by_cases rm : r∈Y
  · have iso (i : B) (im : i∈Z) (edge : G.Adj (f r) i) : False := by
      obtain ⟨c,ok⟩ := (color_function ..).mp col
      have one := ok _ rm _ mate h.edge
      have two := ok _ rm _ (mem_pull.mp im) (h.newAdj.mpr (Or.inr edge))
      have three := ok _ mate _ (mem_pull.mp im) (h.oldAdj.mpr edge)
      cases a : c r <;> cases b : c (s (f r)) <;> cases d : c (s i) <;> simp [a,b,d] at *
    have sub : Y\univ.image s⊆{r} := by
      intro x xm
      rcases h.all x with eq|⟨i,ix⟩
      · exact mem_singleton.mpr eq
      · exact ((mem_sdiff.mp xm).2 (ix ▸ mem_image_of_mem _ (mem_univ i))).elim
    have cap := card_le_card sub; rw [card_singleton] at cap
    change Y.card=Z.card+_ at count
    change Y.card≤Z.card+bonus G (f r) Z
    rw [bonus,if_pos iso]; omega
  · have none : Y\univ.image s=∅ := by
      apply eq_empty_iff_forall_not_mem.mpr
      intro x xm
      rcases h.all x with eq|⟨i,ix⟩
      · exact rm (eq ▸ (mem_sdiff.mp xm).1)
      · exact (mem_sdiff.mp xm).2 (ix ▸ mem_image_of_mem _ (mem_univ i))
    rw [none,card_empty,add_zero] at count
    omega

theorem TrueChart.odd_iff (h : TrueChart H G f s r) (gc : G.Connected) (hn : 2<Fintype.card B)
    (nh : ∀ i,¬Universal G i) (I : Finset B) (ia : f r∈I) :
    let A := I.image s
    let P := parity H r true
    Pinned H r true A (A∩P) ↔ OddRootTest G (f r) I := by
  classical
  intro A P
  let Q := parity G (f r) true
  let U := eligible I Q (f r)
  let K := insert (f r) (I∩Q)
  obtain ⟨ac,pc,ue,dc⟩ := h.marks gc (by omega) I ia
  have off : f r∉U := by simp [U,Q,eligible_iff,mem_parity,dist_self]
  have up := h.bags.costExact gc hn nh ((insert (f r) U).image s)
  rw [h.full U off,card_image_of_injective _ h.sec.injective,card_insert_of_not_mem off] at up
  have score : weightedLeaves H (eligible A P r)=weightedLeaves G U+1 := by
    rw [ue]
    change weightedLeaves H ((insert (f r) U).image s)=weightedLeaves G U+1
    omega
  change A.card=I.card at ac
  change P.card=Q.card+1 at pc
  change A∩P=K.image s at dc
  constructor
  · rintro ⟨Y,col,keep,ok⟩
    have inc : K⊆pull s Y := fun i im => mem_pull.mpr (keep (dc ▸ mem_image_of_mem _ im))
    have cap := h.colorCap col (mem_pull.mp (inc (mem_insert_self ..)))
    have old := restrict_color G H s h.sec.injective (fun e => h.oldAdj.mpr e) col
    refine ⟨_,old,inc,?_⟩
    change 1+A.card+P.card≤weightedLeaves H (eligible A P r)+Y.card at ok
    change 1+I.card+Q.card≤weightedLeaves G U+(pull s Y).card+bonus G (f r) (pull s Y)
    rw [ac,pc,score] at ok; omega
  · rintro ⟨Z,col,keep,ok⟩
    obtain ⟨Y,bi,inc,size⟩ := h.colorUp col
    refine ⟨Y,bi,?_,?_⟩
    · change A∩P⊆Y
      rw [dc]; exact (image_subset_image keep).trans inc
    · change 1+A.card+P.card≤weightedLeaves H (eligible A P r)+Y.card
      change 1+I.card+Q.card≤weightedLeaves G U+Z.card+bonus G (f r) Z at ok
      rw [ac,pc,score]; omega

#print axioms TrueChart.colorUp
#print axioms TrueChart.colorCap
#print axioms TrueChart.odd_iff
end Minimal180.Substitution
