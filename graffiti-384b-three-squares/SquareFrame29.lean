import CoverDense31
namespace Graffiti384b.Squares29
open Finset SimpleGraph EarFrame33
open private Repair.nbr_mono Repair.full_nbr Repair.omit_set from Repair384b
open private CubicShore.square_frame from CubicDiamondCut33
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The vertex x lies opposite the degree-two vertex e on a four-cycle. -/
def Opposite (e x : V) : Prop :=
  G.degree e=2 ∧ e≠x ∧ G.neighborFinset e⊆G.neighborFinset x

def Sparse : Prop := ∀ A B,Frame G A B → ∀ e∈A∪B,∀ f∈A∪B,G.degree e=2 → G.degree f=2 → e=f

theorem sparse (bad : bound G<gamma G) : Sparse G := by
  classical
  intro P Q fr e ep f fp de df
  apply Classical.byContradiction; intro ne
  let S := insert e (insert f (high G))
  have eh : e∉high G := fun z => by have a : 3≤G.degree e := (mem_filter.mp z).2; omega
  have fh : f∉high G := fun z => by have a : 3≤G.degree f := (mem_filter.mp z).2; omega
  have sz : S.card=(high G).card+2 := by simp [S,ne,eh,fh,Nat.add_assoc]
  have types_le := type_bound G
  obtain ⟨A,pa,qb,la,rb⟩ := PinnedColor34.cut G P Q fr.1
  have free (v : V) (vm : v∈S) (vp : v∉P) (vq : v∉Q) : 3≤G.degree v := by
    have out : v∉P∪Q := fun z => (mem_union.mp z).elim vp vq
    rcases mem_insert.mp vm with rfl|vm
    · exact (out ep).elim
    rcases mem_insert.mp vm with rfl|vm
    · exact (out fp).elim
    exact (mem_filter.mp vm).2
  have left (v : V) (vm : v∈S) (va : v∈A) : 2≤nbr G v Aᶜ := by
    by_cases vp : v∈P
    · exact (fr.2.1 v vp).trans (Repair.nbr_mono G _ qb)
    have := free v vm vp (fun z => mem_compl.mp (qb z) va)
    have := la v va vp
    have := Repair.full_nbr G v A
    omega
  have right (v : V) (vm : v∈S) (va : v∉A) : 2≤nbr G v A := by
    by_cases vq : v∈Q
    · exact (fr.2.2 v vq).trans (Repair.nbr_mono G _ pa)
    have := free v vm (fun z => va (pa z)) vq
    have := rb v (mem_compl.mpr va) vq
    have := Repair.full_nbr G v A
    omega
  have l := Repair.omit_set G (S∩A) (fun v vm => (left v (mem_inter.mp vm).1 (mem_inter.mp vm).2).trans
    (Repair.nbr_mono G _ (fun _ z => mem_compl.mpr (fun m => mem_compl.mp z (mem_inter.mp m).2))))
  have r := Repair.omit_set G (S\A) (fun v vm => (right v (mem_sdiff.mp vm).1 (mem_sdiff.mp vm).2).trans
    (Repair.nbr_mono G _ (fun _ z => mem_compl.mpr (fun m => (mem_sdiff.mp m).2 z))))
  have := card_sdiff_add_card_inter S A
  unfold bound at bad
  omega

theorem frame {e x : V} (sq : Opposite G e x) : Frame G {e,x} (G.neighborFinset e) := by
  obtain ⟨a,b,ab,eq⟩ := card_eq_two.mp ((card_neighborFinset_eq_degree ..).trans sq.1)
  have am : a∈G.neighborFinset e := eq ▸ mem_insert_self _ _
  have bm : b∈G.neighborFinset e := eq ▸ mem_insert_of_mem (mem_singleton_self _)
  rw [eq]
  exact CubicShore.square_frame G ((G.mem_neighborFinset ..).mp am) ((G.mem_neighborFinset ..).mp bm)
    ((G.mem_neighborFinset ..).mp (sq.2.2 am)).symm ((G.mem_neighborFinset ..).mp (sq.2.2 bm)).symm sq.2.1 ab

omit [Fintype V] in
private theorem merge {A B C D : Finset V} (f : Frame G A B) (g : Frame G C D)
    (ad : Disjoint A D) (bc : Disjoint B C) : Frame G (A∪C) (B∪D) := by
  refine ⟨by simp only [disjoint_union_left,disjoint_union_right]; exact ⟨⟨f.1,bc.symm⟩,ad,g.1⟩,?_,?_⟩
  · intro v m
    exact (mem_union.mp m).elim (fun z => (f.2.1 _ z).trans (Repair.nbr_mono G _ subset_union_left))
      (fun z => (g.2.1 _ z).trans (Repair.nbr_mono G _ subset_union_right))
  · intro v m
    exact (mem_union.mp m).elim (fun z => (f.2.2 _ z).trans (Repair.nbr_mono G _ subset_union_left))
      (fun z => (g.2.2 _ z).trans (Repair.nbr_mono G _ subset_union_right))

theorem outside (sp : Sparse G) {e f x : V} (ne : e≠f) (sq : Opposite G e x) (df : G.degree f=2) :
    f∉({e,x}:Finset V)∪G.neighborFinset e := fun fm =>
  ne (sp _ _ (frame G sq) _ (mem_union_left _ (mem_insert_self ..)) _ fm sq.1 df)

/-- Two squares force a shared anchor and a cross-contact between an opposite
vertex and the other pair of anchors. The latter holds for every choice. -/
theorem contact (sp : Sparse G) {e f x y : V} (ne : e≠f) (s : Opposite G e x) (v : Opposite G f y) :
    (G.neighborFinset e∩G.neighborFinset f).Nonempty ∧
      (x∈G.neighborFinset f ∨ y∈G.neighborFinset e) := by
  classical
  let A := G.neighborFinset e
  let B := G.neighborFinset f
  let P : Finset V := {e,x}
  let Q : Finset V := {f,y}
  have se : Frame G P A := frame G s
  have sf : Frame G Q B := frame G v
  have fm : f∉P∪A := outside G sp ne s v.1
  have em : e∉Q∪B := outside G sp ne.symm v s.1
  have ep : e∈P := mem_insert_self ..
  have fq : f∈Q := mem_insert_self ..
  have cross : x∈B ∨ y∈A := by
    apply Classical.byContradiction; intro no; push_neg at no
    have pb : Disjoint P B := disjoint_left.mpr (by
      intro z zm bm; rcases mem_insert.mp zm with rfl|u
      · exact em (mem_union_right _ bm)
      · exact no.1 (mem_singleton.mp u ▸ bm))
    have qa : Disjoint Q A := disjoint_left.mpr (by
      intro z zm am; rcases mem_insert.mp zm with rfl|u
      · exact fm (mem_union_right _ am)
      · exact no.2 (mem_singleton.mp u ▸ am))
    exact ne (sp _ _ (merge G se sf pb qa.symm) e (mem_union_left _ (mem_union_left _ ep))
      f (mem_union_left _ (mem_union_right _ fq)) s.1 v.1)
  refine ⟨?_,cross⟩
  apply Classical.byContradiction; intro no
  have ab : Disjoint A B := disjoint_left.mpr (fun z za zb => no ⟨z,mem_inter.mpr ⟨za,zb⟩⟩)
  have xy : x≠y := by
    intro eq; subst y
    have xm : x∈P := mem_insert_of_mem (mem_singleton_self _)
    have xq : x∈Q := mem_insert_of_mem (mem_singleton_self _)
    exact cross.elim (disjoint_left.mp sf.1 xq) (disjoint_left.mp se.1 xm)
  have pq : Disjoint P Q := disjoint_left.mpr (by
    intro z zp zq; rcases mem_insert.mp zp with rfl|zx
    · exact em (mem_union_left _ zq)
    · rcases mem_insert.mp zq with rfl|zy
      · exact fm (mem_union_left _ zp)
      · exact xy ((mem_singleton.mp zx).symm.trans (mem_singleton.mp zy)))
  have swap : Frame G B Q := ⟨sf.1.symm,sf.2.2,sf.2.1⟩
  exact ne (sp _ _ (merge G se swap pq ab) e (mem_union_left _ (mem_union_left _ ep))
    f (mem_union_right _ (mem_union_right _ fq)) s.1 v.1)

end Graffiti384b.Squares29
#print axioms Graffiti384b.Squares29.sparse
#print axioms Graffiti384b.Squares29.contact
