import FlexibleTip
namespace Graffiti384b.EightPins
open Finset SimpleGraph EarFrame33
open private Repair.nbr_mono Repair.full_nbr Repair.linkEdges Repair.edge_info from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A graph with minimum internal degree three in C admits a cut supporting
every vertex of C, and either side can be chosen for i. -/
theorem internal_frame (C : Finset V) {i : V} (ic : i∈C) (deg : ∀ v∈C,3≤nbr G v C) :
    ∃ L⊆C,∃ R⊆C,i∈R ∧ Frame G L R := by
  classical
  let H : SimpleGraph V := ⟨fun a b => a∈C ∧ b∈C ∧ G.Adj a b,
    fun _ _ h => ⟨h.2.1,h.1,h.2.2.symm⟩,fun a h => G.loopless a h.2.2⟩
  have eq (v : V) (vm : v∈C) (S : Finset V) : nbr H v S=nbr G v (S∩C) := by
    unfold nbr; congr 1; ext z
    change (z∈S.filter (fun x => v∈C ∧ x∈C ∧ G.Adj v x)) ↔ _
    simp only [mem_filter,mem_inter]; tauto
  have degreeIn (v : V) (vc : v∈C) : H.degree v=nbr G v C := by
    rw [←card_neighborFinset_eq_degree]
    unfold nbr; congr 1; ext z
    rw [mem_neighborFinset,mem_filter]
    change (v∈C ∧ z∈C ∧ G.Adj v z) ↔ z∈C ∧ G.Adj v z
    simp only [vc,true_and]
  obtain ⟨A,_,_,l,r⟩ := PinnedColor34.cut H ∅ ∅ (by simp)
  let L := A∩C; let R := Aᶜ∩C
  have frame : Frame G L R := by
    refine ⟨disjoint_left.mpr (fun v vl vr => mem_compl.mp (mem_inter.mp vr).1 (mem_inter.mp vl).1),?_,?_⟩
    · intro v vm; obtain ⟨va,vc⟩ := mem_inter.mp vm
      have cmp := l v va (not_mem_empty v)
      have full := Repair.full_nbr H v A
      rw [degreeIn v vc] at full; have lower := deg v vc; change 2≤nbr G v (Aᶜ∩C); rw [←eq v vc]; omega
    · intro v vm; obtain ⟨va,vc⟩ := mem_inter.mp vm
      have cmp := r v va (not_mem_empty v)
      have full := Repair.full_nbr H v A
      rw [degreeIn v vc] at full; have lower := deg v vc; change 2≤nbr G v (A∩C); rw [←eq v vc]; omega
  by_cases a : i∈A
  · exact ⟨R,inter_subset_right,L,inter_subset_right,mem_inter.mpr ⟨a,ic⟩,frame.1.symm,frame.2.2,frame.2.1⟩
  · exact ⟨L,inter_subset_right,R,inter_subset_right,mem_inter.mpr ⟨mem_compl.mpr a,ic⟩,frame⟩

/-- Add an independently supported region on the opposite side of the root. -/
theorem attach_region {P Q C : Finset V} {w i : V} (tip : Tip G P Q w) (ic : i∈C)
    (wi : G.Adj w i) (away : Disjoint C (P∪Q)) (deg : ∀ v∈C,3≤nbr G v C) :
    ∃ L R,P⊆L ∧ Q⊆R ∧ Frame G L R := by
  obtain ⟨L,lc,R,rc,ir,fr⟩ := internal_frame G C ic deg
  have crossL : Disjoint L Q := (away.mono_left lc).mono_right subset_union_right
  have crossR : Disjoint P R := ((away.mono_left rc).mono_right (show P⊆P∪Q from subset_union_left)).symm
  refine ⟨P∪L,Q∪R,subset_union_left,subset_union_left,?_,?_,?_⟩
  · simp only [disjoint_union_left,disjoint_union_right]; exact ⟨⟨tip.dis,crossL⟩,crossR,fr.1⟩
  · intro a am; rcases mem_union.mp am with ap|al
    · by_cases aw : a=w
      · subst a; obtain ⟨z,zm,wz⟩ := tip.near
        exact PinnedColor34.two G (fun (h:i=z) => disjoint_left.mp away ic (mem_union_right _ (h ▸ zm : i∈Q))) wi wz (mem_union_right _ ir) (mem_union_left _ zm)
      · exact (tip.left a ap aw).trans (Repair.nbr_mono G _ subset_union_left)
    · exact (fr.2.1 a al).trans (Repair.nbr_mono G _ subset_union_right)
  · intro a am; rcases mem_union.mp am with aq|ar
    · exact (tip.right a aq).trans (Repair.nbr_mono G _ subset_union_left)
    · exact (fr.2.2 a ar).trans (Repair.nbr_mono G _ subset_union_right)

/-- If every triangle neighbor lies in C or at w, at most one triangle
at v can use w when w has only two neighbors in C. -/
theorem local_triangles {C : Finset V} {v w : V} (vc : v∈C) (small : nbr G w C≤2)
    (cover : ∀ a b,G.Adj v a → G.Adj v b → G.Adj a b → a∈insert w C) :
    trianglesAt G v≤(nbr G v C).choose 2+1 := by
  classical
  let U := C.filter (G.Adj v)
  let W := C.filter (G.Adj w)
  let B := if G.Adj w v then (W.erase v).image (fun z => ({w,z}:Finset V)) else ∅
  have insertCase {a : V} (va : G.Adj v a) (vw : G.Adj v w) (wa : G.Adj w a) :
      ({w,a}:Finset V)∈B := by
    have ac := (mem_insert.mp (cover a w va vw wa.symm)).resolve_left wa.ne.symm
    simp only [B,if_pos vw.symm]
    exact mem_image.mpr ⟨a,mem_erase.mpr ⟨va.ne.symm,mem_filter.mpr ⟨ac,wa⟩⟩,rfl⟩
  have sub : Repair.linkEdges G v⊆U.powersetCard 2∪B := by
    intro s sm; obtain ⟨ns,sz,cl⟩ := Repair.edge_info G sm
    obtain ⟨a,b,ab,rfl⟩ := card_eq_two.mp sz
    have am : a∈({a,b}:Finset V) := mem_insert_self ..
    have bm : b∈({a,b}:Finset V) := mem_insert_of_mem (mem_singleton_self _)
    have va := (G.mem_neighborFinset ..).mp (ns am); have vb := (G.mem_neighborFinset ..).mp (ns bm)
    have edge := cl _ am _ bm ab
    by_cases aw : a=w
    · subst a; exact mem_union_right _ (insertCase vb va edge)
    by_cases bw : b=w
    · subst b; rw [pair_comm a w]; exact mem_union_right _ (insertCase va vb edge.symm)
    exact mem_union_left _ (mem_powersetCard.mpr ⟨insert_subset
      (mem_filter.mpr ⟨(mem_insert.mp (cover a b va vb edge)).resolve_left aw,va⟩)
      (singleton_subset_iff.mpr (mem_filter.mpr ⟨(mem_insert.mp (cover b a vb va edge.symm)).resolve_left bw,vb⟩)),sz⟩)
  have lim : B.card≤1 := by
    dsimp [B]; split
    · rename_i edge; have h := card_image_le (f:=fun z => ({w,z}:Finset V)) (s:=W.erase v)
      have vm : v∈W := mem_filter.mpr ⟨vc,edge⟩
      rw [card_erase_of_mem vm] at h; change W.card≤2 at small; omega
    · simp
  have z := (card_le_card sub).trans (card_union_le ..)
  rw [card_powersetCard] at z; change trianglesAt G v≤(nbr G v C).choose 2+B.card at z; omega

end Graffiti384b.EightPins
#print axioms Graffiti384b.EightPins.internal_frame
#print axioms Graffiti384b.EightPins.attach_region
#print axioms Graffiti384b.EightPins.local_triangles
