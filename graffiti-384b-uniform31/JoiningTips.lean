import FlexibleTip
namespace Graffiti384b.TenPins
open Finset SimpleGraph EarFrame33 EightPins
open private Repair.nbr_mono Repair.full_nbr Repair.linkEdges Repair.edge_info from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A single prescribed vertex of positive internal degree can use an
outside neighbor. All the other vertices of C have internal degree at least three. -/
theorem internal_tip (C : Finset V) {z : V} (zc : z∈C) (pos : 0<nbr G z C)
    (deg : ∀ v∈C,v≠z → 3≤nbr G v C) : ∃ R⊆C,∃ L⊆C,Tip G R L z := by
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
  have dis : Disjoint L R := disjoint_left.mpr (fun v vl vr => mem_compl.mp (mem_inter.mp vr).1 (mem_inter.mp vl).1)
  have left (v : V) (vm : v∈L) : nbr G v C≤2*nbr G v R := by
    obtain ⟨va,vc⟩ := mem_inter.mp vm
    have cmp := l v va (not_mem_empty v); have full := Repair.full_nbr H v A
    rw [degreeIn v vc] at full; change _≤2*nbr G v (Aᶜ∩C); rw [←eq v vc]; omega
  have right (v : V) (vm : v∈R) : nbr G v C≤2*nbr G v L := by
    obtain ⟨va,vc⟩ := mem_inter.mp vm
    have cmp := r v va (not_mem_empty v); have full := Repair.full_nbr H v A
    rw [degreeIn v vc] at full; change _≤2*nbr G v (A∩C); rw [←eq v vc]; omega
  have one {S : Finset V} (h : 0<nbr G z S) : ∃v∈S,G.Adj z v := by
    obtain ⟨v,vm⟩ := card_pos.mp h; exact ⟨v,(mem_filter.mp vm).1,(mem_filter.mp vm).2⟩
  have make (U W : Finset V) (uc : U⊆C) (wc : W⊆C) (dw : Disjoint U W) (zu : z∈U)
      (lu : ∀v∈U,nbr G v C≤2*nbr G v W) (rw' : ∀v∈W,nbr G v C≤2*nbr G v U) : Tip G U W z := by
    refine ⟨dw,zu,one (by have := lu z zu; omega),?_,?_⟩
    · intro v vm vz; have := deg v (uc vm) vz; have := lu v vm; omega
    · intro v vm; have ne : v≠z := fun h => disjoint_left.mp dw zu (h ▸ vm)
      have := deg v (wc vm) ne; have := rw' v vm; omega
  by_cases za : z∈A
  · exact ⟨L,inter_subset_right,R,inter_subset_right,make L R inter_subset_right inter_subset_right dis (mem_inter.mpr ⟨za,zc⟩) left right⟩
  · exact ⟨R,inter_subset_right,L,inter_subset_right,make R L inter_subset_right inter_subset_right dis.symm (mem_inter.mpr ⟨mem_compl.mpr za,zc⟩) right left⟩

/-- Join two disjoint regions with one pending vertex in each. Their pending
vertices become each other's second opposite neighbor. -/
theorem join_tips {P Q C : Finset V} {w z : V} (tip : Tip G P Q w) (zc : z∈C) (wz : G.Adj w z)
    (away : Disjoint C (P∪Q)) (pos : 0<nbr G z C) (deg : ∀v∈C,v≠z → 3≤nbr G v C) :
    ∃ U W,P⊆U ∧ Q⊆W ∧ Frame G U W := by
  obtain ⟨R,rc,L,lc,other⟩ := internal_tip G C zc pos deg
  have crossL : Disjoint L Q := (away.mono_left lc).mono_right subset_union_right
  have crossR : Disjoint P R := ((away.mono_left rc).mono_right (show P⊆P∪Q from subset_union_left)).symm
  refine ⟨P∪L,Q∪R,subset_union_left,subset_union_left,?_,?_,?_⟩
  · simp only [disjoint_union_left,disjoint_union_right]; exact ⟨⟨tip.dis,crossL⟩,crossR,other.dis.symm⟩
  · intro a am; rcases mem_union.mp am with ap|al
    · by_cases aw : a=w
      · subst a; obtain ⟨y,ym,wy⟩ := tip.near
        exact PinnedColor34.two G (fun (h:z=y) => disjoint_left.mp away zc (mem_union_right _ (h ▸ ym : z∈Q))) wz wy (mem_union_right _ other.onSide) (mem_union_left _ ym)
      · exact (tip.left a ap aw).trans (Repair.nbr_mono G _ subset_union_left)
    · exact (other.right a al).trans (Repair.nbr_mono G _ subset_union_right)
  · intro a am; rcases mem_union.mp am with aq|ar
    · exact (tip.right a aq).trans (Repair.nbr_mono G _ subset_union_left)
    · by_cases az : a=z
      · subst a; obtain ⟨y,ym,zy⟩ := other.near
        exact PinnedColor34.two G (fun (h:w=y) => disjoint_left.mp away (h ▸ lc ym) (mem_union_left _ tip.onSide)) wz.symm zy (mem_union_left _ tip.onSide) (mem_union_right _ ym)
      · exact (other.left a ar az).trans (Repair.nbr_mono G _ subset_union_right)

/-- Only common neighbors of the exceptional root w and v can create
additional triangles. The estimate records the zero loss when w and v are nonadjacent. -/
theorem local_link {C : Finset V} {v w : V}
    (small : G.Adj w v → nbr G v (C.filter (G.Adj w))≤1)
    (cover : ∀ a b,G.Adj v a → G.Adj v b → G.Adj a b → a∈insert w C) :
    trianglesAt G v≤(nbr G v C).choose 2+(if G.Adj w v then 1 else 0) := by
  classical
  let U := C.filter (G.Adj v)
  let W := C.filter (G.Adj w)
  let B := if G.Adj w v then (W.filter (G.Adj v)).image (fun z => ({w,z}:Finset V)) else ∅
  have insertCase {a : V} (va : G.Adj v a) (vw : G.Adj v w) (wa : G.Adj w a) :
      ({w,a}:Finset V)∈B := by
    have ac := (mem_insert.mp (cover a w va vw wa.symm)).resolve_left wa.ne.symm
    simp only [B,if_pos vw.symm]
    exact mem_image.mpr ⟨a,mem_filter.mpr ⟨mem_filter.mpr ⟨ac,wa⟩,va⟩,rfl⟩
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
  have lim : B.card≤(if G.Adj w v then 1 else 0) := by
    by_cases edge : G.Adj w v
    · simp only [B,if_pos edge]
      exact (card_image_le (f:=fun z => ({w,z}:Finset V)) (s:=W.filter (G.Adj v))).trans (small edge)
    · simp [B,edge]
  have z := (card_le_card sub).trans (card_union_le ..)
  rw [card_powersetCard] at z; change trianglesAt G v≤(nbr G v C).choose 2+B.card at z; omega

end Graffiti384b.TenPins
#print axioms Graffiti384b.TenPins.internal_tip
#print axioms Graffiti384b.TenPins.join_tips
#print axioms Graffiti384b.TenPins.local_link
