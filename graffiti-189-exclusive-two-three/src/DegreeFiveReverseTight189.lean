import DegreeFiveReverseSupport189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private Shore shore_off shore_disjoint from DegreeFiveActualCut189
open private secondShore anywhere_high_of_two from DegreeFiveDistanceTwoThreeClose189
open private Cmp portColor from DegreeFiveThreeForeignImpossible189
open private local_shell_comes_from_port from DegreeFiveNonmixedThreeFour189
open private tight_shell_high_contact local_d2_plus_foreign_le_five nonmixed_shell_nonports reverse_boundary
  from DegreeFiveReverseSupport189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

private theorem neighbor_outside_small {v : V} {S : Finset V} (vs : v∈S)
    (small : S.card ≤ 5) (high : 5 ≤ G.degree v) : ∃ w, G.Adj v w ∧ w∉S := by
  apply Classical.byContradiction
  intro n
  have sub : G.neighborFinset v ⊆ S.erase v := by
    intro w wm
    have vw := (mem_neighborFinset G _ _).mp wm
    exact mem_erase.mpr ⟨vw.ne.symm,Classical.byContradiction (fun h=>n ⟨w,vw,h⟩)⟩
  have k := card_le_card sub
  rw [card_erase_of_mem vs,card_neighborFinset_eq_degree] at k
  omega

private theorem shell_needs_cross
    (hc : G.Connected)
    {D : Cmp (G:=G) (a:=a) (b:=b)} {c d : V}
    (dir : (c=a ∧ d=b) ∨ (c=b ∧ d=a))
    (cover : Shore D ⊆ (portColor D c ∪ portColor D d) ∪
      (secondShore D c ∪ secondShore D d))
    (small : (portColor D c).card+(secondShore D c).card ≤ 5)
    {v : V} (vs : v∈secondShore D c) (out : v∉secondShore D d)
    (noa : ¬G.Adj a v) (nob : ¬G.Adj b v) (high : 5 ≤ G.degree v) :
    ∃ w∈secondShore D d,G.Adj v w := by
  classical
  have vh := (mem_inter.mp vs).1
  obtain ⟨w,vw,wo⟩ := neighbor_outside_small (mem_union_right (portColor D c) vs)
    ((card_union_le _ _).trans small) high
  have wd : w∈Shore D := by
    rcases reverse_boundary dir vh vw with rfl|rfl|wd
    · rcases dir with ⟨rfl,_⟩|⟨rfl,_⟩
      · exact (noa vw.symm).elim
      exact (nob vw.symm).elim
    · rcases dir with ⟨_,rfl⟩|⟨_,rfl⟩
      · exact (nob vw.symm).elim
      exact (noa vw.symm).elim
    exact wd
  refine ⟨w,?_,vw⟩
  rcases mem_union.mp (cover wd) with h|h
  · rcases mem_union.mp h with wp|wp
    · exact (wo (mem_union_left _ wp)).elim
    have dv : ¬G.Adj d v := by rcases dir with ⟨_,rfl⟩|⟨_,rfl⟩; exact nob; exact noa
    have dv' : d≠v := by
      rcases dir with ⟨_,rfl⟩|⟨_,rfl⟩
      · exact fun h=>(shore_off D).2 (h.symm ▸ vh)
      exact fun h=>(shore_off D).1 (h.symm ▸ vh)
    exact (out (mem_inter.mpr ⟨vh,d2 hc dv' dv (mem_filter.mp wp).2 vw.symm⟩)).elim
  rcases mem_union.mp h with wp|wp
  · exact (wo (mem_union_right _ wp)).elim
  exact wp

theorem no_tight_shells_in_reverse_alignment
    (hc : G.Connected) (two : G.dist a b=2)
    (even : ∀ x,(EvenFrom G x).card ≤ 6)
    (degree : ∀ u v : V,u≠v → 5 ≤ G.degree u ∨ 5 ≤ G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (none : ∀ w∈Shore D,¬(G.Adj a w ∧ G.Adj b w))
    (nonmix : ∀ u∈portColor D a,∀ v∈portColor D b,¬G.Adj u v)
    (cA : (portColor C a).card=4) (cB : (portColor C b).card=3)
    (pA : (portColor D a).card=2) (pB : (portColor D b).card=3)
    (eA : (secondShore D a).card=3) (eB : (secondShore D b).card=2)
    (cover : Shore D ⊆ (portColor D a∪portColor D b)∪(secondShore D a∪secondShore D b)) :
    False := by
  classical
  let A := portColor D a
  let B := portColor D b
  let E := secondShore D a
  let F := secondShore D b
  let H := B.filter (fun v=>5 ≤ G.degree v)
  have dis : Disjoint E F := by
    apply disjoint_left.mpr
    intro w we wf
    obtain ⟨u,ua,uw⟩ := local_shell_comes_from_port hc two (.inl rfl) we
    have fB (v : V) (vb : v∈B) (hi : 5 ≤ G.degree v) : G.Adj v w := by
      obtain ⟨vd,bv⟩ := mem_filter.mp vb
      exact tight_shell_high_contact hc (.inr ⟨rfl,rfl⟩) (by omega) vb
        (fun av=>none v vd ⟨av,bv⟩) hi w wf
    have big : 2 ≤ H.card := by
      by_contra! small
      have lowCard : 2 ≤ (B\H).card := by
        have split : (B\H).card+H.card=B.card :=
          card_sdiff_add_card_eq_card (filter_subset (fun v=>5 ≤ G.degree v) B)
        change B.card=3 at pB
        omega
      obtain ⟨s,sm,t,tm,st⟩ := one_lt_card.mp (show 1<(B\H).card by omega)
      have bad (y : V) (ym : y∈B\H) : ¬5 ≤ G.degree y :=
        fun h=>(mem_sdiff.mp ym).2 (mem_filter.mpr ⟨(mem_sdiff.mp ym).1,h⟩)
      exact (degree s t st).elim (bad s sm) (bad t tm)
    have sub : H ⊆ secondShore D u := by
      intro v vh
      obtain ⟨vb,vhi⟩ := mem_filter.mp vh
      obtain ⟨ud,au⟩ := mem_filter.mp ua
      obtain ⟨vd,bv⟩ := mem_filter.mp vb
      have ne : u≠v := fun e=>none v vd ⟨e ▸ au,bv⟩
      exact mem_inter.mpr ⟨vd,d2 hc ne (nonmix u ua v vb) uw (fB v vb vhi).symm⟩
    have q := card_le_card sub
    have k := local_d2_plus_foreign_le_five hc even cd ua
    rw [cA] at k
    omega
  have aNon : ∀ w∈E,¬G.Adj a w ∧ ¬G.Adj b w :=
    fun _ w=>nonmixed_shell_nonports hc two none nonmix (.inl ⟨rfl,rfl⟩) w
  have bNon : ∀ w∈F,¬G.Adj a w ∧ ¬G.Adj b w :=
    fun _ w=>nonmixed_shell_nonports hc two none nonmix (.inr ⟨rfl,rfl⟩) w
  have flip : Shore D ⊆ (B∪A)∪(F∪E) := by simpa [union_comm] using cover
  by_cases allF : ∀ w∈F,5 ≤ G.degree w
  · obtain ⟨u,ua,uh⟩ := anywhere_high_of_two degree (show 2 ≤ A.card by exact le_of_eq pA.symm)
    obtain ⟨ud,au⟩ := mem_filter.mp ua
    have sub : F⊆secondShore D u := by
      intro w wf
      have we : w∉E := fun e=>disjoint_left.mp dis e wf
      obtain ⟨t,te,wt⟩ := shell_needs_cross hc (.inr ⟨rfl,rfl⟩) flip
        (by omega) wf we (bNon w wf).1 (bNon w wf).2 (allF w wf)
      have wd := (mem_inter.mp wf).1
      have un : ¬G.Adj u w := fun uw=>we (mem_inter.mpr ⟨wd,
        d2 hc (fun e=>(shore_off D).1 (e.symm ▸ wd)) (bNon w wf).1 au uw⟩)
      have ne : u≠w := fun e=>(bNon w wf).1 (e ▸ au)
      have ut := tight_shell_high_contact hc (.inl ⟨rfl,rfl⟩) (by omega) ua
        (fun bu=>none u ud ⟨au,bu⟩) uh t te
      exact mem_inter.mpr ⟨wd,d2 hc ne un ut wt.symm⟩
    have q := card_le_card sub
    have k := local_d2_plus_foreign_le_five hc even cd ua
    rw [cA] at k
    change F.card=2 at eB
    omega
  push_neg at allF
  obtain ⟨z,zf,zl⟩ := allF
  have allE (w : V) (we : w∈E) : 5 ≤ G.degree w := by
    have wz : w≠z := fun e=>disjoint_left.mp dis (e ▸ we) zf
    exact (degree w z wz).resolve_right (by omega)
  obtain ⟨v,vb,vh⟩ := anywhere_high_of_two degree (show 2 ≤ B.card by change 2 ≤ (portColor D b).card; omega)
  obtain ⟨vd,bv⟩ := mem_filter.mp vb
  have sub : E⊆secondShore D v := by
    intro w we
    have wf : w∉F := fun f=>disjoint_left.mp dis we f
    obtain ⟨t,tf,wt⟩ := shell_needs_cross hc (.inl ⟨rfl,rfl⟩) cover
      (by omega) we wf (aNon w we).1 (aNon w we).2 (allE w we)
    have wd := (mem_inter.mp we).1
    have vn : ¬G.Adj v w := fun vw=>wf (mem_inter.mpr ⟨wd,
      d2 hc (fun e=>(shore_off D).2 (e.symm ▸ wd)) (aNon w we).2 bv vw⟩)
    have ne : v≠w := fun e=>(aNon w we).2 (e ▸ bv)
    have vt := tight_shell_high_contact hc (.inr ⟨rfl,rfl⟩) (by omega) vb
      (fun av=>none v vd ⟨av,bv⟩) vh t tf
    exact mem_inter.mpr ⟨wd,d2 hc ne vn vt wt.symm⟩
  have q := card_le_card sub
  have k := local_d2_plus_foreign_le_five hc even cd vb
  rw [cB] at k
  change E.card=3 at eA
  omega

#print axioms no_tight_shells_in_reverse_alignment
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
