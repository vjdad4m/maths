import DegreeFiveReverseTight189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset
open private Shore shore_off from DegreeFiveActualCut189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private Cmp portColor from DegreeFiveThreeForeignImpossible189
open private local_shell_comes_from_port from DegreeFiveNonmixedThreeFour189
open private tight_shell_high_contact local_d2_plus_foreign_le_five nonmixed_shell_nonports reverse_boundary
  from DegreeFiveReverseSupport189
open private shell_needs_cross from DegreeFiveReverseTight189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- The all-high opposite shore cannot have a tight two-point b-shell.
No exact cardinality for the a-shell is needed. -/
theorem no_two_b_shell_in_all_high_reverse
    (hc : G.Connected) (two : G.dist a b=2)
    (even : ∀ x,(EvenFrom G x).card≤6)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (none : ∀ w∈Shore D,¬(G.Adj a w ∧ G.Adj b w))
    (nonmix : ∀ u∈portColor D a,∀ v∈portColor D b,¬G.Adj u v)
    (cA : (portColor C a).card=4)
    (pA : (portColor D a).card=2) (pB : (portColor D b).card=3)
    (eA : (secondShore D a).card≤4) (eB : (secondShore D b).card=2)
    (cover : Shore D ⊆ (portColor D a∪portColor D b)∪(secondShore D a∪secondShore D b))
    (high : ∀ w∈Shore D,5≤G.degree w) : False := by
  classical
  let A := portColor D a
  let B := portColor D b
  let E := secondShore D a
  let F := secondShore D b
  have a2 : A.card=2 := pA
  have b3 : B.card=3 := pB
  have f2 : F.card=2 := eB
  have e4 : E.card≤4 := eA
  have localCap {u : V} (ua : u∈A) : (secondShore D u).card≤1 := by
    have k := local_d2_plus_foreign_le_five hc even cd ua
    rw [cA] at k
    omega
  have neqLocal {u x y : V} (ua : u∈A)
      (xd : x∈secondShore D u) (yd : y∈secondShore D u) : x=y := by
    by_contra h
    have q := one_lt_card.mpr ⟨x,xd,y,yd,h⟩
    have cap := localCap ua
    omega
  have tight {v : V} (vp : v∈B) : ∀ w∈F,G.Adj v w := by
    obtain ⟨vd,bv⟩ := mem_filter.mp vp
    exact tight_shell_high_contact hc (.inr ⟨rfl,rfl⟩) (by omega) vp
      (fun av=>none v vd ⟨av,bv⟩) (high v vd)
  have dis : Disjoint E F := by
    apply disjoint_left.mpr
    intro w we wf
    obtain ⟨u,ua,uw⟩ := local_shell_comes_from_port hc two (.inl rfl) we
    obtain ⟨ud,au⟩ := mem_filter.mp ua
    have sub : B ⊆ secondShore D u := by
      intro v vb
      obtain ⟨vd,bv⟩ := mem_filter.mp vb
      have ne : u≠v := fun e=>none v vd ⟨e ▸ au,bv⟩
      exact mem_inter.mpr ⟨vd,d2 hc ne (nonmix u ua v vb) uw (tight vb w wf).symm⟩
    have q := (card_le_card sub).trans (localCap ua)
    omega
  have nonA (w : V) (wf : w∈F) : ¬G.Adj a w :=
    (nonmixed_shell_nonports hc two none nonmix (.inr ⟨rfl,rfl⟩) wf).1
  have nonB (w : V) (wf : w∈F) : ¬G.Adj b w :=
    (nonmixed_shell_nonports hc two none nonmix (.inr ⟨rfl,rfl⟩) wf).2
  have aNot {u w : V} (ua : u∈A) (wf : w∈F) : ¬G.Adj u w := by
    intro uw
    have wd := (mem_inter.mp wf).1
    have neq : a≠w := fun e=>(shore_off D).1 (e.symm ▸ wd)
    exact disjoint_left.mp dis (mem_inter.mpr ⟨wd,d2 hc neq (nonA w wf)
      (mem_filter.mp ua).2 uw⟩) wf
  have lift {u w t : V} (ua : u∈A) (wf : w∈F) (ut : G.Adj u t) (wt : G.Adj w t) :
      w∈secondShore D u := by
    have ne : u≠w := fun e=>nonA w wf (e ▸ (mem_filter.mp ua).2)
    exact mem_inter.mpr ⟨(mem_inter.mp wf).1,d2 hc ne (aNot ua wf) ut wt.symm⟩
  obtain ⟨w,wf,s,sf,ws⟩ := one_lt_card.mp (show 1<F.card by omega)
  have flip : Shore D ⊆ (B∪A)∪(F∪E) := by simpa [union_comm] using cover
  have cross (r : V) (rf : r∈F) : ∃ t∈E,G.Adj r t :=
    shell_needs_cross hc (.inr ⟨rfl,rfl⟩) flip (by omega)
      rf (fun h=>disjoint_left.mp dis h rf) (nonA r rf) (nonB r rf)
      (high r (mem_inter.mp rf).1)
  obtain ⟨t,te,wt⟩ := cross w wf
  obtain ⟨q,qe,sq⟩ := cross s sf
  obtain ⟨u,ua,ut⟩ := local_shell_comes_from_port hc two (.inl rfl) te
  obtain ⟨v,va,vq⟩ := local_shell_comes_from_port hc two (.inl rfl) qe
  have wu := lift ua wf ut wt
  have sv := lift va sf vq sq
  have uv : u≠v := fun e=>ws (neqLocal ua wu (e.symm ▸ sv))
  have uq : ¬G.Adj u q := fun h=>ws (neqLocal ua wu (lift ua sf h sq))
  have uvEdge : G.Adj u v := by
    by_contra nuv
    obtain ⟨ud,au⟩ := mem_filter.mp ua
    have no : ¬G.Adj b u := fun e=>none u ud ⟨au,e⟩
    have coverA : A={u,v} := by
      apply (eq_of_subset_of_card_le _ _).symm
      · intro x hx
        rcases mem_insert.mp hx with rfl|h
        · exact ua
        obtain rfl := mem_singleton.mp h
        exact va
      · simpa [uv] using a2.le
    have sub : G.neighborFinset u ⊆ insert a (E.erase q) := by
      intro y yn
      have uy := (mem_neighborFinset G _ _).mp yn
      rcases reverse_boundary (.inl ⟨rfl,rfl⟩) ud uy with rfl|rfl|yd
      · exact mem_insert_self _ _
      · exact (no uy.symm).elim
      apply mem_insert_of_mem
      have hy : y≠q := fun e=>uq (e ▸ uy)
      refine mem_erase.mpr ⟨hy,?_⟩
      by_cases ay : G.Adj a y
      · have yp : y∈A := mem_filter.mpr ⟨yd,ay⟩
        rw [coverA] at yp
        rcases mem_insert.mp yp with rfl|h
        · exact (G.loopless _ uy).elim
        obtain rfl := mem_singleton.mp h
        exact (nuv uy).elim
      have ne : a≠y := fun e=>(shore_off D).1 (e.symm ▸ yd)
      exact mem_inter.mpr ⟨yd,d2 hc ne ay au uy⟩
    have cap := (card_le_card sub).trans (card_insert_le _ _)
    rw [card_neighborFinset_eq_degree,card_erase_of_mem qe] at cap
    have dg := high u ud
    omega
  have qd := (mem_inter.mp qe).1
  have qu : q∈secondShore D u := by
    -- The nonport q cannot equal the a-porter u.
    have n : u≠q := by
      intro eq
      have aq : G.Adj a q := eq ▸ (mem_filter.mp ua).2
      have first := dist_eq_one_iff_adj.mpr aq
      have second := (mem_filter.mp (mem_inter.mp qe).2).2
      omega
    exact mem_inter.mpr ⟨qd,d2 hc n uq uvEdge vq⟩
  have wq := neqLocal ua wu qu
  exact disjoint_left.mp dis (wq.symm ▸ qe) wf

#print axioms no_two_b_shell_in_all_high_reverse
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
