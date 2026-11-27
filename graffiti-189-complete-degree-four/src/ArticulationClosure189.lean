import ArticulationSmall189
import ArticulationClique189

universe u
namespace Graffiti189LongestPath.CrossSaturation
open SimpleGraph SimpleGraph.Walk Finset
variable {V : Type u} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

def RootedSpan (G : SimpleGraph V) (r : V) : Prop :=
  ∃ a,∃ p : G.Walk r a,p.IsPath ∧ ∀ z,z∈p.support

def RootedClosureAPI : Prop :=
  ∀ {U : Type u} [Fintype U] [DecidableEq U] {J K : SimpleGraph U}
    [DecidableRel J.Adj] [DecidableRel K.Adj],
    J ≤ K → ∀ r, (∀ x y, K.Adj x y → ¬J.Adj x y → Fintype.card U≤J.degree x+J.degree y) →
      RootedSpan K r → RootedSpan J r

def completeWith (J : SimpleGraph V) (A : Finset V) : SimpleGraph V where
  Adj x y := J.Adj x y ∨ x∈A ∧ y∈A ∧ x≠y
  symm := by
    intro x y h
    exact h.imp Adj.symm (fun ⟨h1,h2,ne⟩=>⟨h2,h1,ne.symm⟩)
  loopless := fun x h=>h.elim (J.loopless x) (fun h=>h.2.2 rfl)

theorem completeWith_of_mem (J : SimpleGraph V) (A : Finset V) :
    CompleteOn (completeWith J A) A :=
  fun _ ha _ hb ne=>Or.inr ⟨ha,hb,ne⟩

theorem completeWith_mono (J : SimpleGraph V) (A : Finset V) : J ≤ completeWith J A :=
  fun _ _ e=>Or.inl e

theorem close_completed_class {J : SimpleGraph V} [DecidableRel J.Adj]
    (ore : RootedClosureAPI.{u}) (A : Finset V) (r : V)
    (d : ∀ x∈A,∀ y∈A,Fintype.card V≤J.degree x+J.degree y)
    (path : RootedSpan (completeWith J A) r) : RootedSpan J r := by
  classical
  apply ore (completeWith_mono J A) r _ path
  intro x y xy no
  obtain ⟨xa,ya,_⟩ := xy.resolve_left no
  exact d _ xa _ ya

namespace ArticulationPair
open private left_boundary' from ArticulationEight189
variable {c : V} (S : Graffiti189LongestPath.CrossSaturation.ArticulationPair G c)

private theorem side_any_internal_neighbor {z : V} (zl : z∈S.L) (two : 2≤S.L.card) :
    ∃ y∈S.L,G.Adj z y := by
  classical
  obtain ⟨w,wm⟩ : (S.L.erase z).Nonempty := card_pos.mp (by rw [card_erase_of_mem zl]; omega)
  have ⟨wz,wl⟩ := mem_erase.mp wm
  let W : Set V := ↑S.L
  obtain ⟨p⟩ := S.joinedL.preconnected (⟨z,zl⟩ : W) (⟨w,wl⟩ : W)
  cases p with
  | nil => exact (wz rfl).elim
  | @cons a b d e p => exact ⟨b.val,b.property,e⟩

private theorem small_left_rooted (ore : RootedClosureAPI.{u})
    (hc : G.Connected) (even : ∀ x, (EvenFrom G x).card≤5)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    (small : S.L.card≤7) :
    ∃ y,∃ p : G.Walk c y,p.IsPath ∧ ∀ z,z∈p.support ↔ z=c ∨ z∈S.L := by
  classical
  obtain ⟨x,xl,cx⟩ := S.hitL
  by_cases single : S.L.card≤1
  · have eq : S.L={x} :=
      (eq_of_subset_of_card_le (singleton_subset_iff.mpr xl) (by simpa)).symm
    refine ⟨x,Walk.cons cx .nil,Walk.IsPath.cons (by simp) (by simpa using cx.ne),?_⟩
    intro z
    simp [eq,support_cons]
  apply S.lift_rooted_with_articulation
  let F := insert c S.L
  let U := ↑(↑F : Set V)
  let J := G.induce (↑F : Set V)
  let root : U := ⟨c,mem_insert_self _ _⟩
  let A : Finset U := univ.filter fun z=> z.val∈S.L ∧ 4≤G.degree z.val
  let K := completeWith J A
  change RootedSpan J root
  have ul : ∀ z : U, z≠root → z.val∈S.L := by
    intro z zr
    rcases mem_insert.mp z.property with e|h
    · exact (zr (Subtype.ext e)).elim
    · exact h
  have Fcard : Fintype.card U≤8 := by
    change Fintype.card {v : V // v∈F} ≤ 8
    rw [Fintype.card_coe]
    have cc := card_insert_le c S.L
    change F.card≤8
    exact cc.trans (by omega)
  have ad (z : U) (za : z∈A) : 4≤J.degree z := by
    obtain ⟨zl,dh⟩ := (mem_filter.mp za).2
    rw [S.left_degree_preserved z.val zl]
    exact dh
  apply close_completed_class ore A root (fun a ha b hb=>by
    have h1 := ad a ha
    have h2 := ad b hb
    omega)
  by_cases low : ∃ z∈S.L, ¬4≤G.degree z
  · obtain ⟨z,zl,zlow⟩ := low
    let zz : U := ⟨z,mem_insert_of_mem zl⟩
    have rzne : root≠zz := by
      intro e
      have h : c=z := congrArg Subtype.val e
      exact S.offL (h.symm ▸ zl)
    have hight (v : U) (vr : v≠root) (vz : v≠zz) : v∈A := by
      have vz' : v.val≠z := fun h=>vz (Subtype.ext h)
      exact mem_filter.mpr ⟨mem_univ _,ul v vr,(degree _ _ vz').resolve_right zlow⟩
    have clique : CompleteOn K ((univ.erase root).erase zz) := by
      intro v va w wa vw
      have vne := mem_erase.mp va
      have wne := mem_erase.mp wa
      exact completeWith_of_mem J A v (hight v (mem_erase.mp vne.2).1 vne.1)
        w (hight w (mem_erase.mp wne.2).1 wne.1) vw
    by_cases cz : G.Adj c z
    · obtain ⟨y,yl,zy⟩ := side_any_internal_neighbor S zl (by omega)
      let yy : U := ⟨y,mem_insert_of_mem yl⟩
      have yr : yy≠root := by
        intro e
        have h : y=c := congrArg Subtype.val e
        exact S.offL (h ▸ yl)
      exact rooted_path_through_outlier_into_clique K (completeWith_mono J A (show J.Adj root zz from cz))
        (completeWith_mono J A (show J.Adj zz yy from zy)) yr clique
    have g4 := S.left_size_ge_four_of_two degree (by omega)
    obtain ⟨v,vl,w,wl,vw,cv,zw⟩ := S.distinct_root_and_outlier_ports hc even degree zl cz (by omega)
    let vv : U := ⟨v,mem_insert_of_mem vl⟩
    let ww : U := ⟨w,mem_insert_of_mem wl⟩
    have vz : vv≠zz := by
      intro e
      have h : v=z := congrArg Subtype.val e
      exact cz (h ▸ cv)
    have wr : ww≠root := by
      intro e
      have h : w=c := congrArg Subtype.val e
      exact S.offL (h ▸ wl)
    have vvww : vv≠ww := fun h=>vw (congrArg Subtype.val h)
    exact rooted_path_from_clique_to_outlier K
      (completeWith_mono J A (show J.Adj root vv from cv))
      (completeWith_mono J A (show J.Adj ww zz from zw.symm)) rzne vz wr vvww clique
  have clique : CompleteOn K (univ.erase root) := by
    intro v va w wa vw
    have mem (o : U) (om : o∈(univ : Finset U).erase root) : o∈A := by
      have ol := ul o (mem_erase.mp om).1
      have oh : 4≤G.degree o.val := Classical.byContradiction (fun neg=>low ⟨o.val,ol,neg⟩)
      exact mem_filter.mpr ⟨mem_univ _,ol,oh⟩
    exact completeWith_of_mem J A _ (mem v va) _ (mem w wa) vw
  let xx : U := ⟨x,mem_insert_of_mem xl⟩
  exact rooted_path_from_root_into_clique K (completeWith_mono J A (show J.Adj root xx from cx)) clique

private theorem large_left_rooted (ore : RootedClosureAPI.{u})
    (hc : G.Connected) (even : ∀ x, (EvenFrom G x).card≤5)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    (eight : S.L.card=8) :
    ∃ y,∃ p : G.Walk c y,p.IsPath ∧ ∀ z,z∈p.support ↔ z=c ∨ z∈S.L := by
  classical
  obtain ⟨x,xl,cx⟩ := S.hitL
  obtain ⟨y,yr,cy⟩ := S.hitR
  apply S.prefix_induced_side_path xl cx
  let U := ↑(↑S.L : Set V)
  let J := G.induce (↑S.L : Set V)
  let root : U := ⟨x,xl⟩
  change RootedSpan J root
  have U8 : Fintype.card U=8 := by
    change Fintype.card {v : V // v∈S.L}=8
    rw [Fintype.card_coe,eight]
  have all_case (d : ∀ v : U, 4≤J.degree v) : RootedSpan J root := by
    refine close_completed_class ore univ root ?_ ?_
    · intro v _ w _
      have h1 := d v
      have h2 := d w
      omega
    obtain ⟨e,p,pp,ps⟩ := rooted_path_in_clique univ (completeWith_of_mem J univ) (mem_univ root)
    exact ⟨e,p,pp,fun v=>(ps v).mpr (mem_univ _)⟩
  by_cases one : S.R.card≤1
  · have eq : S.R={y} :=
      (eq_of_subset_of_card_le (singleton_subset_iff.mpr yr) (by simpa)).symm
    have hi := S.eight_singleton_internal_min_degree hc even degree eight eq
    exact all_case (fun v=>(inside_card_eq_degree_induce (G:=G) S.L v) ▸ hi _ v.property)
  have two : 2≤S.R.card := by omega
  have hi := S.eight_nonsingleton_high_internal_degree hc even degree eight two
  have rootHigh : 4≤G.degree x := by
    obtain ⟨n,_,port⟩ := S.eight_nonsingleton_port_universal hc even degree eight two
    have sub : S.L.erase x ⊆ G.neighborFinset x := by
      intro v vm
      obtain ⟨vx,vl⟩ := mem_erase.mp vm
      exact (mem_neighborFinset _ _ _).mpr ((port x xl cx v vl).resolve_left vx)
    have b := card_le_card sub
    rw [card_neighborFinset_eq_degree,card_erase_of_mem xl,eight] at b
    omega
  by_cases low : ∃ z∈S.L, ¬4≤G.degree z
  · obtain ⟨z,zl,zlow⟩ := low
    have zx : z≠x := fun e=>zlow (e.symm ▸ rootHigh)
    let zz : U := ⟨z,zl⟩
    let A : Finset U := univ.erase zz
    have ha (v : U) (va : v∈A) : 4≤J.degree v := by
      have vz : v.val≠z := fun e=>(mem_erase.mp va).1 (Subtype.ext e)
      have dh := (degree _ _ vz).resolve_right zlow
      exact (inside_card_eq_degree_induce (G:=G) S.L v) ▸ hi _ v.property dh
    refine close_completed_class ore A root ?_ ?_
    · intro v vm w wm
      have v4 := ha v vm
      have w4 := ha w wm
      omega
    obtain ⟨w,wm,zw⟩ := S.eight_nonsingleton_every_other_has_residual_neighbor hc even degree eight two
      xl cx z (mem_erase.mpr ⟨zx,zl⟩)
    obtain ⟨wx,wl⟩ := mem_erase.mp wm
    let ww : U := ⟨w,wl⟩
    have rz : root≠zz := fun e=>zx.symm (congrArg Subtype.val e)
    have wz : ww≠zz := fun e=>zw.ne.symm (congrArg Subtype.val e)
    have rw' : root≠ww := fun e=>wx.symm (congrArg Subtype.val e)
    exact rooted_path_of_clique_and_outlier (completeWith J A) rz wz rw'
      (completeWith_mono J A (show J.Adj ww zz from zw.symm)) (completeWith_of_mem J A)
  apply all_case
  intro v
  have dh : 4≤G.degree v.val := Classical.byContradiction (fun n=>low ⟨v.val,v.property,n⟩)
  exact (inside_card_eq_degree_induce (G:=G) S.L v) ▸ hi _ v.property dh

theorem left_rooted_at_articulation (ore : RootedClosureAPI.{u})
    (hc : G.Connected) (even : ∀ x, (EvenFrom G x).card≤5)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v) :
    ∃ y,∃ p : G.Walk c y,p.IsPath ∧ ∀ z,z∈p.support ↔ z=c ∨ z∈S.L := by
  have bound := (S.sides_le_eight hc even).1
  by_cases small : S.L.card≤7
  · exact small_left_rooted S ore hc even degree small
  exact large_left_rooted S ore hc even degree (by omega)

end ArticulationPair

theorem traceable_at_articulation_of_rooted_closure (ore : RootedClosureAPI.{u}) (hc : G.Connected)
    (even : ∀ x, (EvenFrom G x).card≤5)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    (c : V) (cut : ¬(G.induce {z : V | z≠c}).Connected) : ∃ a, RootedSpan G a := by
  classical
  by_cases small : Fintype.card V≤1
  · have ss := Fintype.card_le_one_iff_subsingleton.mp small
    exact ⟨c,c,Walk.nil,by simp,fun z=>by simp [ss.elim z c]⟩
  obtain ⟨S⟩ := articulation_pair_of_disconnected hc c even degree (by omega) cut
  exact S.splice_rooted (S.left_rooted_at_articulation ore hc even degree)
    (S.swapSides.left_rooted_at_articulation ore hc even degree)

#print axioms ArticulationPair.left_rooted_at_articulation
#print axioms traceable_at_articulation_of_rooted_closure
end Graffiti189LongestPath.CrossSaturation
