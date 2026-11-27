import DegreeFiveReverseSupport189
import DegreeFiveOppositeNearParity189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private Shore shore_off shore_connected from DegreeFiveActualCut189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private Cmp portColor from DegreeFiveThreeForeignImpossible189
open private tight_shell_high_contact local_d2_plus_foreign_le_five nonmixed_shell_nonports
  from DegreeFiveReverseSupport189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- Nonmixed opposite 2+2 shore in the (3,3) case has at most seven
vertices: the low root forces both three-point nonport shells to agree,
and those shells then saturate the local porter spheres. -/
theorem two_two_nonmixed_small_of_low_both
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (none : ∀ v∈Shore D,¬(G.Adj a v ∧ G.Adj b v))
    (nonmix : ∀ u∈portColor D a,∀ v∈portColor D b,¬G.Adj u v)
    (cA : (portColor C a).card=3)
    (pA : (portColor D a).card=2) (pB : (portColor D b).card=2)
    (eA : (secondShore D a).card=3) (eB : (secondShore D b).card=3)
    (high : ∀ w∈Shore D,5≤G.degree w)
    {z : V} (zc : z∈Shore C) (za : G.dist z a=2) (zb : G.dist z b=2) :
    (Shore D).card≤7 := by
  classical
  let A := portColor D a
  let B := portColor D b
  let E := secondShore D a
  let F := secondShore D b
  have nall : ∀ w∈E∪F,¬G.Adj a w ∧ ¬G.Adj b w := by
    intro w wm
    rcases mem_union.mp wm with we|wf
    · exact nonmixed_shell_nonports hc two none nonmix (.inl ⟨rfl,rfl⟩) we
    exact nonmixed_shell_nonports hc two none nonmix (.inr ⟨rfl,rfl⟩) wf
  have id : (E∪F).filter (fun w=>¬G.Adj a w ∧ ¬G.Adj b w)=E∪F :=
    filter_eq_self.mpr nall
  have c3 := opposite_near_nonports_le_three hc two even cd zc za zb
  change ((E∪F).filter _).card≤3 at c3
  rw [id] at c3
  have ec : E.card=3 := eA
  have fc : F.card=3 := eB
  have a2 : A.card=2 := pA
  have b2 : B.card=2 := pB
  have eq : E=F :=
    (eq_of_subset_of_card_le (subset_union_left : E⊆E∪F) (by omega)).trans
      (eq_of_subset_of_card_le (subset_union_right : F⊆E∪F) (by omega)).symm
  have aAll {u : V} (ua : u∈A) : ∀ w∈E,G.Adj u w := by
    obtain ⟨ud,au⟩ := mem_filter.mp ua
    exact tight_shell_high_contact hc (.inl ⟨rfl,rfl⟩) (by omega) ua
      (fun bu=>none u ud ⟨au,bu⟩) (high u ud)
  have bAll {v : V} (vb : v∈B) : ∀ w∈E,G.Adj v w := by
    obtain ⟨vd,bv⟩ := mem_filter.mp vb
    intro w we
    rw [eq] at we
    exact tight_shell_high_contact hc (.inr ⟨rfl,rfl⟩) (by omega) vb
      (fun av=>none v vd ⟨av,bv⟩) (high v vd) w we
  let U := (A∪B)∪E
  obtain ⟨u,ua⟩ := card_pos.mp (show 0<A.card by omega)
  obtain ⟨ud,au⟩ := mem_filter.mp ua
  obtain ⟨e,ee⟩ := card_pos.mp (show 0<E.card by omega)
  have sphere : B=secondShore D u := by
    have sub : B⊆secondShore D u := by
      intro w wb
      obtain ⟨wd,bw⟩ := mem_filter.mp wb
      have ne : u≠w := fun h=>none w wd ⟨h ▸ au,bw⟩
      exact mem_inter.mpr ⟨wd,d2 hc ne (nonmix u ua w wb) (aAll ua e ee) (bAll wb e ee).symm⟩
    have h := local_d2_plus_foreign_le_five hc even cd ua
    rw [cA] at h
    exact eq_of_subset_of_card_le sub (by omega)
  have adjacentPort {x w : V} (xp : x∈A∪B) (wd : w∈Shore D) (wo : w∉U) :
      ¬G.Adj x w := by
    intro xw
    have na : ¬G.Adj a w := fun h=>wo (mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨wd,h⟩)))
    have nb : ¬G.Adj b w := fun h=>wo (mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨wd,h⟩)))
    rcases mem_union.mp xp with xa|xb
    · have ne : a≠w := fun h=>(shore_off D).1 (h.symm ▸ wd)
      have we : w∈E := mem_inter.mpr ⟨wd,d2 hc ne na (mem_filter.mp xa).2 xw⟩
      exact wo (mem_union_right _ we)
    have ne : b≠w := fun h=>(shore_off D).2 (h.symm ▸ wd)
    have wf : w∈F := mem_inter.mpr ⟨wd,d2 hc ne nb (mem_filter.mp xb).2 xw⟩
    exact wo (mem_union_right _ (eq.symm ▸ wf))
  have closed (x w : V) (xu : x∈U) (wd : w∈Shore D) (xw : G.Adj x w) : w∈U := by
    by_contra wo
    rcases mem_union.mp xu with xp|xe
    · exact adjacentPort xp wd wo xw
    have ne : u≠w := fun h=>wo (h ▸ mem_union_left E (mem_union_left B ua))
    have no := adjacentPort (mem_union_left B ua) wd wo
    have w2 : w∈secondShore D u := mem_inter.mpr ⟨wd,d2 hc ne no (aAll ua x xe) xw⟩
    exact wo (mem_union_left E (mem_union_right A (sphere.symm ▸ w2)))
  have cover : Shore D⊆U := by
    intro w wd
    let V' := ↑(↑(Shore D) : Set V)
    obtain ⟨q⟩ := (shore_connected D).preconnected (⟨u,ud⟩ : V') ⟨w,wd⟩
    have reach {x y : V'} (p : (G.induce (↑(Shore D) : Set V)).Walk x y) :
        x.val∈U → y.val∈U := by
      induction p with
      | nil => exact fun h=>h
      | @cons x v y xv p ih =>
        intro hx
        exact ih (closed x.val v.val hx v.property xv)
    exact reach q (mem_union_left E (mem_union_left B ua))
  have k := (card_le_card cover).trans (card_union_le _ _)
  have q := card_union_le A B
  omega

#print axioms two_two_nonmixed_small_of_low_both
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
