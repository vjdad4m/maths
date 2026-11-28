import TwoCutFourCenters189
import SixDistanceThreeShort189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset
open private CutGraph Shore shore_off shore_closed shore_disjoint shore_hit_a shore_hit_b
  from AdjacentCutFiveActual189
open private Cmp DeletionConnected from SixCutFar189
open private actual_two_shores from AdjacentCutFiveTwoOrderTwenty189
open private both_sides positive_even_cap near_port_even from TwoCutOrderCenters189
open private four_centers_from_split odd_both_across_even from TwoCutFourCenters189
open private local_universal_of_no_local_two from SixCutComponents189
open private no_common_far from SixDistanceThreeShort189
open private d2 from CrossSaturation189
open private swapCut from AdjacentCutFiveMixedNineGeom189
open FiveAdjacent (shore_swapCut)
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

private theorem card_of_four_sets (A B P Q : Finset V) (n : A.card+B.card+P.card+Q.card≤22)
    (cov : ∀ z : V,z≠a → z≠b → z∈A ∨ z∈B ∨ z∈P ∨ z∈Q) :
    Fintype.card V≤24 := by
  let R := ((A∪B)∪P)∪Q
  have covers : (univ : Finset V)⊆insert a (insert b R) := by
    intro z _
    by_cases za : z=a
    · simp [za]
    by_cases zb : z=b
    · simp [zb]
    rcases cov z za zb with h|h|h|h <;> simp [R,h]
  have h := card_le_card covers
  rw [card_univ] at h
  have i := card_insert_le a (insert b R)
  have j := card_insert_le b R
  have k := card_union_le ((A∪B)∪P) Q
  have l := card_union_le (A∪B) P
  have m := card_union_le A B
  change R.card≤((A∪B)∪P).card+Q.card at k
  omega

private theorem in_positive_even_of_dist_two {x z : V} (q : G.dist x z=2) :
    z∈PositiveEven G x := by
  classical
  have ne : z≠x := by intro e; rw [e,dist_self] at q; omega
  exact mem_erase.mpr ⟨ne,mem_filter.mpr ⟨mem_univ _,by rw [q]; decide⟩⟩

private theorem port_have_wasted_even (hc : G.Connected) (far : 3≤G.dist a b)
    (C : Cmp G a b) {x : V} (xc : x∈Shore C) (ax : G.Adj a x)
    (bp : ∃ y∈Shore C,G.Adj b y) {D : Cmp G a b} (cd : C≠D) :
    ∃ z,z∉Shore D ∧ z∈PositiveEven G x := by
  classical
  by_cases h : ∃ y∈Shore C,y∈DistanceTwo G x
  · obtain ⟨z,zc,hz⟩ := h
    exact ⟨z,fun zd=>disjoint_left.mp (shore_disjoint cd) zc zd,
      in_positive_even_of_dist_two (mem_filter.mp hz).2⟩
  push_neg at h
  obtain ⟨y,yc,by'⟩ := bp
  have yx : y≠x := fun e=>no_common_far far ⟨ax,e ▸ by'⟩
  have xy := (local_universal_of_no_local_two hc C xc h y yc).resolve_left yx
  have xb : x≠b := fun e=>(shore_off C).2 (e ▸ xc)
  have no : ¬G.Adj x b := fun e=>no_common_far far ⟨ax,e.symm⟩
  have two := d2 hc xb no xy by'.symm
  exact ⟨b,(shore_off D).2,in_positive_even_of_dist_two (mem_filter.mp two).2⟩

private theorem odd_center_wastes_even (hc : G.Connected) (far : 3≤G.dist a b)
    (C : Cmp G a b) {x : V} (xc : x∈Shore C)
    (ax : ¬Even (G.dist a x)) (bx : ¬Even (G.dist b x))
    (pa : ∃ y∈Shore C,G.Adj a y) (pb : ∃ z∈Shore C,G.Adj b z)
    {D : Cmp G a b} (cd : C≠D) :
    ∃ z,z∉Shore D ∧ z∈PositiveEven G x := by
  classical
  by_cases h : ∃ z∈Shore C,z∈DistanceTwo G x
  · obtain ⟨z,zc,hz⟩ := h
    exact ⟨z,fun zd=>disjoint_left.mp (shore_disjoint cd) zc zd,
      in_positive_even_of_dist_two (mem_filter.mp hz).2⟩
  push_neg at h
  have u := local_universal_of_no_local_two hc C xc h
  obtain ⟨y,yc,ay⟩ := pa
  obtain ⟨z,zc,bz⟩ := pb
  have da : G.dist a x≤2 := by
    rcases u y yc with rfl|xy
    · rw [dist_eq_one_iff_adj.mpr ay]; decide
    have q := G.dist_le (Walk.cons ay (Walk.cons xy.symm .nil))
    simpa using q
  have db : G.dist b x≤2 := by
    rcases u z zc with rfl|xz
    · rw [dist_eq_one_iff_adj.mpr bz]; decide
    have q := G.dist_le (Walk.cons bz (Walk.cons xz.symm .nil))
    simpa using q
  simp only [Nat.even_iff] at ax bx
  have ae : G.dist a x=1 := by omega
  have be : G.dist b x=1 := by omega
  exact (no_common_far far ⟨dist_eq_one_iff_adj.mp ae,dist_eq_one_iff_adj.mp be⟩).elim

private noncomputable def cropped (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : Finset V) (x : V) : Finset V := by classical exact W.filter (fun z=>z∈PositiveEven G x)

private theorem crop_le_five (even : ∀ x,(EvenFrom G x).card≤7) (W : Finset V) (x : V)
    (w : ∃ z,z∉W ∧ z∈PositiveEven G x) : (cropped G W x).card≤5 := by
  classical
  obtain ⟨z,zn,zp⟩ := w
  have nz : z∉cropped G W x := fun h=>zn (mem_filter.mp h).1
  have sub : insert z (cropped G W x)⊆PositiveEven G x :=
    insert_subset zp (fun _ h=>(mem_filter.mp h).2)
  have c := card_le_card sub
  rw [card_insert_of_not_mem nz] at c
  have p := positive_even_cap (d:=6) (even x)
  omega

theorem order_le_twenty_four_at_distance_two (hc : G.Connected) (ab : a≠b)
    (even : ∀ z,(EvenFrom G z).card≤7) (conn : DeletionConnected G)
    (cut : 2≤Nat.card (Cmp G a b)) (two : G.dist a b=2) :
    Fintype.card V≤24 := by
  classical
  obtain ⟨S,la,lb,ra,rb,laL,lbL,raR,rbR,ala,blb,ara,brb⟩ := both_sides ab conn cut
  obtain ⟨x,y,cover⟩ := four_centers_from_split hc ab S laL lbL raR rbR ala blb ara brb
  have bb := in_positive_even_of_dist_two two
  have aa := in_positive_even_of_dist_two (by rwa [dist_comm])
  have ca := card_erase_of_mem bb
  have cb := card_erase_of_mem aa
  have pa := positive_even_cap (d:=6) (even a)
  have pb := positive_even_cap (d:=6) (even b)
  have px := positive_even_cap (d:=6) (even x)
  have py := positive_even_cap (d:=6) (even y)
  apply card_of_four_sets ((PositiveEven G a).erase b) ((PositiveEven G b).erase a)
    (PositiveEven G x) (PositiveEven G y) (by omega)
  intro z za zb
  rcases cover z za zb with h|h|h|h
  · exact .inl (mem_erase.mpr ⟨zb,h⟩)
  · exact .inr (.inl (mem_erase.mpr ⟨za,h⟩))
  · exact .inr (.inr (.inl h))
  exact .inr (.inr (.inr h))

theorem order_le_twenty_four_at_distance_three (hc : G.Connected) (ab : a≠b)
    (even : ∀ z,(EvenFrom G z).card≤7) (conn : DeletionConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (cut : 2≤Nat.card (Cmp G a b)) (far : 3≤G.dist a b) :
    Fintype.card V≤24 := by
  classical
  obtain ⟨C,D,cd,cover⟩ := actual_two_shores (component_card_eq_two_at_six hc ab even conn degree cut)
  let oo (x : V) := ¬Even (G.dist a x) ∧ ¬Even (G.dist b x)
  have Cpa := shore_hit_a ab conn C
  have Cpb := shore_hit_b ab conn C
  have Dpa := shore_hit_a ab conn D
  have Dpb := shore_hit_b ab conn D
  have pa := positive_even_cap (d:=6) (even a)
  have pb := positive_even_cap (d:=6) (even b)
  have term {z : V} (za : z≠a) (zb : z≠b) :
      z∈PositiveEven G a ∨ z∈PositiveEven G b ∨ oo z := by
    by_cases ea : Even (G.dist a z)
    · exact .inl (mem_erase.mpr ⟨za,mem_filter.mpr ⟨mem_univ _,ea⟩⟩)
    by_cases eb : Even (G.dist b z)
    · exact .inr (.inl (mem_erase.mpr ⟨zb,mem_filter.mpr ⟨mem_univ _,eb⟩⟩))
    exact .inr (.inr ⟨ea,eb⟩)
  have oneSided (K L : Cmp G a b) (kl : K≠L)
      (h : ∀ z,z≠a → z≠b → oo z → z∈Shore L) : Fintype.card V≤24 := by
    obtain ⟨x,xk,ax⟩ := shore_hit_a ab conn K
    obtain ⟨y,yk,by'⟩ := shore_hit_b ab conn K
    have far' : 3≤G.dist b a := by rwa [dist_comm]
    have wx := port_have_wasted_even hc far K xk ax (shore_hit_b ab conn K) kl
    have wy : ∃ z,z∉Shore L ∧ z∈PositiveEven G y := by
      have kl' : swapCut K≠swapCut L := fun e=>kl (swapCut.injective e)
      have yk' : y∈Shore (swapCut K) := by rwa [shore_swapCut]
      have op := shore_hit_b ab.symm conn (swapCut K)
      simpa only [shore_swapCut] using
        (port_have_wasted_even (a:=b) (b:=a) hc far' (swapCut K) yk' by' op kl')
    have px := crop_le_five even (Shore L) x wx
    have py := crop_le_five even (Shore L) y wy
    apply card_of_four_sets (PositiveEven G a) (PositiveEven G b)
      (cropped G (Shore L) x) (cropped G (Shore L) y) (by omega)
    intro z za zb
    rcases term za zb with q|q|q
    · exact .inl q
    · exact .inr (.inl q)
    have zl := h z za zb q
    have zk : z∉Shore K := fun k=>disjoint_left.mp (shore_disjoint kl) k zl
    by_cases le : G.dist a z≤G.dist b z
    · exact .inr (.inr (.inl (mem_filter.mpr ⟨zl,near_port_even (Shore K) hc xk zk
        (shore_closed K) (fun e=>(shore_off K).2 (e ▸ xk)) ax le q.1⟩)))
    exact .inr (.inr (.inr (mem_filter.mpr ⟨zl,near_port_even (a:=b) (b:=a) (Shore K)
      hc yk zk (fun u um v uv=>by simpa only [or_left_comm (a:=v=a) (b:=v=b)] using shore_closed K u um v uv)
      (fun e=>(shore_off K).1 (e ▸ yk)) by' (by omega) q.2⟩)))
  by_cases cenC : ∃ x∈Shore C,oo x
  · by_cases cenD : ∃ y∈Shore D,oo y
    · obtain ⟨x,xc,xo⟩ := cenC
      obtain ⟨y,yd,yo⟩ := cenD
      have wx := odd_center_wastes_even hc far C xc xo.1 xo.2 Cpa Cpb cd
      have wy := odd_center_wastes_even hc far D yd yo.1 yo.2 Dpa Dpb cd.symm
      have px := crop_le_five even (Shore D) x wx
      have py := crop_le_five even (Shore C) y wy
      apply card_of_four_sets (PositiveEven G a) (PositiveEven G b)
        (cropped G (Shore D) x) (cropped G (Shore C) y) (by omega)
      intro z za zb
      rcases term za zb with q|q|q
      · exact .inl q
      · exact .inr (.inl q)
      rcases cover za zb with zc|zd
      · have zo : z∉Shore D := fun h=>disjoint_left.mp (shore_disjoint cd) zc h
        exact .inr (.inr (.inr (mem_filter.mpr ⟨zc,odd_both_across_even (Shore D) hc yd zo
          (shore_closed D) yo.1 yo.2 q.1 q.2⟩)))
      have zo : z∉Shore C := fun h=>disjoint_left.mp (shore_disjoint cd) h zd
      exact .inr (.inr (.inl (mem_filter.mpr ⟨zd,odd_both_across_even (Shore C) hc xc zo
        (shore_closed C) xo.1 xo.2 q.1 q.2⟩)))
    exact oneSided D C cd.symm (fun z za zb k=>(cover za zb).resolve_right (fun dz=>cenD ⟨z,dz,k⟩))
  exact oneSided C D cd (fun z za zb k=>(cover za zb).resolve_left (fun cz=>cenC ⟨z,cz,k⟩))

#print axioms order_le_twenty_four_at_distance_two
#print axioms order_le_twenty_four_at_distance_three
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
