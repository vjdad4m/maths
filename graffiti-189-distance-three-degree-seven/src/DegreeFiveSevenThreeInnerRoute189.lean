import DegreeFiveSevenThreeInnerGeometry189

namespace Graffiti189LongestPath.CrossSaturation.Split.Five
open SimpleGraph SimpleGraph.Walk Finset
open private not_common from DegreeFiveFourPort189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} (S : Graffiti189LongestPath.CrossSaturation.Split G a b)
set_option linter.unusedSectionVars false

theorem four_a_no_bridge_three_inner_free (hc : G.Connected) (far : 3≤G.dist a b)
    (even : ∀ x,(EvenFrom G x).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (a4 : S.localA.card=4) (foreign : S.foreignA.card=3)
    (b4 : (S.L.filter (G.Adj b)).card≤4) (i3 : (farNonports S.L a b G).card=3)
    (big : 9≤S.L.card) (noBridge : ¬portBridge S)
    (visible : farNonports S.L a b G⊆secondA G S.L a)
    (bcap : (secondA G S.L b).card≤2) :
    ∃ u v,G.Adj a u ∧ RouteOn G S.L u v := by
  classical
  let A := S.localA
  let B := S.L.filter (G.Adj b)
  let I := farNonports S.L a b G
  obtain ⟨_,acl,bcl,i,j,k,ij,ik,jk,eqI,kAdj,active,⟨p,pa,pi⟩,⟨y,yB,jy⟩,edge⟩ :=
    four_a_no_bridge_three_inner_geometry S hc far even degree a4 foreign b4 i3 big noBridge visible bcap
  change CompleteOn G A at acl
  change I={i,j,k} at eqI
  change A.card=4 at a4
  have ii : i∈I := by simp [eqI]
  have ji : j∈I := by simp [eqI]
  have ki : k∈I := by simp [eqI]
  have ia : i∉A := fun h=>(mem_filter.mp ii).2.1 (mem_filter.mp h).2
  have ja : j∉A := fun h=>(mem_filter.mp ji).2.1 (mem_filter.mp h).2
  have ka : k∉A := fun h=>(mem_filter.mp ki).2.1 (mem_filter.mp h).2
  let F := A.filter (fun x=>G.Adj x i)
  have pf : p∈F := mem_filter.mpr ⟨pa,pi⟩
  have make : ∃ u∈A,RouteOn G (A∪I) u j := by
    by_cases many : 2≤F.card
    · have other : ∃ q∈F,q≠p := by
        apply Classical.byContradiction
        intro no
        have sub : F⊆{p} := fun q qq=>mem_singleton.mpr
          (Classical.byContradiction (fun h=>no ⟨q,qq,h⟩))
        have k := card_le_card sub
        rw [card_singleton] at k
        omega
      obtain ⟨q,qF,qp⟩ := other
      obtain ⟨qa,qi⟩ := mem_filter.mp qF
      let R := (A.erase p).erase q
      have qr : q∈A.erase p := mem_erase.mpr ⟨qp,qa⟩
      have pos : 0<R.card := by
        change 0<((A.erase p).erase q).card
        rw [card_erase_of_mem qr,card_erase_of_mem pa,a4]
        decide
      obtain ⟨r,rR⟩ := card_pos.mp pos
      have sub : R⊆A := (erase_subset _ _).trans (erase_subset _ _)
      have C : CompleteOn G R := fun z zr w wr zw=>acl z (sub zr) w (sub wr) zw
      obtain ⟨u,w,wp,ws⟩ := rooted_path_in_clique R C rR
      have path : RouteOn G R u r := (show RouteOn G R r u from ⟨w,wp,ws⟩).reverse
      have ua : u∈A := sub ((ws u).mp w.end_mem_support)
      have po : p∉R := fun h=>(mem_erase.mp (mem_erase.mp h).2).1 rfl
      have qo : q∉R := fun h=>(mem_erase.mp h).1 rfl
      have step₁ := path.suffix (kAdj r (sub rR)) (fun h=>ka (sub h))
      have step₂ := step₁.suffix (kAdj p pa).symm (by
        have pk : p≠k := fun h=>ka (h ▸ pa)
        simp [pk,po])
      have step₃ := step₂.suffix pi (by
        have ip : i≠p := fun h=>ia (h.symm ▸ pa)
        have ir : i∉R := fun h=>ia (sub h)
        simp [ip,ik,ir])
      have step₄ := step₃.suffix qi.symm (by
        have qii : q≠i := fun h=>ia (h ▸ qa)
        have qk : q≠k := fun h=>ka (h ▸ qa)
        simp [qii,qp,qk,qo])
      have step₅ := step₄.suffix ((active q qa).mp qi) (by
        have jq : j≠q := fun h=>ja (h.symm ▸ qa)
        have jp : j≠p := fun h=>ja (h.symm ▸ pa)
        have jr : j∉R := fun h=>ja (sub h)
        simp [jq,ij.symm,jp,jk,jr])
      have eq : insert j (insert q (insert i (insert p (insert k R))))=A∪I := by
        ext v
        by_cases vp : v=p
        · subst v
          simp [pa]; exact Or.inl pa
        by_cases vq : v=q
        · subst v
          simp [qa]
        simp [R,vp,vq,eqI,or_comm,or_left_comm,or_assoc]
      exact ⟨u,ua,eq ▸ step₅⟩
    have one : F.card=1 := by
      have n := card_pos.mpr ⟨p,pf⟩
      omega
    change (A.filter (fun x=>G.Adj x i)).card=1 at one
    have edge' := edge one
    let R := A.erase p
    have pR : p∉R := fun h=>(mem_erase.mp h).1 rfl
    have sub : R⊆A := erase_subset _ _
    have m : 0<R.card := by
      change 0<(A.erase p).card
      rw [card_erase_of_mem pa,a4]
      decide
    obtain ⟨r,rR⟩ := card_pos.mp m
    have cr : CompleteOn G R := fun z zr w wr zw=>acl z (sub zr) w (sub wr) zw
    obtain ⟨u,w,wp,ws⟩ := rooted_path_in_clique R cr rR
    have path : RouteOn G R u r := (show RouteOn G R r u from ⟨w,wp,ws⟩).reverse
    have ua : u∈A := sub ((ws u).mp w.end_mem_support)
    have st₁ := path.suffix (kAdj r (sub rR)) (fun h=>ka (sub h))
    have st₂ := st₁.suffix (kAdj p pa).symm (by
      have pk : p≠k := fun h=>ka (h ▸ pa)
      simp [pk,pR])
    have st₃ := st₂.suffix pi (by
      have ip : i≠p := fun h=>ia (h.symm ▸ pa)
      have ir : i∉R := fun h=>ia (sub h)
      simp [ip,ik,ir])
    have st₄ := st₃.suffix edge' (by
      have jp : j≠p := fun h=>ja (h.symm ▸ pa)
      have jr : j∉R := fun h=>ja (sub h)
      simp [ij.symm,jp,jk,jr])
    have eq : insert j (insert i (insert p (insert k R)))=A∪I := by
      ext v
      by_cases vp : v=p
      · subst v
        simp [pa]; exact Or.inl pa
      simp [R,vp,eqI,or_comm,or_left_comm,or_assoc]
    exact ⟨u,ua,eq ▸ st₄⟩
  obtain ⟨u,ua,path⟩ := make
  obtain ⟨v,q,qp,qs⟩ := rooted_path_in_clique B bcl yB
  have tail : RouteOn G B y v := ⟨q,qp,qs⟩
  have aB : Disjoint A B := disjoint_left.mpr
    (fun w wa wb=>not_common far (mem_filter.mp wa).2 (mem_filter.mp wb).2)
  have iB : Disjoint I B := disjoint_left.mpr
    (fun w wi wb=>(mem_filter.mp wi).2.2 (mem_filter.mp wb).2)
  have eq : (A∪I)∪B=S.L := by
    rw [union_right_comm]
    exact left_port_partition S far
  exact ⟨u,v,(mem_filter.mp ua).2,eq ▸ path.join tail (disjoint_union_left.mpr ⟨aB,iB⟩) jy⟩

#print axioms four_a_no_bridge_three_inner_free
end Graffiti189LongestPath.CrossSaturation.Split.Five
