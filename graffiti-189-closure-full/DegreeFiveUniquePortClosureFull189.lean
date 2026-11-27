import DegreeFiveUniquePortHighShore189
import DegreeFiveUniquePortLowCommon189
import DegreeFiveFourPort189
import DegreeFiveUniquePortClosureTest189
import DegreeFiveActualCut189
import TerminalOreClosure189
import TerminalOutlier189

namespace Graffiti189LongestPath.CrossSaturation.Split.Five
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private left_boundary from AdjacentCut189
open private d2 from CrossSaturation189
open private lift_side_path from DegreeFiveSmallSides189
open private inside_at_least_four_at_exclusive_high from DegreeFiveUniquePortHighShore189
open private neighbor_in_connected_shore from DegreeFiveUniquePortLowCommon189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} (S : Split G a b)
set_option linter.unusedSectionVars false

private theorem low_shore_has_five
    {z : V} (_zl : z∈S.L) (high : ∀ v∈S.L,v≠z → 5≤G.degree v)
    (none : ∀ v∈S.L,¬(G.Adj a v ∧ G.Adj b v)) :
    5≤S.L.card := by
  classical
  obtain ⟨u,ul,au⟩ := S.leftA
  obtain ⟨v,vl,bv⟩ := S.leftB
  have uv : u≠v := fun e=>none u ul ⟨au,e.symm ▸ bv⟩
  have existsHigh : ∃ w∈S.L,w≠z := by
    by_cases h : u=z
    · exact ⟨v,vl,fun e=>uv (h.trans e.symm)⟩
    exact ⟨u,ul,h⟩
  obtain ⟨w,wl,wz⟩ := existsHigh
  have base := inside_at_least_four_at_exclusive_high S wl (none w wl) (high w wl wz)
  have sub : inside G S.L w ⊆ S.L.erase w := by
    intro y ym
    obtain ⟨yl,wy⟩ := mem_filter.mp ym
    exact mem_erase.mpr ⟨wy.ne.symm,yl⟩
  have h := card_le_card sub
  rw [card_erase_of_mem wl] at h
  omega

private theorem low_port_has_distinct_opposite_exit
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (small : S.L.card≤6)
    {z : V} (zl : z∈S.L) (az : G.Adj a z)
    (high : ∀ v∈S.L,v≠z → 5≤G.degree v)
    (none : ∀ v∈S.L,¬(G.Adj a v ∧ G.Adj b v)) :
    ∃ u∈S.L,∃ v∈S.L,G.Adj z u ∧ G.Adj b v ∧ u≠v := by
  classical
  apply Classical.byContradiction
  intro no
  obtain ⟨w,wl,bw⟩ := S.leftB
  have wz : w≠z := fun e=>none z zl ⟨az,e ▸ bw⟩
  obtain ⟨u,ul,zu⟩ := neighbor_in_connected_shore S zl wl wz.symm
  have uw : u=w := Classical.byContradiction (fun e=>no ⟨u,ul,w,wl,zu,bw,e⟩)
  have zw : G.Adj z w := uw ▸ zu
  have onlyN (v : V) (vl : v∈S.L) (zv : G.Adj z v) : v=w :=
    Classical.byContradiction (fun e=>no ⟨v,vl,w,wl,zv,bw,e⟩)
  have onlyB (v : V) (vl : v∈S.L) (bv : G.Adj b v) : v=w :=
    Classical.byContradiction (fun e=>no ⟨w,wl,v,vl,zw,bv,Ne.symm e⟩)
  let H := S.L.erase z
  have five := low_shore_has_five S zl high none
  have find_other : ∃ v∈H,v≠w := by
    apply Classical.byContradiction
    intro h
    have sub : H⊆{w} := fun v vm =>mem_singleton.mpr
      (Classical.byContradiction fun ne=>h ⟨v,vm,ne⟩)
    have c := card_le_card sub
    change (S.L.erase z).card≤({w} : Finset V).card at c
    rw [card_erase_of_mem zl,card_singleton] at c
    omega
  have Ncover {v : V} (vh : v∈H) (vw : v≠w) :
      inside G S.L v⊆H.erase v := by
    intro k km
    obtain ⟨kl,vk⟩ := mem_filter.mp km
    have kz : k≠z := fun e=>vw (onlyN v (mem_erase.mp vh).2 (e ▸ vk.symm))
    exact mem_erase.mpr ⟨vk.ne.symm,mem_erase.mpr ⟨kz,kl⟩⟩
  obtain ⟨v,vh,vw⟩ := find_other
  have vL := (mem_erase.mp vh).2
  have vhigh := high v vL (mem_erase.mp vh).1
  have vi := inside_at_least_four_at_exclusive_high S vL (none v vL) vhigh
  have k := card_le_card (Ncover vh vw)
  rw [card_erase_of_mem vh] at k
  have Hc : H.card=S.L.card-1 := card_erase_of_mem zl
  have six : S.L.card=6 := by omega
  have wAll (t : V) (tl : t∈S.L) (tw : t≠w) : G.Adj w t := by
    by_cases tz : t=z
    · exact tz.symm ▸ zw.symm
    have th : t∈H := mem_erase.mpr ⟨tz,tl⟩
    have bound := inside_at_least_four_at_exclusive_high S tl (none t tl) (high t tl tz)
    have cap : (H.erase t).card≤(inside G S.L t).card := by
      rw [card_erase_of_mem th]
      omega
    have eq := eq_of_subset_of_card_le (Ncover th tw) cap
    have wm : w∈H.erase t := mem_erase.mpr ⟨tw.symm,mem_erase.mpr ⟨wz,wl⟩⟩
    exact ((mem_filter.mp (eq.symm ▸ wm)).2).symm
  have Ab : a∈DistanceTwo G b := by
    have ba : G.dist b a=2 := by rwa [SimpleGraph.dist_comm]
    simp [DistanceTwo,ba]
  have sub : insert a (S.L.erase w)⊆DistanceTwo G b := by
    intro q qm
    rcases mem_insert.mp qm with rfl|qr
    · exact Ab
    obtain ⟨qw,ql⟩ := mem_erase.mp qr
    have ne : b≠q := fun e=>S.leftOff.2 (e.symm ▸ ql)
    exact d2 hc ne (fun e=>qw (onlyB q ql e)) bw (wAll q ql qw)
  have c := card_le_card sub
  rw [card_insert_of_not_mem (fun h=>S.leftOff.1 (mem_erase.mp h).2),
    card_erase_of_mem wl,six] at c
  have budget := distanceTwo_le_of_even 5 b (even b)
  omega

theorem terminal_route_of_low_exclusive_shore (hc : G.Connected)
    (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ C : Finset V,C.card<2 → (G.induce ((↑C : Set V)ᶜ)).Connected)
    (small : S.L.card≤6) (ports : 3≤(S.L.filter (fun x=>G.Adj a x ∨ G.Adj b x)).card)
    {z : V} (zl : z∈S.L)
    (high : ∀ v∈S.L,v≠z → 5≤G.degree v)
    (none : ∀ v∈S.L,¬(G.Adj a v ∧ G.Adj b v)) :
    ∃ u∈S.L,∃ v∈S.L,G.Adj a u ∧ G.Adj b v ∧ RouteOn G S.L u v := by
  classical
  let U := ↑(↑S.L : Set V)
  let J := G.induce (↑S.L : Set V)
  let zz : U := ⟨z,zl⟩
  let A : Finset U := univ.erase zz
  let K := completeWith J A
  letI : DecidableRel K.Adj := Classical.decRel _
  have size : Fintype.card U≤6 := by
    change Fintype.card {x : V // x∈S.L}≤6
    rwa [Fintype.card_coe]
  have cv (v : U) : v∈A ↔ v≠zz := by simp [A]
  have all (v : U) : v∈insert zz A := by simp [A]
  have four (v : U) (vA : v∈A) : 4≤J.degree v := by
    change 4≤(G.induce (↑S.L : Set V)).degree v
    rw [←inside_card_eq_degree_induce (G:=G) S.L v]
    exact inside_at_least_four_at_exclusive_high S v.property (none _ v.property)
      (high _ v.property (fun e=>(cv v).mp vA (Subtype.ext e)))
  have cap (u v : U) (uv : K.Adj u v) (nE : ¬J.Adj u v) :
      Fintype.card U+1≤J.degree u+J.degree v := by
    change J.Adj u v ∨ (u∈A ∧ v∈A ∧ u≠v) at uv
    obtain ⟨uA,vA,_⟩ := uv.resolve_left nE
    have f := four u uA
    have g := four v vA
    omega
  have trans {u v : U} (route : RouteOn K (insert zz A) u v) : RouteOn G S.L u.val v.val := by
    obtain ⟨p,pp,ps⟩ := route
    obtain ⟨q,qp,qa⟩ := terminal_ore_closure (completeWith_mono J A) cap p pp
      (fun v=>(ps v).mpr (all v))
    exact lift_side_path S.L q qp qa
  have rootZ {u v : V} (uL : u∈S.L) (vL : v∈S.L) (zu : G.Adj z u)
      (uv : u≠v) (vz : v≠z) : RouteOn G S.L z v := by
    let uu : U := ⟨u,uL⟩
    let vv : U := ⟨v,vL⟩
    have uA := (cv uu).mpr (fun e=>zu.ne.symm (congrArg Subtype.val e))
    have vA := (cv vv).mpr (fun e=>vz (congrArg Subtype.val e))
    obtain ⟨p,pp,ps⟩ := path_between_in_clique A (completeWith_of_mem J A)
      uA vA (fun e=>uv (congrArg Subtype.val e))
    have t : RouteOn K A uu vv := ⟨p,pp,ps⟩
    exact trans (t.prefix (completeWith_mono J A (show J.Adj zz uu from zu))
      (fun h=>(cv zz).mp h rfl))
  by_cases az : G.Adj a z
  · obtain ⟨u,uL,v,vL,zu,bv,uv⟩ := low_port_has_distinct_opposite_exit S hc two even small zl az high none
    have vz : v≠z := fun e=>none z zl ⟨az,e ▸ bv⟩
    exact ⟨z,zl,v,vL,az,bv,rootZ uL vL zu uv vz⟩
  by_cases bz : G.Adj b z
  · have two' : G.dist b a=2 := by rwa [SimpleGraph.dist_comm]
    obtain ⟨u,uL,v,vL,zu,av,uv⟩ := low_port_has_distinct_opposite_exit S.flip hc two' even
      small zl bz high (fun v vl h=>none v vl ⟨h.2,h.1⟩)
    have vz : v≠z := fun e=>az (e ▸ av)
    exact ⟨v,vL,z,zl,av,bz,(rootZ uL vL zu uv vz).reverse⟩
  obtain ⟨u,uL,au⟩ := S.leftA
  obtain ⟨v,vL,bv⟩ := S.leftB
  have uz : u≠z := fun e=>az (e ▸ au)
  have vz : v≠z := fun e=>bz (e ▸ bv)
  obtain ⟨w,wL,zw⟩ := neighbor_in_connected_shore S zl uL uz.symm
  have wne : w≠z := zw.ne.symm
  have another : ∃ t∈S.L,t≠w ∧ G.Adj z t := by
    apply Classical.byContradiction
    intro no
    let W := (↑({w} : Finset V) : Set V)ᶜ
    let zr : W := ⟨z,by simpa [W] using wne.symm⟩
    have aw : a≠w := fun e=>S.leftOff.1 (e.symm ▸ wL)
    let ar : W := ⟨a,by simpa [W] using aw⟩
    have step {u v : W} (p : (G.induce W).Walk u v) :
        u=v ∨ ∃ k : W,(G.induce W).Adj u k := by
      cases p with
      | nil => exact .inl rfl
      | @cons _ k _ e p => exact .inr ⟨k,e⟩
    obtain ⟨p⟩ := (conn {w} (by simp)).preconnected zr ar
    have h : zr≠ar := by
      intro eq
      have za : z=a := congrArg Subtype.val eq
      exact S.leftOff.1 (za ▸ zl)
    obtain ⟨k,e⟩ := (step p).resolve_left h
    change G.Adj z k.val at e
    rcases left_boundary S z zl k.val e with h|h|kL
    · exact az (h ▸ e.symm)
    · exact bz (h ▸ e.symm)
    exact no ⟨k.val,kL,(by simpa [W] using k.property),e⟩
  obtain ⟨t,tL,tw,zt⟩ := another
  have perform {p q i j : V} (pL : p∈S.L) (qL : q∈S.L) (iL : i∈S.L) (jL : j∈S.L)
      (ap : G.Adj a p) (bq : G.Adj b q) (zi : G.Adj z i) (zj : G.Adj z j)
      (ip : i≠p) (iq : i≠q) (ij : i≠j) :
      ∃ u∈S.L,∃ v∈S.L,G.Adj a u ∧ G.Adj b v ∧ RouteOn G S.L u v := by
    let pp : U := ⟨p,pL⟩
    let qq : U := ⟨q,qL⟩
    let ii : U := ⟨i,iL⟩
    let jj : U := ⟨j,jL⟩
    have pA := (cv pp).mpr (fun e=>az ((show p=z from congrArg Subtype.val e) ▸ ap))
    have qA := (cv qq).mpr (fun e=>bz ((show q=z from congrArg Subtype.val e) ▸ bq))
    have iA := (cv ii).mpr (fun e=>zi.ne.symm (congrArg Subtype.val e))
    have jA := (cv jj).mpr (fun e=>zj.ne.symm (congrArg Subtype.val e))
    have pq : p≠q := fun e=>none p pL ⟨ap,e.symm ▸ bq⟩
    have path := terminal_path_in_clique_with_outlier (completeWith_of_mem J A)
      pA qA iA jA (fun e=>(cv zz).mp e rfl)
      (fun e=>pq (congrArg Subtype.val e)) (fun e=>ip (congrArg Subtype.val e))
      (fun e=>iq (congrArg Subtype.val e)) (fun e=>ij (congrArg Subtype.val e))
      (completeWith_mono J A (show J.Adj zz ii from zi))
      (completeWith_mono J A (show J.Adj zz jj from zj))
    exact ⟨p,pL,q,qL,ap,bq,trans path⟩
  by_cases wu : w=u ∨ w=v
  · by_cases tu : t=u ∨ t=v
    · let P := S.L.filter (fun x=>G.Adj a x ∨ G.Adj b x)
      have extra : ∃ i∈P,i≠u ∧ i≠v := by
        apply Classical.byContradiction
        intro no
        have sub : P⊆({u,v} : Finset V) := by
          intro i im
          by_cases iu : i=u
          · simp [iu]
          by_cases iv : i=v
          · simp [iv]
          exact (no ⟨i,im,iu,iv⟩).elim
        have cap := (card_le_card sub).trans (card_insert_le u ({v} : Finset V))
        simp only [card_singleton] at cap
        change 3≤P.card at ports
        omega
      obtain ⟨i,iP,iu,iv⟩ := extra
      obtain ⟨iL,ai|bi⟩ := mem_filter.mp iP
      · rcases wu with rfl|rfl
        · have vt : t=v := tu.resolve_left tw
          subst t
          exact perform iL vL uL vL ai bv zw zt iu.symm tw.symm tw.symm
        have ut : t=u := tu.resolve_right tw
        subst t
        exact perform iL vL uL vL ai bv zt zw iu.symm tw tw
      rcases wu with rfl|rfl
      · have vt : t=v := tu.resolve_left tw
        subst t
        exact perform uL iL vL uL au bi zt zw tw iv.symm tw
      have ut : t=u := tu.resolve_right tw
      subst t
      exact perform uL iL vL uL au bi zw zt tw.symm iv.symm tw.symm
    have h : t≠u ∧ t≠v := ⟨fun e=>tu (.inl e),fun e=>tu (.inr e)⟩
    exact perform uL vL tL wL au bv zt zw h.1 h.2 tw
  exact perform uL vL wL tL au bv zw zt (fun e=>wu (.inl e)) (fun e=>wu (.inr e)) tw.symm

theorem traceable_unique_common_test_with_low_on_other_shore (hc : G.Connected)
    (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (rightConn : (G.induce (↑S.R : Set V)).Connected)
    (rightA : ∃ u∈S.R,G.Adj a u) (rightB : ∃ u∈S.R,G.Adj b u)
    {x : V} (xL : x∈S.L) (ax : G.Adj a x) (bx : G.Adj b x)
    (one : (CommonPorts G a b).card=1)
    (test : Fintype.card V-2≤G.degree a+G.degree b)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    {low : V} (lowR : low∈S.R)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (below : ¬5≤G.degree low) :
    ∃ u v : V,∃ p : G.Walk u v,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  let T := switch S rightConn rightA rightB
  have n15 := order_le_fifteen_of_unique_common_closure_test S hc two even
    rightConn rightA rightB xL ax bx one test
  have maxInner := (degree_sum_threshold_iff_at_unique_common two one).mp test
  have unique {z : V} (az : G.Adj a z) (bz : G.Adj b z) : z=x := by
    have xm : x∈CommonPorts G a b :=
      mem_inter.mpr ⟨(mem_neighborFinset G a x).mpr ax,(mem_neighborFinset G b x).mpr bx⟩
    have zm : z∈CommonPorts G a b :=
      mem_inter.mpr ⟨(mem_neighborFinset G a z).mpr az,(mem_neighborFinset G b z).mpr bz⟩
    exact card_le_one.mp one.le z zm x xm
  have none {z : V} (zr : z∈S.R) : ¬(G.Adj a z ∧ G.Adj b z) := by
    intro h
    exact disjoint_left.mp S.dis xL (unique h.1 h.2 ▸ zr)
  have highL (v : V) (vL : v∈S.L) : 5≤G.degree v :=
    (degree v low (fun e=>disjoint_left.mp S.dis vL (e.symm ▸ lowR))).resolve_right below
  have highR (v : V) (_ : v∈S.R) (vl : v≠low) : 5≤G.degree v :=
    (degree v low vl).resolve_right below
  have r5 : 5≤S.R.card :=
    low_shore_has_five T lowR highR (fun _ zR=>none zR)
  have sizeL : S.L.card≤8 := by
    have ab : a≠b := by intro e; rw [e,SimpleGraph.dist_self] at two; omega
    have aa : a∉S.L∪S.R := by simp [S.leftOff.1,S.rightOff.1]
    have bb : b∉S.L∪S.R := by simp [S.leftOff.2,S.rightOff.2]
    have nb : a∉insert b (S.L∪S.R) := by simp [ab,aa]
    have c := card_le_univ (insert a (insert b (S.L∪S.R)))
    rw [card_insert_of_not_mem nb,card_insert_of_not_mem bb,card_union_of_disjoint S.dis] at c
    omega
  have sizeR : S.R.card≤6 ∧ 3≤S.foreignPorts.card := by
    have fl : S.foreignPorts⊆DistanceTwo G x := by
      intro z zp
      obtain ⟨zr,az|bz⟩ := mem_filter.mp zp
      all_goals
        have ne : x≠z := fun e=>disjoint_left.mp S.dis xL (e.symm ▸ zr)
        have no := S.cross x xL z zr
      · exact d2 hc ne no ax.symm az
      exact d2 hc ne no bx.symm bz
    have fc := (card_le_card fl).trans (distanceTwo_le_of_even 5 x (even x))
    have sub : S.R ⊆ S.foreignPorts∪Nonports G a b := by
      intro z zr
      by_cases h : G.Adj a z ∨ G.Adj b z
      · exact mem_union_left _ (mem_filter.mpr ⟨zr,h⟩)
      apply mem_union_right
      apply mem_sdiff.mpr
      refine ⟨mem_erase.mpr ⟨fun e=>S.rightOff.2 (e ▸ zr),
        mem_erase.mpr ⟨fun e=>S.rightOff.1 (e ▸ zr),mem_univ _⟩⟩,?_⟩
      intro nm
      exact h ((mem_union.mp nm).imp ((mem_neighborFinset G a z).mp) ((mem_neighborFinset G b z).mp))
    have c := (card_le_card sub).trans (card_union_le S.foreignPorts (Nonports G a b))
    exact ⟨by omega,by omega⟩
  obtain ⟨u,ur,v,vr,au,bv,path⟩ := terminal_route_of_low_exclusive_shore T hc two even conn
    sizeR.1 sizeR.2 lowR highR (fun z zr=>none zr)
  have m : RouteOn G (insert a (insert b S.R)) a b := by
    have r := path.suffix bv.symm S.rightOff.2
    exact r.prefix au (by simp [T.leftOff.1,show a≠b by
      intro e; rw [e,SimpleGraph.dist_self] at two; omega])
  obtain ⟨w,l⟩ := root_any_vertex_of_high_shore_with_one_common S sizeL
    highL xL (fun z _ az bz=>unique az bz) xL
  have all := m.reverse.join l
    (by apply disjoint_left.mpr; intro z zm zl; simp only [mem_insert] at zm;
        rcases zm with rfl|rfl|zr
        · exact S.leftOff.1 zl
        · exact S.leftOff.2 zl
        exact disjoint_left.mp S.dis zl zr)
    ax
  obtain ⟨p,pp,ps⟩ := all
  refine ⟨b,w,p,pp,fun z=>(ps z).mpr ?_⟩
  rcases S.cover z with rfl|rfl|zl|zr
  · simp
  · simp
  · exact mem_union_right _ zl
  exact mem_union_left _ (mem_insert_of_mem (mem_insert_of_mem zr))

#print axioms terminal_route_of_low_exclusive_shore
#print axioms traceable_unique_common_test_with_low_on_other_shore
end Graffiti189LongestPath.CrossSaturation.Split.Five

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset
open private CutGraph Shore mem_shore shore_off shore_disjoint shore_closed shore_connected
  shore_hit_a shore_hit_b from DegreeFiveActualCut189
open private two_walk_middle from DistanceTwoCut189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

theorem traceable_of_actual_unique_common_closure_test {a b : V}
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (comp : Nat.card (CutGraph (G:=G) a b).ConnectedComponent=2)
    (one : (CommonPorts G a b).card=1)
    (test : Fintype.card V-2≤G.degree a+G.degree b)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v) :
    ∃ u v : V,∃ p : G.Walk u v,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  let J := CutGraph (G:=G) a b
  haveI : Finite J.ConnectedComponent := Finite.of_surjective J.connectedComponentMk (fun c=>c.exists_rep)
  letI : Fintype J.ConnectedComponent := Fintype.ofFinite _
  change Nat.card J.ConnectedComponent=2 at comp
  rw [Nat.card_eq_fintype_card] at comp
  have ab : a≠b := by intro eq; rw [eq,SimpleGraph.dist_self] at two; omega
  obtain ⟨p,pl⟩ := hc.exists_walk_length_eq_dist a b
  obtain ⟨x,ax,xb⟩ := two_walk_middle p (pl.trans two)
  let C := J.connectedComponentMk ⟨x,ax.ne.symm,xb.ne⟩
  have xC : x∈Shore C := mem_shore.mpr ⟨⟨ax.ne.symm,xb.ne⟩,rfl⟩
  let T := (univ : Finset J.ConnectedComponent).erase C
  have tc : T.card=1 := by
    dsimp [T]
    rw [card_erase_of_mem (mem_univ _),card_univ,comp]
  obtain ⟨D,hD⟩ := card_eq_one.mp tc
  have dt : D∈T := by simp [hD]
  have DC : D≠C := (mem_erase.mp dt).1
  have dis : Disjoint (Shore C) (Shore D) := shore_disjoint DC.symm
  have cover (u : V) : u=a ∨ u=b ∨ u∈Shore C ∨ u∈Shore D := by
    by_cases ua : u=a
    · exact .inl ua
    by_cases ub : u=b
    · exact .inr (.inl ub)
    let E := J.connectedComponentMk ⟨u,ua,ub⟩
    have eu : u∈Shore E := mem_shore.mpr ⟨⟨ua,ub⟩,rfl⟩
    by_cases ec : E=C
    · exact .inr (.inr (.inl (ec ▸ eu)))
    have et : E∈T := mem_erase.mpr ⟨ec,mem_univ _⟩
    rw [hD] at et
    exact .inr (.inr (.inr (mem_singleton.mp et ▸ eu)))
  have cross (u : V) (uC : u∈Shore C) (v : V) (vD : v∈Shore D) : ¬G.Adj u v := by
    intro uv
    rcases shore_closed C u uC v uv with rfl|rfl|vC
    · exact (shore_off D).1 vD
    · exact (shore_off D).2 vD
    exact disjoint_left.mp dis vC vD
  let S : Split G a b :=
    ⟨Shore C,Shore D,dis,shore_off C,shore_off D,shore_connected C,cross,
      shore_hit_a ab conn C,shore_hit_b ab conn C,cover⟩
  have rc := shore_connected D
  have ra := shore_hit_a ab conn D
  have rb := shore_hit_b ab conn D
  by_cases hh : ∀ z,z∈S.L ∨ z∈S.R → 5≤G.degree z
  · exact Split.Five.traceable_unique_common_test_of_high_shores S hc two even rc ra rb
      xC ax xb.symm one test hh
  have bad : ∃ z,(z∈S.L ∨ z∈S.R) ∧ ¬5≤G.degree z := by
    push_neg at hh
    simpa only [not_le] using hh
  obtain ⟨low,hl,below⟩ := bad
  rcases hl with l|r
  · exact Split.Five.traceable_unique_common_test_with_low_on_common_shore S hc two even rc ra rb
      xC ax xb.symm one test conn l degree below
  exact Split.Five.traceable_unique_common_test_with_low_on_other_shore S hc two even rc ra rb
    xC ax xb.symm one test conn r degree below

#print axioms traceable_of_actual_unique_common_closure_test
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
