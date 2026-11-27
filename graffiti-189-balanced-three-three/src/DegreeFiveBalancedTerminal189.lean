import DegreeFiveRouteBasic189
import DegreeFiveUniquePortHighShore189
import DegreeFiveUniquePortLowCommon189
import TerminalOreClosure189
import TerminalOutlier189

namespace Graffiti189LongestPath.CrossSaturation.Split.Five
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private left_boundary from AdjacentCut189
open private lift_side_path from DegreeFiveSmallSides189
open private inside_at_least_four_at_exclusive_high from DegreeFiveUniquePortHighShore189
open private neighbor_in_connected_shore from DegreeFiveUniquePortLowCommon189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} (S : Split G a b)
set_option linter.unusedSectionVars false

theorem terminal_route_of_small_balanced_shore_one_low 
    (conn : ∀ C : Finset V,C.card<2 → (G.induce ((↑C : Set V)ᶜ)).Connected)
    (small : S.L.card≤7) (pA : 2≤(S.L.filter (G.Adj a)).card)
    (pB : 2≤(S.L.filter (G.Adj b)).card)
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
  have size : Fintype.card U≤7 := by
    change Fintype.card {x : V // x∈S.L}≤7
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
  have pick (c : V) (two : 2≤(S.L.filter (G.Adj c)).card) (w : V) :
      ∃ v∈S.L,G.Adj c v ∧ w≠v := by
    obtain ⟨p,pp,q,qp,pq⟩ := one_lt_card.mp (show 1<(S.L.filter (G.Adj c)).card by omega)
    obtain ⟨pl,cp⟩ := mem_filter.mp pp
    obtain ⟨ql,cq⟩ := mem_filter.mp qp
    by_cases wp : w=p
    · exact ⟨q,ql,cq,fun eq=>pq (wp.symm.trans eq)⟩
    exact ⟨p,pl,cp,wp⟩
  by_cases az : G.Adj a z
  · obtain ⟨k,kl,bk⟩ := S.leftB
    have zk : z≠k := fun e=>none z zl ⟨az,e.symm ▸ bk⟩
    obtain ⟨u,uL,zu⟩ := neighbor_in_connected_shore S zl kl zk
    obtain ⟨v,vL,bv,uv⟩ := pick b pB u
    have vz : v≠z := fun e=>none z zl ⟨az,e ▸ bv⟩
    exact ⟨z,zl,v,vL,az,bv,rootZ uL vL zu uv vz⟩
  by_cases bz : G.Adj b z
  · obtain ⟨k,kl,ak⟩ := S.leftA
    have zk : z≠k := fun e=>az (e.symm ▸ ak)
    obtain ⟨u,uL,zu⟩ := neighbor_in_connected_shore S zl kl zk
    obtain ⟨v,vL,av,uv⟩ := pick a pA u
    have vz : v≠z := fun e=>az (e ▸ av)
    exact ⟨v,vL,z,zl,av,bz,(rootZ uL vL zu uv vz).reverse⟩
  have ports : 3≤(S.L.filter (fun x=>G.Adj a x ∨ G.Adj b x)).card := by
    let PA := S.L.filter (G.Adj a)
    let PB := S.L.filter (G.Adj b)
    have dis : Disjoint PA PB := by
      apply disjoint_left.mpr
      intro q qa qb
      exact none q (mem_filter.mp qa).1 ⟨(mem_filter.mp qa).2,(mem_filter.mp qb).2⟩
    have e : PA∪PB=S.L.filter (fun x=>G.Adj a x ∨ G.Adj b x) := by
      ext q
      simp [PA,PB,and_or_left]
    have h := congrArg Finset.card e
    rw [card_union_of_disjoint dis] at h
    change 2≤PA.card at pA
    change 2≤PB.card at pB
    omega
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


theorem terminal_route_of_small_balanced_exclusive_shore
    (conn : ∀ C : Finset V,C.card<2 → (G.induce ((↑C : Set V)ᶜ)).Connected)
    (small : S.L.card≤7) (pA : 2≤(S.L.filter (G.Adj a)).card)
    (pB : 2≤(S.L.filter (G.Adj b)).card)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (none : ∀ v∈S.L,¬(G.Adj a v ∧ G.Adj b v)) :
    ∃ u∈S.L,∃ v∈S.L,G.Adj a u ∧ G.Adj b v ∧ RouteOn G S.L u v := by
  classical
  by_cases low : ∃ z∈S.L,¬5≤G.degree z
  · obtain ⟨z,zL,zlo⟩ := low
    exact terminal_route_of_small_balanced_shore_one_low S conn small pA pB zL
      (fun v _ vz=>(degree v z vz).resolve_right zlo) none
  obtain ⟨u,ul,au⟩ := S.leftA
  obtain ⟨v,vl,bv⟩ := S.leftB
  have uv : u≠v := fun e=>none u ul ⟨au,e.symm ▸ bv⟩
  let U := ↑(↑S.L : Set V)
  let J := G.induce (↑S.L : Set V)
  let uu : U := ⟨u,ul⟩
  let vv : U := ⟨v,vl⟩
  have cnt : Fintype.card U≤7 := by
    change Fintype.card {w : V // w∈S.L}≤7
    rwa [Fintype.card_coe]
  have deg (w : U) : 4≤J.degree w := by
    change 4≤(G.induce (↑S.L : Set V)).degree w
    rw [←inside_card_eq_degree_induce (G:=G) S.L w]
    exact inside_at_least_four_at_exclusive_high S w.property (none w.val w.property)
      (Classical.byContradiction (fun e=>low ⟨w.val,w.property,e⟩))
  obtain ⟨p,pp,ps⟩ := hamilton_connected_of_ore (G:=J) (by
    intro x y _ _
    change Fintype.card U+1≤J.degree x+J.degree y
    have a := deg x
    have b := deg y
    omega) (show uu≠vv from fun e=>uv (congrArg Subtype.val e))
  exact ⟨u,ul,v,vl,au,bv,lift_side_path S.L p pp ps⟩

#print axioms terminal_route_of_small_balanced_exclusive_shore
end Graffiti189LongestPath.CrossSaturation.Split.Five
