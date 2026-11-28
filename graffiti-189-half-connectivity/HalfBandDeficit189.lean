import Mathlib.Tactic.FinCases
import ThreeFifthsDeficit189
import TwoSmallNormalized189
import ThreeNormalized189
import LargeRobustShore189
import SplitShoreThree189
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack Graffiti189LongestPath.PinRun
open Graffiti189LongestPath.DeficitActive Graffiti189LongestPath.ScaledActive Graffiti189LongestPath.DeficitLongest
open Graffiti189LongestPath.QuadraticShore
open Graffiti189LongestPath.GeneralGapMidpoint Graffiti189LongestPath.Normalize Graffiti189LongestPath.DeficitThirdShell
open Graffiti189LongestPath.StandaloneShellQuadratic Graffiti189LongestPath.RadialOrder
open Graffiti189LongestPath.GreedyTerminal Graffiti189LongestPath.FanWeighted Graffiti189LongestPath.MengerRoutable
open Graffiti189LongestPath.ShoreSplit Graffiti189LongestPath.ExplicitShoreCycle
open Graffiti189LongestPath.SplitShellCharge Graffiti189LongestPath.StarCycleClosure Graffiti189LongestPath.PosaOneLow Graffiti189LongestPath.ActiveStarHeight
open private Graffiti189LongestPath.Rigidity.mem_omittedStar Graffiti189LongestPath.Rigidity.mem_external from Rigidity189
open private Graffiti189LongestPath.pin_data from SmallSeparator189
open private Graffiti189LongestPath.OneSlack.boundary_except_pins_two Graffiti189LongestPath.OneSlack.card_pinVertices
  Graffiti189LongestPath.OneSlack.pin_vertices_subset_boundary Graffiti189LongestPath.OneSlack.first_eq_if_no_pair
  Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem from OneSlack189
open private Graffiti189LongestPath.PortReachCount.side_ports_bound from PortReachCount189
set_option warningAsError true
set_option maxHeartbeats 7000000
namespace Graffiti189LongestPath.HalfBandDeficit
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- #189 in an explicit quadratic connectivity range, without needing
2-connectivity of the omitted shore.
No normalized attachment or separator geometry is assumed. -/
theorem traceable_of_half_gap (hc : G.Connected) (k sl : Nat) (large : 1000000≤k) (ratio : sl+100≤k) (positive : 2*k≤3*sl)
    (cap : ∀ v,(EvenFrom G v).card≤k+sl+1)
    (conn : ∀ S : Finset V,S.card<k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (deg : ∀ u v : V,u≠v → k+sl≤G.degree u ∨ k+sl≤G.degree v) :
    ∃ (u v : V) (q : G.Walk u v),q.IsPath ∧ ∀ z,z∈q.support := by
  classical
  apply Classical.byContradiction
  intro fail
  obtain ⟨a,b,p,hmin⟩ := exists_edgeMinAvoid hc (k+sl) deg
  have hp := hmin.1.1
  have no : ∃ x,x∉p.support := Classical.byContradiction (fun h =>
    fail ⟨a,b,p,hp.1,fun z => Classical.byContradiction (fun e => h ⟨z,e⟩)⟩)
  obtain ⟨x,hx,xh,i,hi⟩ := scaled_deficit_has_high_active hc k sl (by omega) (by omega) cap conn deg hp no
  let d := k+sl
  let A := OmittedStar p x
  let B := External G A
  let H := Shell G x 3
  let W := Shell G x 4
  let U := (univ:Finset V)\(A∪B)
  have cap₂ (v : V) : (DistanceTwo G v).card≤d := distanceTwo_le_of_even d v (cap v)
  have pack := high_omitted_pin_budget hc d k cap conn hp hx (Graffiti189LongestPath.pin_data hi).2 xh
  have p3 : (Pins p x).card≤sl := by dsimp [d] at pack; omega
  have w3 : W.card≤sl := by change k+(Pins p x).card+W.card≤d at pack; dsimp [d] at pack; omega
  have rad (z : V) : G.dist x z≤4 := by
    by_contra! far
    have c := shell_card_of_far hc k conn (x:=x) (y:=z) (i:=4) (by decide) (by omega)
    change k≤W.card at c
    omega
  let loss := sl+1-(Pins p x).card
  have height : k+loss≤A.card := by
    have e := star_card_degree_and_pins hp hx
    change A.card+(Pins p x).card=G.degree x+1 at e
    dsimp [loss,d] at *
    omega
  have first := GapOne.first_pins_at_least_pins_sub_one hc d cap deg hmin.1 hx xh (by dsimp [d]; omega)
  have bp : B.card+(Pins p x).card≤d+1 := by
    have f := boundary_flank_count hc hp hx
    rw [flank_count_exact hp hx] at f
    have c := cap₂ x
    change B.card+((Pins p x).card+(FirstPins p x).card)≤
      (DistanceTwo G x).card+(Pins p x).card at f
    omega
  have bk : B.card≤k+loss := by
    dsimp [d] at bp
    dsimp [loss]
    omega
  have floor (z : V) : 2≤G.degree z := by
    have ne : a≠x := fun e => hx (e ▸ p.start_mem_support)
    have n := enough_vertices_of_degree (k+sl) deg ne
    have kdeg := degree_floor_when_enough_vertices k conn (by omega) z
    omega
  have largeP := longest_length_ge_twice_of_not_traceable hc d (by omega) floor deg fail hp
  have far : k≤U.card := by
    have cover : p.support.toFinset⊆B∪U := by
      intro z hz
      by_cases zb : z∈B
      · exact mem_union.mpr (Or.inl zb)
      have za : z∉A := fun e => (Graffiti189LongestPath.Rigidity.mem_omittedStar.mp e).1 (List.mem_toFinset.mp hz)
      exact mem_union.mpr (Or.inr (mem_sdiff.mpr ⟨mem_univ z,fun e => (mem_union.mp e).elim za zb⟩))
    have h := (card_le_card cover).trans (card_union_le B U)
    rw [List.toFinset_card_of_nodup hp.1.support_nodup,length_support] at h
    dsimp [d] at largeP
    omega
  let T := A.erase x
  let J := G.induce (T:Set V)
  let L := T.filter (fun v => G.degree v<d)
  let m := (k-2)/2
  have xA : x∈A := Graffiti189LongestPath.Rigidity.mem_omittedStar.mpr ⟨hx,Or.inl rfl⟩
  have L1 : L.card≤1 := by
    apply Nat.le_of_not_gt
    intro e
    obtain ⟨u,uu,v,vv,ne⟩ := one_lt_card.mp (show 1<L.card from e)
    have e₁ := (mem_filter.mp uu).2
    have e₂ := (mem_filter.mp vv).2
    exact (deg u v ne).elim (Nat.not_le_of_lt e₁) (Nat.not_le_of_lt e₂)
  have highJ (v : V) (vt : v∈T) (vl : v∉L) : m≤(T.filter (G.Adj v)).card := by
    let v' : ↥(T:Set V) := ⟨v,vt⟩
    have vh : d≤G.degree v := Nat.le_of_not_gt (fun h => vl (mem_filter.mpr ⟨vt,h⟩))
    have b := (quadratic_root_deleted_degrees hc k sl loss cap conn hp hx bk far v').2 vh
    change A.card≤2*J.degree v'+loss+3 at b
    have id := induced_degree_count (G:=G) T v'
    change (T.filter (G.Adj v)).card=J.degree v' at id
    dsimp [m]
    omega
  have floorJ (v : ↥(T:Set V)) : 2≤J.degree v := by
    have b := (quadratic_root_deleted_degrees hc k sl loss cap conn hp hx bk far v).1
    change A.card≤2*J.degree v+sl+loss+3 at b
    omega
  have lowJ (v : V) (vt : v∈T) (_vl : v∈L) : 1≤(T.filter (G.Adj v)).card := by
    let v' : ↥(T:Set V) := ⟨v,vt⟩
    have b := floorJ v'
    have id := induced_degree_count (G:=G) T v'
    change (T.filter (G.Adj v)).card=J.degree v' at id
    omega
  have highDegree (v : ↥(T:Set V)) (vh : d≤G.degree v.val) : m≤J.degree v := by
    have u := highJ v.val v.property (fun e => (Nat.not_lt_of_ge vh) (mem_filter.mp e).2)
    have eq := induced_degree_count (G:=G) T v
    change (T.filter (G.Adj v.val)).card=J.degree v at eq
    omega
  have root (v : V) (va : v∈A) (ne : v≠x) : G.Adj x v :=
    ((Graffiti189LongestPath.Rigidity.mem_omittedStar.mp va).2).resolve_left ne
  have routes := one_low_universal_uniform_routes A L x xA root L1 m highJ lowJ
  have ao : ∀ v∈A,v∉p.support := fun _ va =>
    (Graffiti189LongestPath.Rigidity.mem_omittedStar.mp va).1
  obtain ⟨F⟩ := hooks_of_small_deletion_connectivity A k hp ao (by omega) (support_large k conn hp hx) conn
  have bound := weighted_hooked_lower k (by omega) hp (m+1) A ao (by omega) routes F
  have low : A.card+k+(k+1)*(m+1)≤Fintype.card V := by omega
  have order := order_le_radius_four_layers hc x rad
  change Fintype.card V≤G.degree x+1+(DistanceTwo G x).card+H.card+W.card at order
  have base : Fintype.card V≤A.card+k+2*sl+H.card := by
    have d₂ := cap₂ x
    have degX := star_card_degree_and_pins hp hx
    change A.card+(Pins p x).card=G.degree x+1 at degX
    change k+(Pins p x).card+W.card≤d at pack
    dsimp [d] at d₂ pack
    omega
  by_cases robust : ∀ S : Finset ↥(T:Set V), S.card<2 →
      (J.induce ((↑S:Set _)ᶜ)).Connected
  · have vc : Fintype.card ↥(T:Set V)=A.card-1 := by
      change Fintype.card ↥T=A.card-1
      exact (Fintype.card_coe T).trans (card_erase_of_mem xA)
    have md : 2≤m := by dsimp [m]; omega
    have pair (u v : ↥(T:Set V)) (ne : u≠v) : m≤J.degree u ∨ m≤J.degree v :=
      (deg u.val v.val (fun e => ne (Subtype.ext e))).imp (highDegree u) (highDegree v)
    obtain ⟨r,c,cc,cl⟩ := proved_one_low_circumference _ J m md (by omega) robust floorJ pair
    have lim : k-3≤c.length := by
      have bm : 2*m≤A.card-1 := by dsimp [m]; omega
      have bm' : 2*m≤Fintype.card ↥(T:Set V) := by rw [vc]; exact bm
      rw [min_eq_right bm'] at cl
      dsimp [m] at cl
      omega
    have routesLong := routes_of_explicit_root_deleted_cycle hx robust (k-3)
      ⟨r,c,cc,by omega⟩
    have lowLong := weighted_hooked_lower k (by omega) hp (k-3+1) A ao (by omega) routesLong F
    have lowLong' : A.card+k+(k+1)*(k-2)≤Fintype.card V := by
      rw [show k-3+1=k-2 by omega] at lowLong
      omega
    have shell := universal_shell_three_quadratic hc d cap₂ x
    change 4*H.card≤(d+1)*(d+1) at shell
    have small : (d+1)*(d+1)+8*sl<4*((k+1)*(k-2)) := by
      have v : d+1≤2*k-6 := by dsimp [d]; omega
      have sq := Nat.mul_le_mul v v
      have eq : (2*k-6)*(2*k-6)+24*k=4*(k*k)+36 := by
        let t := k-3
        have kt : k=t+3 := by dsimp [t]; omega
        rw [show 2*k-6=2*t by dsimp [t]; omega]
        rw [kt]
        ring
      have ev : (k+1)*(k-2)+k+2=k*k := by
        let t := k-2
        have kt : k=t+2 := by dsimp [t]; omega
        rw [show k-2=t from rfl,kt]
        ring
      omega
    have um : 4*Fintype.card V<4*(A.card+k+(k+1)*(k-2)) := by
      calc
        _ ≤ 4*(A.card+k+2*sl+H.card) := Nat.mul_le_mul_left 4 base
        _ = 4*(A.card+k)+(4*H.card+8*sl) := by ring
        _ ≤ 4*(A.card+k)+((d+1)*(d+1)+8*sl) :=
          Nat.add_le_add_left (Nat.add_le_add_right shell _) _
        _ < 4*(A.card+k)+4*((k+1)*(k-2)) := Nat.add_lt_add_left small _
        _ = _ := by ring
    omega
  obtain ⟨S,sm,failS⟩ : ∃ S : Finset ↥(T:Set V),S.card<2 ∧ ¬(J.induce ((↑S:Set _)ᶜ)).Connected := by
    apply Classical.byContradiction
    intro neg
    apply robust
    intro S sm
    exact Classical.byContradiction (fun bad => neg ⟨S,sm,bad⟩)
  let emb : ↥(T:Set V) ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  let X := insert x (S.map emb)
  have xx : x∈X := mem_insert_self _ _
  have xsub : X⊆A := by
    intro z zz
    rcases mem_insert.mp zz with rfl|zz
    · exact xA
    · obtain ⟨v,_,rfl⟩ := mem_map.mp zz
      exact (mem_erase.mp v.property).2
  have xs : X.card≤2 := by
    have h := card_insert_le x (S.map emb)
    rw [card_map] at h
    change X.card≤S.card+1 at h
    omega
  have iso := erase_root_and_set_iso (G:=G) A x S
  have bad : ¬(G.induce (↑(A\X):Set V)).Connected := fun h => failS (iso.connected_iff.mp h)
  have nAX : (A\X).Nonempty := card_pos.mp (by
    have e := card_sdiff_add_card_eq_card xsub
    omega)
  obtain ⟨C,E,part,ce,no,cn,en,smaller⟩ : ∃ C E : Finset V,
      C∪E=A\X ∧ Disjoint C E ∧ (∀ u∈C,∀ v∈E,¬G.Adj u v) ∧
      C.Nonempty ∧ E.Nonempty ∧ C.card≤E.card := by
    obtain ⟨C,E,part,ce,no,cn,en⟩ := partition_of_not_connected (A\X) nAX bad
    by_cases smaller : C.card≤E.card
    · exact ⟨C,E,part,ce,no,cn,en,smaller⟩
    · exact ⟨E,C,(union_comm E C).trans part,ce.symm,
        fun v ve u uc ed => no u uc v ve ed.symm,en,cn,by omega⟩
  have lc := side_order_at_least_half A C E X x d (k-1) xx xsub xs part ce cn no deg floorJ highDegree
  let P := PinVertices p x
  let ell := sl-(Pins p x).card
  have lossEq : loss=ell+1 := by dsimp [loss,ell]; omega
  have sP (v : V) (vp : v∈P) : v∈p.support := by
    obtain ⟨j,_,rfl⟩ := mem_image.mp vp
    exact p.getVert_mem_support j
  have cX : Disjoint C X := disjoint_left.mpr (fun v vc vx =>
    (mem_sdiff.mp (part ▸ mem_union.mpr (Or.inl vc) : v∈A\X)).2 vx)
  have eX : Disjoint E X := disjoint_left.mpr (fun v ve vx =>
    (mem_sdiff.mp (part ▸ mem_union.mpr (Or.inr ve) : v∈A\X)).2 vx)
  have hpart : A=C∪E∪X := by rw [part]; exact (sdiff_union_of_subset xsub).symm
  have cA : C⊆A := by
    intro v vv
    have vx : v∈A\X := part ▸ mem_union.mpr (Or.inl vv)
    exact (mem_sdiff.mp vx).1
  have eA : E⊆A := by
    intro v vv
    have vx : v∈A\X := part ▸ mem_union.mpr (Or.inr vv)
    exact (mem_sdiff.mp vx).1
  have cx : x∉C := fun xc => disjoint_left.mp cX xc xx
  have ex : x∉E := fun xe => disjoint_left.mp eX xe xx
  have hcard : A.card=C.card+E.card+X.card := by
    have q := congrArg Finset.card hpart
    rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨cX,eX⟩),card_union_of_disjoint ce] at q
    exact q
  have rootNbr : G.neighborFinset x=T∪P := by
    ext z
    rw [G.mem_neighborFinset,mem_union]
    constructor
    · intro adj
      by_cases zp : z∈p.support
      · obtain ⟨j,jp,e⟩ := Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem hp hx zp adj
        exact Or.inr (mem_image.mpr ⟨j,jp,e⟩)
      exact Or.inl (mem_erase.mpr ⟨adj.ne.symm,
        Graffiti189LongestPath.Rigidity.mem_omittedStar.mpr ⟨zp,Or.inr adj⟩⟩)
    · rintro (zt|zp)
      · exact root z (mem_erase.mp zt).2 (mem_erase.mp zt).1
      · obtain ⟨j,jp,rfl⟩ := mem_image.mp zp
        exact (Graffiti189LongestPath.pin_data jp).2
  have removeRoot (R Y : Finset V) (prt : A=R∪Y)
      (dry : Disjoint R Y) (xy : x∈Y) : R∪Y.erase x=T := by
    ext z
    change z∈R∪Y.erase x↔z∈A.erase x
    rw [prt]
    constructor
    · intro h
      rcases mem_union.mp h with hr|hy
      · exact mem_erase.mpr ⟨fun e => disjoint_left.mp dry hr (e.symm ▸ xy),
          mem_union.mpr (Or.inl hr)⟩
      · exact mem_erase.mpr ⟨(mem_erase.mp hy).1,mem_union.mpr (Or.inr (mem_erase.mp hy).2)⟩
    · intro h
      rcases mem_union.mp (mem_erase.mp h).2 with hr|hy
      · exact mem_union.mpr (Or.inl hr)
      · exact mem_union.mpr (Or.inr (mem_erase.mpr ⟨(mem_erase.mp h).1,hy⟩))
  have leafPartition (R Y : Finset V) (prt : A=R∪Y)
      (dry : Disjoint R Y) (xy : x∈Y) : R∪P∪Y.erase x=G.neighborFinset x := by
    rw [rootNbr,←removeRoot R Y prt dry xy]
    ac_rfl
  have boundSide (R Y : Finset V) (rA : R⊆A) (dRY : Disjoint R Y) (xY : x∈Y)
      (small : (Y.erase x).card≤2)
      (nout : ∀ u∈R,∀ v∈A,v∉R → v∉Y → ¬G.Adj u v)
      (v : ↥(R:Set V)) :
      3≤(G.induce (R:Set V)).degree v ∧
      (d≤G.degree v.val →
        A.card≤2*(G.induce (R:Set V)).degree v+loss+3+2*(Y.erase x).card) := by
    have vx : v.val≠x := fun e => disjoint_left.mp dRY v.property (e.symm ▸ xY)
    let u : ↥(T:Set V) := ⟨v.val,mem_erase.mpr ⟨vx,rA v.property⟩⟩
    have y := SplitShoreThree.side_degree_loss A R Y x nout v.val v.property
    have c1 := induced_degree_count (G:=G) T u
    have c2 := induced_degree_count (G:=G) R v
    change (T.filter (G.Adj v.val)).card=J.degree u at c1
    change (T.filter (G.Adj v.val)).card≤(R.filter (G.Adj v.val)).card+(Y.erase x).card at y
    rw [c1,c2] at y
    have f := quadratic_root_deleted_degrees hc k sl loss cap conn hp hx bk far u
    have lo := f.1
    change A.card≤2*J.degree u+sl+loss+3 at lo
    refine ⟨by omega,?_⟩
    intro vh
    have hi := f.2 vh
    change A.card≤2*J.degree u+loss+3 at hi
    omega
  have noutC (u : V) (uc : u∈C) (v : V) (va : v∈A) (vn : v∉C) (vx : v∉X) :
      ¬G.Adj u v := by
    have vcE : v∈C∪E := (mem_union.mp (hpart ▸ va)).resolve_right vx
    exact no u uc v ((mem_union.mp vcE).resolve_left vn)
  have noutE (u : V) (ue : u∈E) (v : V) (va : v∈A) (vn : v∉E) (vx : v∉X) :
      ¬G.Adj u v := by
    have vcE : v∈C∪E := (mem_union.mp (hpart ▸ va)).resolve_right vx
    exact fun ed => no v ((mem_union.mp vcE).resolve_right vn) u ue ed.symm
  have xx1 : (X.erase x).card≤1 := by have a := card_erase_add_one xx; omega
  have cs := boundSide C X cA cX xx (by omega) noutC
  have es := boundSide E X eA eX xx (by omega) noutE
  have sideHiC (v : ↥(C:Set V)) (hv : d≤G.degree v.val) :
      k-5≤2*(G.induce (C:Set V)).degree v := by have sh := (cs v).2 hv; omega
  have sideHiE (v : ↥(E:Set V)) (hv : d≤G.degree v.val) :
      k-5≤2*(G.induce (E:Set V)).degree v := by have sh := (es v).2 hv; omega
  by_cases tiny : E.card≤k-6
  · apply TwoSmallNormalized.small_split_impossible hc k sl large positive (by omega) hp hx first
      cap₂ conn deg (support_large k conn hp hx) C E X (X.erase x) hpart
      (leafPartition (C∪E) X hpart (disjoint_union_left.mpr ⟨cX,eX⟩) xx)
      xx xs xx1 ce cX eX no lc smaller tiny (fun u => (cs u).1) (fun u => (es u).1)
      sideHiC sideHiE (by change k≤A.card; omega)
      (by change d≤A.card+(Pins p x).card; have z := star_card_degree_and_pins hp hx;
          change A.card+(Pins p x).card=G.degree x+1 at z; omega) (by omega) bp base
  by_cases robustE : ∀ S : Finset ↥(E:Set V),S.card<2 →
      ((G.induce (E:Set V)).induce ((↑S:Set _)ᶜ)).Connected
  · have eh (u v : ↥(E:Set V)) (ne : u≠v) :
        A.card≤2*(G.induce (E:Set V)).degree u+loss+5 ∨
        A.card≤2*(G.induce (E:Set V)).degree v+loss+5 :=
      (deg u.val v.val (fun e => ne (Subtype.ext e))).imp
        (fun uhi => by have u := (es u).2 uhi; omega) (fun vhi => by have v := (es v).2 vhi; omega)
    have sh := universal_shell_three_quadratic hc d cap₂ x
    exact LargeRobustShore.robust_large_shore_impossible k sl A.card loss H.card
      (by omega) (by omega) (by dsimp [loss]; omega) height hp hx
      E ex (fun u ue => ao u (eA ue)) (fun u ue => root u (eA ue) (fun e => ex (e ▸ ue)))
      (by omega) (by omega) conn robustE (support_large k conn hp hx) (fun u => (by have e := (es u).1; omega))
      eh base sh
  obtain ⟨D,Q,Y,subY,yc,eqA,dn,qn,cd,cq,dq,ry,nCD,nCQ,nDQ⟩ :=
    SplitShoreThree.split_third_shore_after_one_more_deletion A C E X hpart ce cX eX no
      (by omega) robustE
  have yx : x∈Y := subY xx
  have y3 : Y.card≤3 := by omega
  have y2 : (Y.erase x).card≤2 := by have a := card_erase_add_one yx; omega
  let M (i : Fin 3) := if i=0 then C else if i=1 then D else Q
  let R := univ.biUnion M
  have Rform : R=C∪D∪Q := by
    ext v
    constructor
    · intro h
      obtain ⟨i,_,vv⟩ := mem_biUnion.mp h
      fin_cases i
      · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inl (by simpa [M] using vv))))
      · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inr (by simpa [M] using vv))))
      · exact mem_union.mpr (Or.inr (by simpa [M] using vv))
    · intro h
      rcases mem_union.mp h with h|h
      · rcases mem_union.mp h with h|h
        · exact mem_biUnion.mpr ⟨0,mem_univ _,by simpa [M] using h⟩
        · exact mem_biUnion.mpr ⟨1,mem_univ _,by simpa [M] using h⟩
      · exact mem_biUnion.mpr ⟨2,mem_univ _,by simpa [M] using h⟩
  have prt : A=R∪Y := by rw [Rform]; exact eqA
  have ry' : Disjoint R Y := by rw [Rform]; exact ry
  have mdis : Pairwise (fun i j => Disjoint (M i) (M j)) := by
    intro i j ne
    fin_cases i <;> fin_cases j
    · exact (ne rfl).elim
    · simpa [M] using cd
    · simpa [M] using cq
    · simpa [M] using cd.symm
    · exact (ne rfl).elim
    · simpa [M] using dq
    · simpa [M] using cq.symm
    · simpa [M] using dq.symm
    · exact (ne rfl).elim
  have mno (i j : Fin 3) (ne : i≠j) (u : V) (ui : u∈M i) (v : V) (vj : v∈M j) :
      ¬G.Adj u v := by
    fin_cases i <;> fin_cases j
    · exact (ne rfl).elim
    · exact nCD u (by simpa [M] using ui) v (by simpa [M] using vj)
    · exact nCQ u (by simpa [M] using ui) v (by simpa [M] using vj)
    · exact fun h => nCD v (by simpa [M] using vj) u (by simpa [M] using ui) h.symm
    · exact (ne rfl).elim
    · exact nDQ u (by simpa [M] using ui) v (by simpa [M] using vj)
    · exact fun h => nCQ v (by simpa [M] using vj) u (by simpa [M] using ui) h.symm
    · exact fun h => nDQ v (by simpa [M] using vj) u (by simpa [M] using ui) h.symm
    · exact (ne rfl).elim
  have mR (i : Fin 3) : M i⊆R := fun _ e => mem_biUnion.mpr ⟨i,mem_univ _,e⟩
  have mA (i : Fin 3) : M i⊆A := by
    intro v vv
    rw [prt]
    exact mem_union.mpr (Or.inl (mR i vv))
  have mY (i : Fin 3) : Disjoint (M i) Y := disjoint_left.mpr (fun _ hi hj =>
    disjoint_left.mp ry' (mR i hi) hj)
  have mOut (i : Fin 3) (u : V) (ui : u∈M i) (v : V) (va : v∈A) (vn : v∉M i) (vy : v∉Y) :
      ¬G.Adj u v := by
    have vr : v∈R := (mem_union.mp (prt ▸ va)).resolve_right vy
    obtain ⟨j,_,vj⟩ := mem_biUnion.mp vr
    exact mno i j (fun e => vn (e.symm ▸ vj)) u ui v vj
  have nonemptyM (i : Fin 3) : (M i).Nonempty := by
    fin_cases i
    · simpa [M] using cn
    · simpa [M] using dn
    · simpa [M] using qn
  have bases (i : Fin 3) := boundSide (M i) Y (mA i) (mY i) yx y2 (mOut i)
  let m3 := (A.card-ell-7)/2
  have m3L : A.card≤2*m3+ell+8 := by dsimp [m3]; omega
  have m3U : 2*m3+ell≤A.card := by dsimp [m3]; omega
  have m3pos : 2≤m3 := by dsimp [m3]; omega
  have mdegree (i : Fin 3) (u : ↥(M i:Set V)) (hi : d≤G.degree u.val) :
      m3≤(G.induce (M i:Set V)).degree u := by
    have b := (bases i u).2 hi
    dsimp [m3]
    omega
  have sizes (i : Fin 3) : m3+1≤(M i).card := by
    obtain ⟨v,vi⟩ := nonemptyM i
    let v' : ↥(M i:Set V) := ⟨v,vi⟩
    have c := (bases i v').1
    have eq : Fintype.card ↥(M i:Set V)=(M i).card := Fintype.card_coe (M i)
    have vv := (G.induce (M i:Set V)).degree_lt_card_verts v'
    obtain ⟨u,ui,w,wi,ne⟩ := one_lt_card.mp (show 1<(M i).card by omega)
    have h : ∃ z∈M i,d≤G.degree z :=
      (deg u w ne).elim (fun a => ⟨u,ui,a⟩) (fun a => ⟨w,wi,a⟩)
    obtain ⟨z,zi,zh⟩ := h
    let z' : ↥(M i:Set V) := ⟨z,zi⟩
    have d' := mdegree i z' zh
    have e := (G.induce (M i:Set V)).degree_lt_card_verts z'
    omega
  have sumSize : A.card=C.card+D.card+Q.card+Y.card := by
    have eq := congrArg Finset.card eqA
    rw [card_union_of_disjoint ry,card_union_of_disjoint (disjoint_union_left.mpr ⟨cq,dq⟩),
      card_union_of_disjoint cd] at eq
    exact eq
  have m3k : m3≤2*k := by
    have a := sizes (0:Fin 3)
    have b := sizes (1:Fin 3)
    have c := sizes (2:Fin 3)
    simp [M] at a b c
    have elK : ell≤k := by dsimp [ell]; omega
    omega
  have tSide (i : Fin 3) (u : V) (ui : u∈M i) : u∈T :=
    mem_erase.mpr ⟨fun e => disjoint_left.mp (mY i) ui (e.symm ▸ yx),mA i ui⟩
  have high3 (i : Fin 3) (u : V) (ui : u∈M i) (ul : u∉L) :
      m3-1≤((M i).filter (G.Adj u)).card := by
    have hi : d≤G.degree u := Nat.le_of_not_gt (fun h => ul (mem_filter.mpr ⟨tSide i u ui,h⟩))
    let v : ↥(M i:Set V) := ⟨u,ui⟩
    have d := mdegree i v hi
    have b := induced_degree_count (G:=G) (M i) v
    change ((M i).filter (G.Adj u)).card=(G.induce (M i:Set V)).degree v at b
    omega
  have low3 (i : Fin 3) (u : V) (ui : u∈M i) (_ul : u∈L) :
      1≤((M i).filter (G.Adj u)).card := by
    let v : ↥(M i:Set V) := ⟨u,ui⟩
    have d := (bases i v).1
    have b := induced_degree_count (G:=G) (M i) v
    change ((M i).filter (G.Adj u)).card=(G.induce (M i:Set V)).degree v at b
    omega
  have highJ3 (v : V) (vt : v∈T) (vl : v∉L) : m3≤(T.filter (G.Adj v)).card := by
    let v' : ↥(T:Set V) := ⟨v,vt⟩
    have vh : d≤G.degree v := Nat.le_of_not_gt (fun h => vl (mem_filter.mpr ⟨vt,h⟩))
    have b := (quadratic_root_deleted_degrees hc k sl loss cap conn hp hx bk far v').2 vh
    change A.card≤2*J.degree v'+loss+3 at b
    have id := induced_degree_count (G:=G) T v'
    change (T.filter (G.Adj v)).card=J.degree v' at id
    dsimp [m3]
    omega
  have route3 := one_low_universal_uniform_routes A L x xA root L1 m3 highJ3 lowJ
  exact ThreeNormalized.three_split_impossible hc k sl m3 large (by omega) m3pos m3k hp hx first
    cap₂ conn deg (support_large k conn hp hx) M Y (Y.erase x) prt
    (leafPartition R Y prt ry' yx) yx y3 y2 ry' mdis mno sizes L L1 high3 low3 route3
    (by change k+ell≤A.card; omega) m3L m3U p3 bp base

/-- High-connectivity range of Graffiti.pc #189 asymptotically one half. -/
theorem traceable_of_half_connectivity (hc : G.Connected) (d k : Nat)
    (large : 1000000≤k) (ratio : d+100≤2*k)
    (cap : ∀ v,(EvenFrom G v).card≤d+1)
    (conn : ∀ S : Finset V,S.card<k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (deg : ∀ u v : V,u≠v → d≤G.degree u ∨ d≤G.degree v) :
    ∃ (u v : V) (q : G.Walk u v),q.IsPath ∧ ∀ z,z∈q.support := by
  by_cases hk : 3*d≤5*k
  · exact Graffiti189LongestPath.ThreeFifthsDeficit.traceable_of_three_fifths_connectivity hc d k
      (by omega) hk cap conn deg
  have eq : k+(d-k)=d := by omega
  exact traceable_of_half_gap hc k (d-k) large (by omega) (by omega)
    (by simpa only [eq] using cap) conn (by simpa only [eq] using deg)

#print axioms traceable_of_half_gap
#print axioms traceable_of_half_connectivity
end Graffiti189LongestPath.HalfBandDeficit
