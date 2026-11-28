import TwoThirdsDeficitAll189
import FlexSplitShell189
import SplitGreedy189
import FlexibleFan189
import PortReachCount189
import GapOne189
import FlexibleFinishNumeric189
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
set_option warningAsError true
set_option maxHeartbeats 7000000
namespace Graffiti189LongestPath.ThreeFifthsDeficit
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- #189 in an explicit quadratic connectivity range, without needing
2-connectivity of the omitted shore.
No normalized attachment or separator geometry is assumed. -/
theorem traceable_of_three_fifths_gap (hc : G.Connected) (k sl : Nat) (large : 2000≤k) (ratio : 3*sl≤2*k) (positive : 1≤sl)
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
  let W' := X.erase x
  have ec : C⊆A\X := fun _ h => part ▸ mem_union.mpr (Or.inl h)
  have ee : E⊆A\X := fun _ h => part ▸ mem_union.mpr (Or.inr h)
  have pinOff : Disjoint A P := disjoint_left.mpr (by
    intro z za zp
    obtain ⟨i,_,rfl⟩ := mem_image.mp zp
    exact ao _ za (p.getVert_mem_support i))
  have cp : Disjoint C P := disjoint_left.mpr (fun _ h h' => disjoint_left.mp pinOff (mem_sdiff.mp (ec h)).1 h')
  have ep : Disjoint E P := disjoint_left.mpr (fun _ h h' => disjoint_left.mp pinOff (mem_sdiff.mp (ee h)).1 h')
  have cw : Disjoint C W' := disjoint_left.mpr (fun _ h h' => (mem_sdiff.mp (ec h)).2 (mem_erase.mp h').2)
  have ew : Disjoint E W' := disjoint_left.mpr (fun _ h h' => (mem_sdiff.mp (ee h)).2 (mem_erase.mp h').2)
  have pw : Disjoint P W' := disjoint_left.mpr (fun _ h h' => disjoint_left.mp pinOff (xsub (mem_erase.mp h').2) h)
  have pp : P.card≤sl := by
    have h := Graffiti189LongestPath.OneSlack.card_pinVertices hp (x:=x)
    change P.card=(Pins p x).card at h
    omega
  have wc : W'.card≤1 := by
    have h := card_erase_add_one xx
    change W'.card+1=X.card at h
    omega
  have nbh : G.neighborFinset x=T∪P := by
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
  have rest : (C∪E)∪W'=T := by
    rw [part]
    ext z
    simp only [mem_union,mem_sdiff,mem_erase,T,W']
    constructor
    · intro h
      rcases h with ⟨za,zx⟩|⟨zx,ze⟩
      · exact ⟨fun e => zx (e.symm ▸ xx),za⟩
      · exact ⟨zx,xsub ze⟩
    · rintro ⟨zx,za⟩
      by_cases zX : z∈X
      · exact Or.inr ⟨zx,zX⟩
      · exact Or.inl ⟨za,zX⟩
  have partition : C∪E∪P∪W'=G.neighborFinset x := by
    rw [nbh,←rest]
    ac_rfl
  have cA : C⊆A := fun _ z => (mem_sdiff.mp (ec z)).1
  have eA : E⊆A := fun _ z => (mem_sdiff.mp (ee z)).1
  have cX : Disjoint C X := disjoint_left.mpr (fun _ z w => (mem_sdiff.mp (ec z)).2 w)
  have eX : Disjoint E X := disjoint_left.mpr (fun _ z w => (mem_sdiff.mp (ee z)).2 w)
  have shore : A=C∪E∪X := by
    rw [part]
    exact (sdiff_union_of_subset xsub).symm
  have ab : Disjoint A B := disjoint_left.mpr (fun _ z w =>
    (Graffiti189LongestPath.Rigidity.mem_external.mp w).1 z)
  have closed (u : V) (ua : u∈A) (v : V) (va : v∉A) (ed : G.Adj u v) : v∈B :=
    Graffiti189LongestPath.Rigidity.mem_external.mpr ⟨va,u,ua,ed⟩
  have mm : m≤C.card := by dsimp [m]; omega
  have gain (C E : Finset V) (part : C∪E=A\X) (no : ∀ u∈C,∀ v∈E,¬G.Adj u v)
      (v : V) (vc : v∈C) :
      (T.filter (G.Adj v)).card≤(C.filter (G.Adj v)).card+1 := by
    have cover : T.filter (G.Adj v)⊆(C.filter (G.Adj v))∪W' := by
      intro z h
      obtain ⟨zt,ed⟩ := mem_filter.mp h
      by_cases zx : z∈X
      · exact mem_union.mpr (Or.inr (mem_erase.mpr ⟨(mem_erase.mp zt).1,zx⟩))
      have zCE : z∈C∪E := part.symm ▸ mem_sdiff.mpr ⟨(mem_erase.mp zt).2,zx⟩
      rcases mem_union.mp zCE with zc|ze
      · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨zc,ed⟩))
      · exact (no v vc z ze ed).elim
    have hc' := (card_le_card cover).trans (card_union_le (C.filter (G.Adj v)) W')
    omega
  have ceB := fun v vc => gain C E part no v vc
  have ecB := fun v ve => gain E C ((union_comm E C).trans part)
    (fun u ue v vc adj => no v vc u ue adj.symm) v ve
  have cT (v : V) (vc : v∈C) : v∈T :=
    mem_erase.mpr ⟨fun h => (mem_sdiff.mp (ec vc)).2 (h.symm ▸ xx),cA vc⟩
  have eT (v : V) (ve : v∈E) : v∈T :=
    mem_erase.mpr ⟨fun h => (mem_sdiff.mp (ee ve)).2 (h.symm ▸ xx),eA ve⟩
  have lowerTwo (v : V) (vt : v∈T) : 2≤(T.filter (G.Adj v)).card := by
    let v' : ↥(T:Set V) := ⟨v,vt⟩
    have eq := induced_degree_count (G:=G) T v'
    change (T.filter (G.Adj v)).card=J.degree v' at eq
    rw [eq]
    exact floorJ v'
  have cross := SplitGreedy.greedy_cross_shore_route A C E L m L1 (by dsimp [m]; omega)
    x xA (fun h => (mem_sdiff.mp (ec h)).2 xx) (fun h => (mem_sdiff.mp (ee h)).2 xx)
    cA eA ce root (fun v vc vl => by have b := highJ v (cT v vc) vl; have e := ceB v vc; omega)
    (fun v ve vl => by have b := highJ v (eT v ve) vl; have e := ecB v ve; omega)
    (fun v vc _ => by have b := lowerTwo v (cT v vc); have e := ceB v vc; omega)
    (fun v ve _ => by have b := lowerTwo v (eT v ve); have e := ecB v ve; omega)
  have shell := FlexSplitShell.flex_split_shell_three_bound hc d (Pins p x).card m (by dsimp [d]; omega)
    cap₂ x A B C E P W' X partition shore (fun v z => or_iff_not_imp_left.mpr (root v z))
    closed deg ce cp cw ep ew pw no smaller mm (by dsimp [m,d]; omega)
    (le_of_eq (Graffiti189LongestPath.OneSlack.card_pinVertices hp (x:=x))) wc xs bp
  have many := PortReachCount.many_flexible_hooks k loss hp A B C E X conn shore ab ce cX eX cn en no
    closed ao bk F
  have flex := FlexibleFan.flexible_hooked_lower k (m+1) (m-2) (by omega) hp A C E X ao
    (by omega) cA eA ce cn en shore routes cross F
  let ff := ((univ : Finset (Fin k)).filter (fun i =>
      (∃ u∈C,G.Adj u (HookRetarget.fromFamily F i).firstPort) ∧
        ∃ v∈E,G.Adj v (HookRetarget.fromFamily F i).firstPort)).card
  change k≤ff+2*loss+2*X.card at many
  change A.card+k+(k+1)*(m+1)+ff*(m-2)≤Fintype.card V+X.card*(m-2) at flex
  have base' : (k+1)*(m+1)≤H.card+2*sl := by omega
  have flex' : (k+1)*(m+1)+ff*(m-2)≤H.card+2*sl+2*(m-2) := by
    have z := Nat.mul_le_mul_right (m-2) xs
    omega
  have mi : 2≤m := by dsimp [m]; omega
  have flexI : ((k:ℤ)+1)*((m:ℤ)+1)+(ff:ℤ)*((m:ℤ)-2)≤
      (H.card:ℤ)+2*(sl:ℤ)+2*((m:ℤ)-2) := by
    have z : ((k:ℤ)+1)*((m:ℤ)+1)+(ff:ℤ)*((m-2:ℕ):ℤ)≤
      (H.card:ℤ)+2*(sl:ℤ)+2*((m-2:ℕ):ℤ) := by exact_mod_cast flex'
    rw [Int.ofNat_sub mi] at z
    simpa using z
  have finish := FlexibleFinishNumeric.split_contradiction (k:ℤ) (sl:ℤ) ((Pins p x).card:ℤ)
    (m:ℤ) (ff:ℤ) (H.card:ℤ) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by dsimp [m]; omega) (by dsimp [m]; omega) (by dsimp [loss] at many; omega)
    (by exact_mod_cast base') flexI (by
      rcases shell with h|h
      · left
        dsimp [d] at h
        exact_mod_cast (by simpa only [pow_two] using h)
      · right
        have mm' : m≤d+1 := by dsimp [d,m]; omega
        have h' : (4:ℤ)*(H.card:ℤ)≤
            ((d+1-m:ℕ):ℤ)*((d+1-m:ℕ):ℤ)+4*((m:ℤ)*((Pins p x).card:ℤ))+8*(d:ℤ) := by
          exact_mod_cast h
        rw [Int.ofNat_sub mm'] at h'
        push_cast at h'
        dsimp [d] at h'
        push_cast at h'
        simpa only [pow_two, ← mul_assoc] using h')
  exact finish

/-- High-connectivity range of Graffiti.pc #189, down to three fifths of the degree threshold. -/
theorem traceable_of_three_fifths_connectivity (hc : G.Connected) (d k : Nat)
    (large : 2000≤k) (ratio : 3*d≤5*k)
    (cap : ∀ v,(EvenFrom G v).card≤d+1)
    (conn : ∀ S : Finset V,S.card<k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (deg : ∀ u v : V,u≠v → d≤G.degree u ∨ d≤G.degree v) :
    ∃ (u v : V) (q : G.Walk u v),q.IsPath ∧ ∀ z,z∈q.support := by
  by_cases hk : d≤k
  · exact traceable_of_even_and_connectivity hc d cap (fun S sc => conn S (sc.trans_le hk))
  have eq : k+(d-k)=d := by omega
  exact traceable_of_three_fifths_gap hc k (d-k) large (by omega) (by omega)
    (by simpa only [eq] using cap) conn (by simpa only [eq] using deg)

#print axioms traceable_of_three_fifths_gap
#print axioms traceable_of_three_fifths_connectivity
end Graffiti189LongestPath.ThreeFifthsDeficit
