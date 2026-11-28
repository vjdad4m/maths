import PosaOneLow189
import SingleRadiusCriticalOffPath189
import StarCycleClosure189
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack Graffiti189LongestPath.ActiveStarHeight
open Graffiti189LongestPath.ExactStarShore Graffiti189LongestPath.ShoreConnectivity Graffiti189LongestPath.ShoreDegrees
open Graffiti189LongestPath.UniversalCharge Graffiti189LongestPath.StarCycleClosure
open Graffiti189LongestPath.Normalize Graffiti189LongestPath.PosaOneLow Graffiti189LongestPath.SingleRadiusRoutable
open Graffiti189LongestPath.CycleHallSplice Graffiti189LongestPath.SingleRadiusCriticalOffPath
open private Graffiti189LongestPath.Rigidity.mem_external Graffiti189LongestPath.Rigidity.mem_omittedStar from Rigidity189
open private Graffiti189LongestPath.boundary_card_of_connectivity Graffiti189LongestPath.no_endpoints from SmallSeparator189
set_option warningAsError true
set_option maxHeartbeats 4500000
namespace Graffiti189LongestPath.SingleRadiusShore
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem single_star_stays_connected (hc : G.Connected) (k : Nat) (hk : 6≤k)
    (cap : ∀ v,(EvenFrom G v).card≤k+3)
    (conn : ∀ D : Finset V,D.card<k → (G.induce ((↑D : Set V)ᶜ)).Connected)
    (deg : ∀ u v : V,u≠v → k+2≤G.degree u ∨ k+2≤G.degree v)
    (fail : ¬∃ (u v : V) (q : G.Walk u v),q.IsPath ∧ ∀ w,w∈q.support)
    {a b x : V} {p : G.Walk a b} (hp : IsLongest p)
    (hx : x∉p.support)
    (one : (Pins p x).card=1) (sat : (External G (OmittedStar p x)).card=k)
    (X : Finset V) (inside : X⊆OmittedStar p x)
    (small : 3*X.card+4<(OmittedStar p x).card) :
    (G.induce ((↑((OmittedStar p x)\X)):Set V)).Connected := by
  classical
  let A := OmittedStar p x
  let B := External G A
  let U := univ\(A∪B)
  change B.card=k at sat
  obtain ⟨i,hi⟩ := card_pos.mp (by omega : 0<(Pins p x).card)
  have large : k≤U.card := opposite_large_of_not_traceable hc k (by omega)
    cap conn deg hp hx (by omega) hi sat fail
  have rA {z : V} (hz : z∈U) : z∉A := fun h =>
    (mem_sdiff.mp hz).2 (mem_union.mpr (Or.inl h))
  have rB {z : V} (hz : z∈U) : z∉B := fun h =>
    (mem_sdiff.mp hz).2 (mem_union.mpr (Or.inr h))
  have ul : ∀ u∈U,∀ v∉U,G.Adj u v → v∈B := by
    intro u hu v hv ed
    have cov : v∈A∪B := Classical.byContradiction
      (fun h => hv (mem_sdiff.mpr ⟨mem_univ _,h⟩))
    exact (mem_union.mp cov).elim (fun h => (rB hu
      (Graffiti189LongestPath.Rigidity.mem_external.mpr ⟨rA hu,v,h,ed.symm⟩)).elim) id
  have ub : Disjoint U B := disjoint_left.mpr (fun _ h h' => rB h h')
  have au : Disjoint A U := disjoint_left.mpr (fun _ h h' => rA h' h)
  have ab : Disjoint A B := disjoint_left.mpr (fun _ h h' =>
    (Graffiti189LongestPath.Rigidity.mem_external.mp h').1 h)
  have cA : ∀ y∈A,∀ z∉A,G.Adj y z → z∈B := fun _ hy _ hz e =>
    Graffiti189LongestPath.Rigidity.mem_external.mpr ⟨hz,_,hy,e⟩
  have r : ∀ z∈A,z=x ∨ G.Adj x z := fun _ h =>
    (Graffiti189LongestPath.Rigidity.mem_omittedStar.mp h).2
  exact universal_shore_stays_connected hc k A B U X x conn sat ab ub au large
    (by omega) cA ul (fun v => distanceTwo_le_of_even (k+2) v (cap v)) r inside small


theorem single_root_deleted_degrees (hc : G.Connected) (k : Nat) (hk : 6≤k)
    (cap : ∀ v,(EvenFrom G v).card≤k+3)
    (conn : ∀ S : Finset V,S.card<k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (deg : ∀ u v : V,u≠v → k+2≤G.degree u ∨ k+2≤G.degree v)
    (fail : ¬∃ (u v : V) (q : G.Walk u v),q.IsPath ∧ ∀ z,z∈q.support)
    {a b x : V} {p : G.Walk a b} (hp : IsLongest p) (hx : x∉p.support)
   
    (one : (Pins p x).card=1) (sat : (External G (OmittedStar p x)).card=k)
    (v : ↥(((OmittedStar p x).erase x : Finset V) : Set V)) :
    (OmittedStar p x).card≤2*(G.induce (((OmittedStar p x).erase x : Finset V) : Set V)).degree v+5 ∧
      (k+2≤G.degree v.val →
       (OmittedStar p x).card≤2*(G.induce (((OmittedStar p x).erase x : Finset V) : Set V)).degree v+3) := by
  classical
  let A := OmittedStar p x
  let B := External G A
  let U := univ\(A∪B)
  let T := A.erase x
  let J := G.induce (T : Set V)
  let I := G.induce (A : Set V)
  change B.card=k at sat
  obtain ⟨i,hi⟩ := card_pos.mp (by omega : 0<(Pins p x).card)
  have large : k≤U.card := opposite_large_of_not_traceable hc k (by omega) cap conn deg
    hp hx (by omega) hi sat fail
  have rA {z : V} (hz : z∈U) : z∉A := fun h => (mem_sdiff.mp hz).2 (mem_union.mpr (Or.inl h))
  have rB {z : V} (hz : z∈U) : z∉B := fun h => (mem_sdiff.mp hz).2 (mem_union.mpr (Or.inr h))
  have ul : ∀ u∈U,∀ v∉U,G.Adj u v → v∈B := by
    intro u hu v hv ed
    have cov : v∈A∪B := Classical.byContradiction (fun h => hv (mem_sdiff.mpr ⟨mem_univ _,h⟩))
    exact (mem_union.mp cov).elim (fun h => (rB hu
      (Graffiti189LongestPath.Rigidity.mem_external.mpr ⟨rA hu,v,h,ed.symm⟩)).elim) id
  have ub : Disjoint U B := disjoint_left.mpr (fun _ h h' => rB h h')
  have au : Disjoint A U := disjoint_left.mpr (fun _ h h' => rA h' h)
  have ab : Disjoint A B := disjoint_left.mpr (fun _ h h' =>
    (Graffiti189LongestPath.Rigidity.mem_external.mp h').1 h)
  have cA : ∀ y∈A,∀ z∉A,G.Adj y z → z∈B := fun _ hy _ hz e =>
    Graffiti189LongestPath.Rigidity.mem_external.mpr ⟨hz,_,hy,e⟩
  have root : ∀ z∈A,z=x ∨ G.Adj x z := fun _ h =>
    (Graffiti189LongestPath.Rigidity.mem_omittedStar.mp h).2
  have va : v.val∈A := (mem_erase.mp v.property).2
  have vo : v.val∉p.support := (Graffiti189LongestPath.Rigidity.mem_omittedStar.mp va).1
  have vx : G.Adj v.val x := ((root _ va).resolve_left (mem_erase.mp v.property).1).symm
  have xa : x∈A := Graffiti189LongestPath.Rigidity.mem_omittedStar.mpr ⟨hx,Or.inl rfl⟩
  have low : k≤G.degree v.val := by
    have av : a≠v.val := fun e => vo (e ▸ p.start_mem_support)
    rw [←G.card_neighborFinset_eq_degree]
    apply Graffiti189LongestPath.boundary_card_of_connectivity k conn (A:={v.val}) (a:=a)
    · exact mem_singleton_self _
    · exact fun h => av (mem_singleton.mp h)
    · exact fun h => (Graffiti189LongestPath.no_endpoints hp vo).1 ((G.mem_neighborFinset _ _).mp h)
    · exact disjoint_left.mpr (fun _ h e => ((G.mem_neighborFinset v.val _).mp e).ne (mem_singleton.mp h).symm)
    · exact fun _ h _ _ e => (G.mem_neighborFinset _ _).mpr ((mem_singleton.mp h) ▸ e)
  let av : ↥(A : Set V) := ⟨v.val,va⟩
  have ineq := universal_shore_charge hc (k+2) k A U B conn sat ab ub au large
    cA ul (fun v => distanceTwo_le_of_even (k+2) v (cap v)) root av
  change A.card+G.degree v.val+_≤2*I.degree av+(k+2)+1 at ineq
  have id := universal_root_degree_drop A x xa v vx
  change J.degree v+1=I.degree av at id
  change A.card≤2*J.degree v+5 ∧ (k+2≤G.degree v.val → A.card≤2*J.degree v+3)
  omega

#print axioms universal_root_degree_drop

theorem single_root_deleted_long_cycle
    (hc : G.Connected) (k : Nat) (hk : 9≤k)
    (cap : ∀ v,(EvenFrom G v).card≤k+3)
    (conn : ∀ S : Finset V,S.card<k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (deg : ∀ u v : V,u≠v → k+2≤G.degree u ∨ k+2≤G.degree v)
    (fail : ¬∃ (u v : V) (q : G.Walk u v),q.IsPath ∧ ∀ z,z∈q.support)
    {a b x : V} {p : G.Walk a b} (hp : EdgeMinAvoid (k+2) p) (hx : x∉p.support)
    (one : (Pins p x).card=1) (sat : (External G (OmittedStar p x)).card=k)
    (high : k+2≤G.degree x) :
    ∃ a, ∃ c : (G.induce (((OmittedStar p x).erase x : Finset V) : Set V)).Walk a a,
      c.IsCycle ∧ 2*((OmittedStar p x).card/2-1)≤c.length := by
  classical
  let A := OmittedStar p x
  let T := A.erase x
  let W := ↥(T : Set V)
  let J := G.induce (T : Set V)
  let m := A.card/2-1
  have xt : x∈A := Graffiti189LongestPath.Rigidity.mem_omittedStar.mpr ⟨hx,Or.inl rfl⟩
  have h : k+2≤A.card := by
    have e := star_card_degree_and_pins hp.1.1 hx
    change A.card+(Pins p x).card=G.degree x+1 at e
    omega
  have wc : Fintype.card W=A.card-1 := by
    change Fintype.card ↥T=A.card-1
    exact (Fintype.card_coe T).trans (card_erase_of_mem xt)
  have del (S : Finset W) (sc : S.card<2) :
      (J.induce ((↑S : Set W)ᶜ)).Connected := by
    let e : W ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
    let X := insert x (S.map e)
    have xs : X⊆A := by
      intro v vx
      rcases mem_insert.mp vx with rfl|h
      · exact xt
      · obtain ⟨w,_,rfl⟩ := mem_map.mp h
        exact (mem_erase.mp w.property).2
    have xl := (card_insert_le x (S.map e)).trans (by rw [card_map])
    change X.card≤S.card+1 at xl
    have sz : 3*X.card+4<(OmittedStar p x).card := by change 3*X.card+4<A.card; omega
    have con := single_star_stays_connected hc k (by omega) cap conn deg fail
      hp.1.1 hx one sat X xs sz
    exact (erase_root_and_set_iso (G:=G) A x S).connected_iff.mp con
  have low (v : W) : 2≤J.degree v := by
    have dg := (single_root_deleted_degrees hc k (by omega) cap conn deg fail hp.1.1
      hx one sat v).1
    change A.card≤2*J.degree v+5 at dg
    omega
  have highJ (v : W) (vh : k+2≤G.degree v.val) : m≤J.degree v := by
    have dg := (single_root_deleted_degrees hc k (by omega) cap conn deg fail hp.1.1
      hx one sat v).2 vh
    change A.card≤2*J.degree v+3 at dg
    dsimp [m]
    omega
  have pair (u v : W) (ne : u≠v) : m≤J.degree u ∨ m≤J.degree v :=
    (deg u.val v.val (fun e => ne (Subtype.ext e))).imp (highJ u) (highJ v)
  have mc : 2≤m := by dsimp [m]; omega
  obtain ⟨r,c,cc,cl⟩ := proved_one_low_circumference W J m mc (by omega) del low pair
  have mm : 2*m≤Fintype.card W := by dsimp [m]; omega
  rw [min_eq_right mm] at cl
  exact ⟨r,c,cc,cl⟩


theorem single_no_long_shore_cycle (hc : G.Connected) (k : Nat) (hk : 6≤k)
    (cap : ∀ v,(EvenFrom G v).card≤k+3)
    (conn : ∀ D : Finset V,D.card<k → (G.induce ((↑D : Set V)ᶜ)).Connected)
    (deg : ∀ u v : V,u≠v → k+2≤G.degree u ∨ k+2≤G.degree v)
    (fail : ¬∃ (u v : V) (q : G.Walk u v),q.IsPath ∧ ∀ w,w∈q.support)
    {a b x : V} {p : G.Walk a b} (hp : IsLongest p)
    (hx : x∉p.support)
    (high : k+2≤G.degree x)
    (one : (Pins p x).card=1) (sat : (External G (OmittedStar p x)).card=k)
    (rad : ∀ z,G.dist x z≤4)
    (large : 10<(OmittedStar p x).card)
    (len : Nat)
    (long : k*(k+2)<(k+1)*(len+1)+
      2*(External G (OmittedStar p x)\p.support.toFinset).card)
    (cyc : ∃ z, ∃ c : (G.induce (((OmittedStar p x).erase x : Finset V) : Set V)).Walk z z,
      c.IsCycle ∧ max 2 len≤c.length) : False := by
  classical
  let A := OmittedStar p x
  let Z : Set V := ((A.erase x : Finset V) : Set V)
  let J := G.induce Z
  have sepConn (S : Finset Z) (sc : S.card<2) :
      (J.induce ((↑S : Set Z)ᶜ)).Connected := by
    let e : Z ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
    let X := insert x (S.map e)
    have xs : X⊆A := by
      intro v vx
      rcases mem_insert.mp vx with rfl|h
      · exact Graffiti189LongestPath.Rigidity.mem_omittedStar.mpr ⟨hx,Or.inl rfl⟩
      · obtain ⟨w,_,rfl⟩ := mem_map.mp h
        exact (mem_erase.mp w.property).2
    have xl := (card_insert_le x (S.map e)).trans (by rw [card_map])
    change X.card≤S.card+1 at xl
    have con := single_star_stays_connected hc k hk cap conn deg fail hp
      hx one sat X xs (by omega)
    exact (erase_root_and_set_iso (G:=G) A x S).connected_iff.mp con
  let f : J →g G := ⟨Subtype.val, fun e => e⟩
  have fi : Function.Injective f := Subtype.val_injective
  have off (z : Z) : x≠f z := fun e => (mem_erase.mp z.property).1 e.symm
  have adj (z : Z) : G.Adj x (f z) := by
    have zz := (mem_erase.mp z.property).2
    exact (Graffiti189LongestPath.Rigidity.mem_omittedStar.mp zz).2.resolve_left (fun ne => off z ne.symm)
  obtain ⟨a,c,hc',cl⟩ := cyc
  have big : 2≤c.support.toFinset.card := by
    rw [cycle_card_support c hc']
    exact (le_max_left _ _).trans cl
  have L : len≤c.length := (le_max_right _ _).trans cl
  have route : ∀ u∈A,∀ v∈A,u≠v →
      ∃ q : G.Walk u v,q.IsPath ∧ (∀ z∈q.support,z∈A) ∧ len+1≤q.length+1 := by
    intro u ua v va uv
    have rA {z : V} (e : z=x ∨ ∃ w : Z,f w=z) : z∈A := by
      rcases e with rfl|⟨w,rfl⟩
      · exact Graffiti189LongestPath.Rigidity.mem_omittedStar.mpr ⟨hx,Or.inl rfl⟩
      · exact (mem_erase.mp w.property).2
    by_cases hu : u=x
    · subst u
      let t : Z := ⟨v,mem_erase.mpr ⟨uv.symm,va⟩⟩
      obtain ⟨q,qp,ql,qs⟩ := cycle_to_prescribed_root_route f fi off adj c hc'
        (t:=t) (fun s h => sepConn s (by omega))
      exact ⟨q,qp,fun z hz => rA (qs z hz),by omega⟩
    by_cases hv : v=x
    · subst v
      let t : Z := ⟨u,mem_erase.mpr ⟨hu,ua⟩⟩
      obtain ⟨q,qp,ql,qs⟩ := cycle_to_prescribed_root_route f fi off adj c hc'
        (t:=t) (fun s h => sepConn s (by omega))
      exact ⟨q.reverse,qp.reverse,fun z hz => rA (qs z (by
        simpa only [support_reverse,List.mem_reverse] using hz)),by simpa using (by omega : len+1≤q.length+1)⟩
    let s : Z := ⟨u,mem_erase.mpr ⟨hu,ua⟩⟩
    let t : Z := ⟨v,mem_erase.mpr ⟨hv,va⟩⟩
    have ne : s≠t := fun e => uv (congrArg Subtype.val e)
    obtain ⟨q,qp,ql,qs⟩ := cycle_to_prescribed_route f fi ne off adj c hc' big sepConn
    exact ⟨q,qp,fun z hz => rA (qs z hz),by omega⟩
  exact single_terminal_order_impossible hc k hk cap conn hp hx high one sat rad
    (len+1) route long

#print axioms erase_root_and_set_iso

theorem single_no_marked_shore_cycle (hc : G.Connected) (k : Nat) (hk : 6≤k)
    (cap : ∀ v,(EvenFrom G v).card≤k+3)
    (conn : ∀ D : Finset V,D.card<k → (G.induce ((↑D : Set V)ᶜ)).Connected)
    (deg : ∀ u v : V,u≠v → k+2≤G.degree u ∨ k+2≤G.degree v)
    (fail : ¬∃ (u v : V) (q : G.Walk u v),q.IsPath ∧ ∀ w,w∈q.support)
    {a b x : V} {p : G.Walk a b} (hp : IsLongest p)
    (hx : x∉p.support)
    (high : k+2≤G.degree x)
    (one : (Pins p x).card=1) (sat : (External G (OmittedStar p x)).card=k)
    (rad : ∀ z,G.dist x z≤4)
    (large : 10<(OmittedStar p x).card)
    (m : ↥(((OmittedStar p x).erase x : Finset V) : Set V))
    (pay : k≤2*(External G (OmittedStar p x)\p.support.toFinset).card+1)
    {z : V} (zb : z∈External G (OmittedStar p x)) (mz : G.Adj m.val z)
    (cyc : ∃ a, ∃ c : (G.induce (((OmittedStar p x).erase x : Finset V) : Set V)).Walk a a,
      c.IsCycle ∧ max 2 (k-1)≤c.length ∧ m∉c.support) : False := by
  classical
  let A := OmittedStar p x
  have A_large : 10<A.card := large
  let Z : Set V := ((A.erase x : Finset V) : Set V)
  let J := G.induce Z
  have sepConn (S : Finset Z) (sc : S.card<2) :
      (J.induce ((↑S : Set Z)ᶜ)).Connected := by
    let e : Z ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
    let X := insert x (S.map e)
    have xs : X⊆A := by
      intro v vx
      rcases mem_insert.mp vx with rfl|h
      · exact Graffiti189LongestPath.Rigidity.mem_omittedStar.mpr ⟨hx,Or.inl rfl⟩
      · obtain ⟨w,_,rfl⟩ := mem_map.mp h
        exact (mem_erase.mp w.property).2
    have xl := (card_insert_le x (S.map e)).trans (by rw [card_map])
    change X.card≤S.card+1 at xl
    have con := single_star_stays_connected hc k hk cap conn deg fail hp
      hx one sat X xs (by omega)
    exact (erase_root_and_set_iso (G:=G) A x S).connected_iff.mp con
  let f : J →g G := ⟨Subtype.val, fun e => e⟩
  have fi : Function.Injective f := Subtype.val_injective
  have off (z : Z) : x≠f z := fun e => (mem_erase.mp z.property).1 e.symm
  have adj (z : Z) : G.Adj x (f z) := by
    have zz := (mem_erase.mp z.property).2
    exact (Graffiti189LongestPath.Rigidity.mem_omittedStar.mp zz).2.resolve_left (fun ne => off z ne.symm)
  obtain ⟨a,c,hc',cl,miss⟩ := cyc
  have big : 2≤c.support.toFinset.card := by
    rw [cycle_card_support c hc']
    exact (le_max_left _ _).trans cl
  have L : k-1≤c.length := (le_max_right _ _).trans cl
  have mA : m.val∈A := (mem_erase.mp m.property).2
  have mx : m.val≠x := (mem_erase.mp m.property).1
  let e (v : V) := if v=m.val then (1:Nat) else 0
  have e0 : e x=0 := by simp [e,mx.symm]
  have gain (v : Z) : e (f v)≤(if v∈c.support then 0 else 1) := by
    by_cases eq : f v=m.val
    · have vm : v=m := Subtype.ext eq
      have no : v∉c.support := vm ▸ miss
      simp [e,eq,no]
    · simp [e,eq]
  have route : ∀ u∈A,∀ v∈A,u≠v →
      ∃ q : G.Walk u v,q.IsPath ∧ (∀ z∈q.support,z∈A) ∧ k+e u+e v≤q.length+1 := by
    intro u ua v va uv
    have rA {z : V} (e : z=x ∨ ∃ w : Z,f w=z) : z∈A := by
      rcases e with rfl|⟨w,rfl⟩
      · exact Graffiti189LongestPath.Rigidity.mem_omittedStar.mpr ⟨hx,Or.inl rfl⟩
      · exact (mem_erase.mp w.property).2
    by_cases hu : u=x
    · subst u
      let t : Z := ⟨v,mem_erase.mpr ⟨uv.symm,va⟩⟩
      obtain ⟨q,qp,ql,qs⟩ := cycle_to_prescribed_root_route_bonus f fi off adj c hc'
        (t:=t) (fun s h => sepConn s (by omega))
      have tv := gain t
      change e v≤_ at tv
      exact ⟨q,qp,fun z hz => rA (qs z hz),by rw [e0]; omega⟩
    by_cases hv : v=x
    · subst v
      let t : Z := ⟨u,mem_erase.mpr ⟨hu,ua⟩⟩
      obtain ⟨q,qp,ql,qs⟩ := cycle_to_prescribed_root_route_bonus f fi off adj c hc'
        (t:=t) (fun s h => sepConn s (by omega))
      have tu := gain t
      change e u≤_ at tu
      exact ⟨q.reverse,qp.reverse,fun z hz => rA (qs z (by
        simpa only [support_reverse,List.mem_reverse] using hz)),by rw [length_reverse,e0]; omega⟩
    let s : Z := ⟨u,mem_erase.mpr ⟨hu,ua⟩⟩
    let t : Z := ⟨v,mem_erase.mpr ⟨hv,va⟩⟩
    have ne : s≠t := fun e => uv (congrArg Subtype.val e)
    obtain ⟨q,qp,ql,qs⟩ := cycle_to_prescribed_route_bonus f fi ne off adj c hc' big sepConn
    have su := gain s
    have tv := gain t
    change e u≤_ at su
    change e v≤_ at tv
    exact ⟨q,qp,fun z hz => rA (qs z hz),by omega⟩
  apply single_marked_order_impossible hc k hk cap conn hp hx high one sat rad mA zb mz pay
  · intro u ua
    obtain ⟨v,va,ne⟩ := exists_ne_of_one_lt_card (by omega : 1<A.card) u
    obtain ⟨q,qp,qs,ql⟩ := route u ua v va ne.symm
    exact ⟨v,q,qp,qs,by change k+e u≤q.length+1; omega⟩
  · exact route

#print axioms single_root_deleted_long_cycle
#print axioms single_no_long_shore_cycle
#print axioms single_no_marked_shore_cycle
end Graffiti189LongestPath.SingleRadiusShore
