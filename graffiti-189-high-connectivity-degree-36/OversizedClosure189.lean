import SeparatedRootReduction189
import OversizedRoutable189
import OversizedShore189
import DefectiveTerminal189
import JointLitBudget189
import HighBoundaryClosure189
import OffPathBoundaryBudget189
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack Graffiti189LongestPath.ActiveStarHeight
open Graffiti189LongestPath.Normalize Graffiti189LongestPath.ExactStarShore Graffiti189LongestPath.TwoShoreTight
open Graffiti189LongestPath.OversizedRoutable Graffiti189LongestPath.OversizedShore
open Graffiti189LongestPath.DefectiveCharge Graffiti189LongestPath.DefectiveTerminal
open Graffiti189LongestPath.JointLitBudget Graffiti189LongestPath.HighBoundaryClosure
open Graffiti189LongestPath.PosaOneLow Graffiti189LongestPath.SingleHeight
open Graffiti189LongestPath.OneExceptionTerminal Graffiti189LongestPath.MengerRoutable Graffiti189LongestPath.OffPathBoundaryBudget
open private Graffiti189LongestPath.Rigidity.mem_external Graffiti189LongestPath.Rigidity.mem_omittedStar from Rigidity189
open private Graffiti189LongestPath.boundary_card_of_connectivity Graffiti189LongestPath.no_endpoints Graffiti189LongestPath.pin_data from SmallSeparator189
set_option warningAsError true
set_option maxHeartbeats 3000000
namespace Graffiti189LongestPath.OversizedClosure
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Outside the already closed Hamilton-connected branch, a high vertex
with critical induced degree exists. Its ambient degree and two-pin
budget force k−floor(h/2) distinct off-path cut ports. -/
theorem oversized_critical_ports (hc : G.Connected) (k : Nat) (hk : 20≤k)
    (cap : ∀ v,(EvenFrom G v).card≤k+3)
    (conn : ∀ S : Finset V,S.card<k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (deg : ∀ u v : V,u≠v → k+2≤G.degree u ∨ k+2≤G.degree v)
    (fail : ¬∃ (u v : V) (q : G.Walk u v),q.IsPath ∧ ∀ z,z∈q.support)
    {a b x : V} {p : G.Walk a b} (hp : EdgeMinAvoid (k+2) p) (hx : x∉p.support)
    (high : k+2≤G.degree x)
    (one : (Pins p x).card=1) (sat : (External G (OmittedStar p x)).card=k+1)
    (upper : Fintype.card V≤(OmittedStar p x).card+k*(k+2)+13) :
    k≤(OmittedStar p x).card/2+(External G (OmittedStar p x)\p.support.toFinset).card := by
  classical
  let A := OmittedStar p x
  let B := External G A
  let U := univ\(A∪B)
  let J := G.induce (A : Set V)
  change B.card=k+1 at sat
  have large : k≤U.card := oversized_opposite_large hc k (by omega) cap conn deg fail hp.1.1 hx one sat
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
  have r : ∀ z∈A,z=x ∨ G.Adj x z := fun _ h =>
    (Graffiti189LongestPath.Rigidity.mem_omittedStar.mp h).2
  have h8 : 9≤A.card := by
    have q := star_card_degree_and_pins hp.1.1 hx
    change A.card+(Pins p x).card=G.degree x+1 at q
    omega
  have lob (v : V) (va : v∈A) : k+2-2≤G.degree v := by
    have vo := (Graffiti189LongestPath.Rigidity.mem_omittedStar.mp va).1
    have av : a≠v := fun e => vo (e ▸ p.start_mem_support)
    simp only [Nat.add_sub_cancel]
    rw [←G.card_neighborFinset_eq_degree]
    apply Graffiti189LongestPath.boundary_card_of_connectivity k conn (A:={v}) (a:=a)
    · exact mem_singleton_self _
    · exact fun h => av (mem_singleton.mp h)
    · exact fun h => (Graffiti189LongestPath.no_endpoints hp.1.1 vo).1 ((G.mem_neighborFinset _ _).mp h)
    · exact disjoint_left.mpr (fun _ h e => ((G.mem_neighborFinset v _).mp e).ne (mem_singleton.mp h).symm)
    · exact fun _ h _ _ e => (G.mem_neighborFinset _ _).mpr ((mem_singleton.mp h) ▸ e)
  have crit : ∃ v : ↥(A : Set V), J.degree v≤A.card/2 ∧ k+2≤G.degree v.val := by
    apply Classical.byContradiction
    intro no
    have noT (v : ↥(A : Set V)) (vd : k+2≤G.degree v.val) : A.card/2<J.degree v := by
      have e := defective_universal_shore_charge hc (k+2) k A U B conn (by omega) ab ub au large cA
        ul (fun z => distanceTwo_le_of_even (k+2) z (cap z)) r v
      change A.card+G.degree v.val+_≤2*J.degree v+(k+2)+2 at e
      have neq : ¬J.degree v≤A.card/2 := fun h => no ⟨v,h,vd⟩
      omega
    have route (u : V) (hu : u∈A) (v : V) (hv : v∈A) (ne : u≠v) :=
      defective_shore_routes_one_exception hc (k+2) k A U B conn (by omega) ab ub au
      large cA ul (fun z => distanceTwo_le_of_even (k+2) z (cap z)) r h8 lob deg noT hu hv ne
    have height : k+2≤A.card := by
      have e := star_card_degree_and_pins hp.1.1 hx
      change A.card+(Pins p x).card=G.degree x+1 at e
      omega
    have over : Fintype.card V<A.card+k+(k+1)*A.card+2*((B\p.support.toFinset).card-1) := by
      change Fintype.card V≤A.card+k*(k+2)+13 at upper
      have b := Nat.mul_le_mul_left (k+1) height
      have id : (k+1)*(k+2)=k*(k+2)+(k+2) := by rw [Nat.add_mul,one_mul]
      omega
    exact oversized_terminal_budget_impossible k (by omega) conn hp.1.1 hx (show k≤A.card by omega) (show B.card≤k+1 by omega)
      A.card (fun a ha b hb ne => by
        obtain ⟨q,qp,qs,ql⟩ := route a ha b hb ne
        exact ⟨q,qp,qs,by omega⟩) over
  obtain ⟨v,vi,vh⟩ := crit
  have vo := (Graffiti189LongestPath.Rigidity.mem_omittedStar.mp v.property).1
  have pins : (Pins p v.val).card≤2 := by
    by_cases e : (Pins p v.val).card=0
    · omega
    obtain ⟨i,hi⟩ := card_pos.mp (by omega : 0<(Pins p v.val).card)
    have q := (normalized_high_omission hc (k+2) k (by omega) le_rfl cap conn hp vo vh i hi).1
    omega
  have bd := degree_le_shore_and_ports hp.1.1 A v vo
  change G.degree v.val≤J.degree v+(Pins p v.val).card+(B\p.support.toFinset).card at bd
  change k≤A.card/2+(B\p.support.toFinset).card
  omega

/-- Universal high-connectivity closure when the second-smallest
degree is at least 36. The parity bound and connectivity are the only
graph-invariant premises; all attachment cases are discharged. -/
theorem traceable_of_high_connectivity_d36 (hc : G.Connected) (k : Nat) (hk : 34≤k)
    (cap : ∀ v,(EvenFrom G v).card≤k+3)
    (conn : ∀ S : Finset V,S.card<k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (deg : ∀ u v : V,u≠v → k+2≤G.degree u ∨ k+2≤G.degree v) :
    ∃ (u v : V) (q : G.Walk u v),q.IsPath ∧ ∀ z,z∈q.support := by
  classical
  apply Classical.byContradiction
  intro fail
  obtain ⟨a,b,p,x,hp,hx,high,one,sat,_,_⟩ := forced_oversized_single_at_d12 hc k (by omega) cap conn deg fail
  let A := OmittedStar p x
  let B := External G A
  have hmin : k+2≤A.card := by
    have e := star_card_degree_and_pins hp.1.1 hx
    change A.card+(Pins p x).card=G.degree x+1 at e
    omega
  obtain ⟨i,hi⟩ := card_pos.mp (by omega : 0<(Pins p x).card)
  have hmax : A.card≤k+4 := Nat.le_of_not_gt (fun r => fail
    (traceable_of_tall_singleton hc k (by omega) cap conn deg hp.1.1 hx one hi r))
  have rad (z : V) : G.dist x z≤4 := by
    by_contra! far
    have g := shell_card_of_far hc k conn (x:=x) (y:=z) (i:=4) (by decide) (by omega)
    have bud := Graffiti189LongestPath.SingleStar.singleton_star_budget hc k conn hp.1.1 hx one (cap x)
    have zz := ((bud.2.2.2.2.2) sat).1
    omega
  have anti (z : V) (zp : z∉p.support) (zd : k+2≤G.degree z) : (Pins p z).card≤1 := by
    by_contra! bad
    obtain ⟨j,hj⟩ := card_pos.mp (by omega : 0<(Pins p z).card)
    have bound := (normalized_high_omission hc (k+2) k (by omega) le_rfl cap conn hp zp zd j hj).1
    have exactTwo : (Pins p z).card=2 := by omega
    have none : PairedPins p z=∅ := eq_empty_iff_forall_not_mem.mpr (by
      intro j jj
      obtain ⟨jj,q,hq,eq|eq⟩ := mem_filter.mp jj
      · exact (normalized_high_omission hc (k+2) k (by omega) le_rfl cap conn hp zp zd q hq).2
          (eq.symm ▸ jj)
      · exact (normalized_high_omission hc (k+2) k (by omega) le_rfl cap conn hp zp zd j jj).2
          (eq.symm ▸ hq))
    obtain ⟨w,zw,wp⟩ := omitted_has_omitted_neighbor hc hp.1.1 zp zd ⟨_,(Graffiti189LongestPath.pin_data hj).2⟩
      (distanceTwo_le_of_even _ _ (cap z))
    exact separated_double_d12_impossible hc k (by omega) cap conn deg fail hp zp wp zw exactTwo none zd
  obtain ⟨upper,alt⟩ := oversized_single_lit_or_off_path hc k (by omega)
    cap conn hp.1.1 hx high one hmax sat rad anti deg
  have crit := oversized_critical_ports hc k (by omega) cap conn deg fail hp hx high one sat upper
  let off := (B\p.support.toFinset).card
  change k≤A.card/2+off at crit
  have up : Fintype.card V<A.card+k+(k+1)*(k-1)+2*(off-1) := by
    change Fintype.card V≤A.card+k*(k+2)+13 at upper
    change Fintype.card V+k-1≤A.card+k*(k+2)+13 ∨ k≤off+8 at alt
    have id : k+(k+1)*(k-1)+k+1=k*(k+2) := by
      have e : (k+1)*(k-1)+(k+1)=(k+1)*k := by
        calc
          _ = (k+1)*(k-1+1) := by rw [Nat.mul_add,Nat.mul_one]
          _ = _ := by rw [show k-1+1=k by omega]
      have f : (k+1)*k=k*k+k := by rw [Nat.add_mul,one_mul]
      have g : k*(k+2)=k*k+2*k := by rw [Nat.mul_add,Nat.mul_comm k 2]
      omega
    rcases alt with few|many <;> omega
  obtain ⟨v,c,cc,cl⟩ := oversized_root_deleted_long_cycle hc k (by omega) cap conn deg fail hp hx one sat high
  change 2*((A.card-1)/2-1)≤c.length at cl
  exact oversized_no_long_shore_cycle hc k (by omega) cap conn deg fail hp.1.1
    hx one sat (show 12<A.card by omega) (k-2) (show k≤A.card by omega) (by
      have h : k-2+1=k-1 := by omega
      rw [h]
      exact up) ⟨v,c,cc,by omega⟩

#print axioms oversized_critical_ports
#print axioms traceable_of_high_connectivity_d36
end Graffiti189LongestPath.OversizedClosure
