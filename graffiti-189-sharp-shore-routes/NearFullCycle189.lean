import MarkedShoreCycle189
import CycleInsert189
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.MarkedShoreCycle Graffiti189LongestPath.StarCycleClosure
open Graffiti189LongestPath.CycleInsert
open private Graffiti189LongestPath.boundary_card_of_connectivity Graffiti189LongestPath.no_endpoints from SmallSeparator189
open private Graffiti189LongestPath.Rigidity.mem_omittedStar Graffiti189LongestPath.Rigidity.mem_external from Rigidity189
set_option warningAsError true
set_option maxHeartbeats 3000000
namespace Graffiti189LongestPath.NearFullCycle
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- At minimum height, a cycle missing at most one vertex of the root-deleted
shore is enough. If that vertex has a cut neighbor, select it as a hook root;
otherwise it is universal in the shore and can be inserted into the cycle. -/
theorem minimum_height_no_near_full_cycle (hc : G.Connected) (k : Nat) (hk : 6≤k)
    (cap : ∀ v,(EvenFrom G v).card≤k+3)
    (conn : ∀ D : Finset V,D.card<k → (G.induce ((↑D : Set V)ᶜ)).Connected)
    (deg : ∀ u v : V,u≠v → k+2≤G.degree u ∨ k+2≤G.degree v)
    (fail : ¬∃ (u v : V) (q : G.Walk u v),q.IsPath ∧ ∀ w,w∈q.support)
    {a b x y : V} {p : G.Walk a b} (hp : IsLongest p)
    (hx : x∉p.support) (hy : y∉p.support) (xy : G.Adj x y)
    (high : k+2≤G.degree x)
    (double : (Pins p x).card=2) (sep : PairedPins p x=∅)
    (large : 10<(OmittedStar p x).card) (height : (OmittedStar p x).card=k+1)
    (pay : k≤2*(External G (OmittedStar p x)\p.support.toFinset).card+1)
    (cyc : ∃ a, ∃ c : (G.induce (((OmittedStar p x).erase x : Finset V) : Set V)).Walk a a,
      c.IsCycle ∧ max 2 (k-1)≤c.length) : False := by
  classical
  let A := OmittedStar p x
  let T := A.erase x
  let J := G.induce (T : Set V)
  have over : k*(k+2)<(k+1)*(k+1)+
      2*(External G (OmittedStar p x)\p.support.toFinset).card := by
    have e : (k+1)*(k+1)=k*(k+2)+1 := by simp [Nat.add_mul,Nat.mul_add,Nat.mul_comm]; omega
    omega
  obtain ⟨r,c,cc,cl⟩ := cyc
  by_cases grow : k≤c.length
  · exact separated_double_no_long_shore_cycle hc k hk cap conn deg fail hp
      hx hy xy high double sep large k over ⟨r,c,cc,by omega⟩
  change A.card=k+1 at height
  have xa : x∈A := Graffiti189LongestPath.Rigidity.mem_omittedStar.mpr ⟨hx,Or.inl rfl⟩
  have tt : T.card=k := by rw [card_erase_of_mem xa,height,Nat.add_sub_cancel]
  let inc : ↥(T : Set V) ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  let D := c.support.toFinset.map inc
  have sub : D⊆T := by
    intro v hv
    obtain ⟨z,_,rfl⟩ := mem_map.mp hv
    exact z.property
  have dc : D.card=c.length := by rw [card_map,cycle_card_support c cc]
  have small : 0<(T\D).card := by
    have e := card_sdiff_add_card_eq_card sub
    omega
  obtain ⟨w,wd⟩ := card_pos.mp small
  obtain ⟨wt,wn⟩ := mem_sdiff.mp wd
  let m : ↥(T : Set V) := ⟨w,wt⟩
  have miss : m∉c.support := fun e =>
    wn (mem_map.mpr ⟨m,List.mem_toFinset.mpr e,rfl⟩)
  by_cases port : ∃ z∈External G A,G.Adj w z
  · obtain ⟨z,zb,wz⟩ := port
    exact separated_double_no_marked_shore_cycle hc k hk cap conn deg fail
      hp hx hy xy high double sep large m pay zb wz ⟨r,c,cc,cl,miss⟩
  have wa : w∈A := (mem_erase.mp wt).2
  have off : w∉p.support := (Graffiti189LongestPath.Rigidity.mem_omittedStar.mp wa).1
  let N := G.neighborFinset w
  have dN : k≤N.card := by
    have aw : a≠w := fun e => off (e ▸ p.start_mem_support)
    apply Graffiti189LongestPath.boundary_card_of_connectivity k conn (A:={w}) (a:=a)
      (mem_singleton_self _)
    · exact fun h => aw (mem_singleton.mp h)
    · exact fun h => (Graffiti189LongestPath.no_endpoints hp off).1
        ((G.mem_neighborFinset _ _).mp h)
    · exact disjoint_left.mpr (fun _ h h' => ((G.mem_neighborFinset _ _).mp h').ne
        (mem_singleton.mp h).symm)
    · intro u hu v _ e
      exact (G.mem_neighborFinset _ _).mpr ((mem_singleton.mp hu) ▸ e)
  have cov : N⊆A.erase w := by
    intro z hz
    have edge := (G.mem_neighborFinset _ _).mp hz
    refine mem_erase.mpr ⟨edge.ne.symm,?_⟩
    apply Classical.byContradiction
    intro zn
    exact port ⟨z,Graffiti189LongestPath.Rigidity.mem_external.mpr ⟨zn,w,wa,edge⟩,edge⟩
  have q := card_erase_of_mem wa
  have eq : N=A.erase w := eq_of_subset_of_card_le cov (by omega)
  have whole : ∀ v∈c.support,J.Adj m v := by
    intro v vc
    have ne : v.val≠w := by
      intro e
      have vm : v=m := Subtype.ext (show v.val=m.val from e)
      exact miss (vm ▸ vc)
    have va : v.val∈A := (mem_erase.mp v.property).2
    change G.Adj w v.val
    apply (G.mem_neighborFinset _ _).mp
    rw [show G.neighborFinset w=N from rfl,eq]
    exact mem_erase.mpr ⟨ne,va⟩
  obtain ⟨C,CC,CL,_⟩ := insert_after_start c cc miss whole
  exact separated_double_no_long_shore_cycle hc k hk cap conn deg fail hp
    hx hy xy high double sep large k over ⟨r,C,CC,by omega⟩

#print axioms minimum_height_no_near_full_cycle
end Graffiti189LongestPath.NearFullCycle
