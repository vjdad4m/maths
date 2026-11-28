import CriticalOffPath189
import NearFullCycle189
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack Graffiti189LongestPath.ActiveStarHeight
open Graffiti189LongestPath.Normalize Graffiti189LongestPath.CriticalOffPath
open Graffiti189LongestPath.NearFullCycle Graffiti189LongestPath.MarkedShoreCycle Graffiti189LongestPath.StarCycleClosure
open private Graffiti189LongestPath.Rigidity.mem_external Graffiti189LongestPath.Rigidity.mem_omittedStar from Rigidity189
set_option warningAsError true
set_option maxHeartbeats 4000000
namespace Graffiti189LongestPath.DiracThreshold
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Apart from the odd minimum-height structural case, the ordinary
Dirac-length shore cycle alone is now enough. The existence of that
cycle, not a prescribed-endpoint path theorem, is the only extra premise. -/
theorem separated_double_no_dirac_cycle (hc : G.Connected) (k : Nat) (hk : 7≤k)
    (cap : ∀ v,(EvenFrom G v).card≤k+3)
    (conn : ∀ S : Finset V,S.card<k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (deg : ∀ u v : V,u≠v → k+2≤G.degree u ∨ k+2≤G.degree v)
    (fail : ¬∃ (u v : V) (q : G.Walk u v),q.IsPath ∧ ∀ z,z∈q.support)
    {a b x y : V} {p : G.Walk a b} (hp : EdgeMinAvoid (k+2) p) (hx : x∉p.support)
    (hy : y∉p.support) (xy : G.Adj x y)
    (double : (Pins p x).card=2) (sep : PairedPins p x=∅)
    (high : k+2≤G.degree x)
    (large : 10<(OmittedStar p x).card)
    (odd_min : (OmittedStar p x).card=k+1 → (OmittedStar p x).card%2=0)
    (cyc : ∃ a, ∃ c : (G.induce (((OmittedStar p x).erase x : Finset V) : Set V)).Walk a a,
      c.IsCycle ∧ 2*((OmittedStar p x).card/2-1)≤c.length) : False := by
  classical
  let A := OmittedStar p x
  let T := A.erase x
  have e := star_card_degree_and_pins hp.1.1 hx
  change A.card+(Pins p x).card=G.degree x+1 at e
  have h : k+1≤A.card := by omega
  have over : k*(k+2)<(k+1)*(k+1)+
      2*(External G A\p.support.toFinset).card := by
    have e : (k+1)*(k+1)=k*(k+2)+1 := by simp [Nat.add_mul,Nat.mul_add,Nat.mul_comm]; omega
    omega
  obtain ⟨r,c,cc,cl⟩ := cyc
  change 2*(A.card/2-1)≤c.length at cl
  by_cases longer : k≤c.length
  · exact separated_double_no_long_shore_cycle hc k (by omega) cap conn deg fail hp.1.1
      hx hy xy high double sep large k over ⟨r,c,cc,by omega⟩
  have crit := separated_double_critical_ports hc k hk cap conn deg fail hp hx hy xy double sep high
  change k≤A.card/2+(External G A\p.support.toFinset).card at crit
  by_cases min : A.card=k+1
  · have even := odd_min min
    change A.card%2=0 at even
    have lim : k≤2*(External G A\p.support.toFinset).card+1 := by omega
    exact minimum_height_no_near_full_cycle hc k (by omega) cap conn deg fail
      hp.1.1 hx hy xy high double sep large min lim ⟨r,c,cc,by omega⟩
  have ord : A.card=k+2 := by omega
  have odd : A.card%2=1 := by omega
  have lim : k≤2*(External G A\p.support.toFinset).card+1 := by omega
  have xa : x∈A := Graffiti189LongestPath.Rigidity.mem_omittedStar.mpr ⟨hx,Or.inl rfl⟩
  have tt : T.card=k+1 := by rw [card_erase_of_mem xa,ord]; omega
  let inc : ↥(T : Set V) ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  let D := c.support.toFinset.map inc
  have sub : D⊆T := by
    intro v hv
    obtain ⟨z,_,rfl⟩ := mem_map.mp hv
    exact z.property
  have dc : D.card=c.length := by rw [card_map,cycle_card_support c cc]
  have small : 1<(T\D).card := by
    have e := card_sdiff_add_card_eq_card sub
    omega
  obtain ⟨u,ud,v,vd,ne⟩ := one_lt_card.mp small
  have goods : ∃ w∈T\D,k+2≤G.degree w :=
    (deg u v ne).elim (fun e => ⟨u,ud,e⟩) (fun e => ⟨v,vd,e⟩)
  obtain ⟨w,wd,wh⟩ := goods
  obtain ⟨wt,wn⟩ := mem_sdiff.mp wd
  have wa : w∈A := (mem_erase.mp wt).2
  let m : ↥(T : Set V) := ⟨w,wt⟩
  have miss : m∉c.support := fun e => wn (mem_map.mpr ⟨m,List.mem_toFinset.mpr e,rfl⟩)
  have port : ∃ z∈External G A,G.Adj w z := by
    apply Classical.byContradiction
    intro no
    have nb : G.neighborFinset w⊆A.erase w := by
      intro z hz
      have edge := (G.mem_neighborFinset _ _).mp hz
      refine mem_erase.mpr ⟨edge.ne.symm,?_⟩
      apply Classical.byContradiction
      intro zn
      exact no ⟨z,Graffiti189LongestPath.Rigidity.mem_external.mpr ⟨zn,w,wa,edge⟩,edge⟩
    have b := card_le_card nb
    rw [G.card_neighborFinset_eq_degree,card_erase_of_mem wa] at b
    omega
  obtain ⟨z,zb,wz⟩ := port
  exact separated_double_no_marked_shore_cycle hc k (by omega) cap conn deg fail hp.1.1
    hx hy xy high double sep large m lim zb wz ⟨r,c,cc,by omega,miss⟩

#print axioms separated_double_no_dirac_cycle
end Graffiti189LongestPath.DiracThreshold
