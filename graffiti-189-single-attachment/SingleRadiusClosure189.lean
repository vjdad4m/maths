import SingleRadiusShore189
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack Graffiti189LongestPath.ActiveStarHeight
open Graffiti189LongestPath.Normalize Graffiti189LongestPath.SingleRadiusCriticalOffPath
open Graffiti189LongestPath.SingleRadiusShore Graffiti189LongestPath.StarCycleClosure
open private Graffiti189LongestPath.Rigidity.mem_external Graffiti189LongestPath.Rigidity.mem_omittedStar from Rigidity189
set_option warningAsError true
set_option maxHeartbeats 4000000
namespace Graffiti189LongestPath.SingleRadiusClosure
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The single-pin normalized star of an exact-cut #189 counterexample
cannot have radius at most four when d≥11. No bound on the ambient
high root degree beyond degree≥d is used. -/
theorem single_radius_four_exact_cut_impossible (hc : G.Connected) (k : Nat) (hk : 9≤k)
    (cap : ∀ v,(EvenFrom G v).card≤k+3)
    (conn : ∀ S : Finset V,S.card<k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (deg : ∀ u v : V,u≠v → k+2≤G.degree u ∨ k+2≤G.degree v)
    (fail : ¬∃ (u v : V) (q : G.Walk u v),q.IsPath ∧ ∀ z,z∈q.support)
    {a b x : V} {p : G.Walk a b} (hp : EdgeMinAvoid (k+2) p) (hx : x∉p.support)
    (high : k+2≤G.degree x) (one : (Pins p x).card=1)
    (sat : (External G (OmittedStar p x)).card=k) (rad : ∀ z,G.dist x z≤4) : False := by
  classical
  let A := OmittedStar p x
  let T := A.erase x
  have e := star_card_degree_and_pins hp.1.1 hx
  change A.card+(Pins p x).card=G.degree x+1 at e
  have h : k+2≤A.card := by omega
  have large : 10<A.card := by omega
  have over : k*(k+2)<(k+1)*(k+1)+
      2*(External G A\p.support.toFinset).card := by
    have e : (k+1)*(k+1)=k*(k+2)+1 := by simp [Nat.add_mul,Nat.mul_add,Nat.mul_comm]; omega
    omega
  obtain ⟨r,c,cc,cl⟩ := single_root_deleted_long_cycle hc k hk cap conn deg fail hp hx one sat high
  change 2*(A.card/2-1)≤c.length at cl
  by_cases longer : k≤c.length
  · exact single_no_long_shore_cycle hc k (by omega) cap conn deg fail hp.1.1
      hx high one sat rad large k over ⟨r,c,cc,by omega⟩
  have crit := single_critical_ports hc k (by omega) cap conn deg fail hp hx high one sat rad
  change k≤A.card/2+(External G A\p.support.toFinset).card at crit
  have ord : A.card=k+2 := by omega
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
  exact single_no_marked_shore_cycle hc k (by omega) cap conn deg fail hp.1.1
    hx high one sat rad large m lim zb wz ⟨r,c,cc,by omega,miss⟩

#print axioms single_radius_four_exact_cut_impossible
end Graffiti189LongestPath.SingleRadiusClosure
