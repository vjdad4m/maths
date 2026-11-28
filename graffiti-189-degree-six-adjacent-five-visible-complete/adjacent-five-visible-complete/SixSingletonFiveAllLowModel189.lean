import SixSingletonFiveAllLowWalk189
import SixSingletonFiveThreeTinyTail189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair PortCertificates PortCertificates.AllLow
open private three_common_model from SixSingletonFiveThreeTinyTail189
open private d8 p5 from SixSingletonFiveShallowRoute189
variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000

def allLowLabel (z w h : V) : Fin 11→V := ![5,6,7,z,w,h,0,1,2,3,4]

private theorem score_list (u : V) (l : List V) (nodup : l.Nodup) :
    (inside G l.toFinset u).card=(l.map (fun t=>marks (decide (G.Adj u t)))).sum := by
  induction l with
  | nil => simp [inside]
  | cons v l ih =>
    have nn := List.nodup_cons.mp nodup
    rw [List.toFinset_cons,inside_insert_score (G:=G) (by simpa using nn.1),ih nn.2]
    simp [Nat.add_comm]

private theorem mark_symm (u v : V) :
    marks (decide (G.Adj u v))=marks (decide (G.Adj v u)) := by
  have d : decide (G.Adj u v)=decide (G.Adj v u) := by
    congr 1
    exact propext ⟨Adj.symm,Adj.symm⟩
  exact congrArg marks d

private theorem low_ports_bound {L R S : Finset V} {T z : V} (F : ProfileThree G L R S T)
    (zd : z∈D) (n : ℕ) (low : (inside G D z).card≤n) :
    6-n≤(inside G P z).card := by
  have sub : G.neighborFinset z⊆inside G D z∪inside G P z := by
    intro u um
    have j := (mem_neighborFinset _ _ _).mp um
    exact (mem_union.mp (F.darkBounds z zd u j)).elim
      (fun m=>mem_union_left _ (mem_filter.mpr ⟨m,j⟩))
      (fun m=>mem_union_right _ (mem_filter.mpr ⟨m,j⟩))
  have k := card_le_card sub
  rw [card_neighborFinset_eq_degree] at k
  have p := card_union_le (inside G D z) (inside G P z)
  have q := F.darkHigh z zd
  omega

private theorem common_port_bound {L R S : Finset V} {T c : V} (F : ProfileThree G L R S T)
    (ck : c∈K) : 2≤(inside G (K∪(D\S)) c).card := by
  have sub : G.neighborFinset c⊆insert a (insert b (insert x (insert y (inside G (K∪(D\S)) c)))) := by
    intro u um
    have e := (mem_neighborFinset _ _ _).mp um
    rcases mem_insert.mp (F.commonBounds c ck u e) with h|h
    · exact mem_insert.mpr (.inl h)
    rcases mem_insert.mp h with h|h
    · exact mem_insert_of_mem (mem_insert.mpr (.inl h))
    apply mem_insert_of_mem
    apply mem_insert_of_mem
    rcases mem_union.mp h with h|h
    · rcases mem_insert.mp h with h|h
      · exact mem_insert.mpr (.inl h)
      rcases mem_insert.mp h with h|h
      · exact mem_insert_of_mem (mem_insert.mpr (.inl h))
      exact mem_insert_of_mem (mem_insert_of_mem (mem_filter.mpr ⟨mem_union_left _ h,e⟩))
    exact mem_insert_of_mem (mem_insert_of_mem (mem_filter.mpr ⟨mem_union_right _ h,e⟩))
  have q := card_le_card sub
  rw [card_neighborFinset_eq_degree] at q
  let U := inside G (K∪(D\S)) c
  change G.degree c≤(insert a (insert b (insert x (insert y U)))).card at q
  have a := card_insert_le a (insert b (insert x (insert y U)))
  have b := card_insert_le b (insert x (insert y U))
  have x := card_insert_le x (insert y U)
  have y := card_insert_le y U
  have g := F.commonHigh c ck
  change 2≤U.card
  omega

private theorem norm_three_distinct {z w h : V}
    (zD : z∈D) (wD : w∈D) (hD : h∈D) (zw : z≠w) (zh : z≠h) (wh : w≠h) :
    ([5,6,7,z,w,h] : List V).Nodup := by
  have ne (u : V) (ud : u∈D) : 5≠u ∧ 6≠u ∧ 7≠u := by
    refine ⟨?_,?_,?_⟩
    · exact fun e=>(by decide : (5:V)∉D) (e.symm ▸ ud)
    · exact fun e=>(by decide : (6:V)∉D) (e.symm ▸ ud)
    · exact fun e=>(by decide : (7:V)∉D) (e.symm ▸ ud)
  obtain ⟨az,bz,cz⟩ := ne z zD
  obtain ⟨aw,bw,cw⟩ := ne w wD
  obtain ⟨ah,bh,ch⟩ := ne h hD
  simp [List.nodup_cons,az,bz,cz,aw,bw,cw,ah,bh,ch,zw,zh,wh]

private theorem common_fold {z w h c : V}
    (zD : z∈D) (wD : w∈D) (hD : h∈D) (zw : z≠w) (zh : z≠h) (wh : w≠h) :
    (inside G (K∪({z,w,h}:Finset V)) c).card=
      marks (decide (G.Adj c 5))+marks (decide (G.Adj c 6))+marks (decide (G.Adj c 7))+
      marks (decide (G.Adj c z))+marks (decide (G.Adj c w))+marks (decide (G.Adj c h)) := by
  have e : ([5,6,7,z,w,h] : List V).toFinset=K∪({z,w,h}:Finset V) := by
    ext u
    simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false,K,mem_union,mem_insert,mem_singleton]
    tauto
  have f := score_list (G:=G) c [5,6,7,z,w,h] (norm_three_distinct zD wD hD zw zh wh)
  rw [e] at f
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] at f
  omega

private theorem port_fold (c : V) :
    (inside G P c).card=
      marks (decide (G.Adj c 5))+marks (decide (G.Adj c 6))+marks (decide (G.Adj c 7))+
      marks (decide (G.Adj c x))+marks (decide (G.Adj c y)) := by
  have e : ([5,6,7,x,y]:List V).toFinset=P := by decide
  have f := score_list (G:=G) c [5,6,7,x,y] (by decide)
  rw [e] at f
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] at f
  omega

private theorem all_low_port_model {L R S : Finset V} {T z w h : V} (F : ProfileThree G L R S T)
    (hc : G.Connected) (even : ∀ u,(EvenFrom G u).card≤7)
    (zm : z∈D\S) (wm : w∈D\S) (hm : h∈D\S)
    (zw : z≠w) (zh : z≠h) (wh : w≠h)
    (W : D\S={z,w,h})
    (zl : (inside G D z).card≤2) (wl : (inside G D w).card≤3) (hl : (inside G D h).card≤3) :
    PortModel (bitGraph G (allLowLabel z w h)) := by
  have m := three_common_model (common_three_balances_nonisolated F hc even)
  have zd := (mem_sdiff.mp zm).1
  have wd := (mem_sdiff.mp wm).1
  have hd := (mem_sdiff.mp hm).1
  refine ⟨m.1,m.2.1,m.2.2,?_,?_,?_,?_,?_,?_⟩
  · have p := common_port_bound F (c:=5) (by decide)
    rw [W,common_fold zd wd hd zw zh wh] at p
    have e : marks (decide (G.Adj (5:V) 5))=0 := by simp [G.loopless,marks]
    rw [e] at p
    simpa only [Nat.zero_add,Nat.add_zero] using p
  · have p := common_port_bound F (c:=6) (by decide)
    rw [W,common_fold zd wd hd zw zh wh] at p
    have e : marks (decide (G.Adj (6:V) 6))=0 := by simp [G.loopless,marks]
    rw [e,mark_symm (6:V) 5] at p
    simpa only [Nat.zero_add,Nat.add_zero] using p
  · have p := common_port_bound F (c:=7) (by decide)
    rw [W,common_fold zd wd hd zw zh wh] at p
    have e : marks (decide (G.Adj (7:V) 7))=0 := by simp [G.loopless,marks]
    rw [e,mark_symm (7:V) 5,mark_symm (7:V) 6] at p
    simpa only [Nat.zero_add,Nat.add_zero] using p
  · have p := low_ports_bound F zd 2 zl
    rw [port_fold,mark_symm z 5,mark_symm z 6,mark_symm z 7] at p
    exact p
  · have p := low_ports_bound F wd 3 wl
    rw [port_fold,mark_symm w 5,mark_symm w 6,mark_symm w 7] at p
    exact p
  · have p := low_ports_bound F hd 3 hl
    rw [port_fold,mark_symm h 5,mark_symm h 6,mark_symm h 7] at p
    exact p

#print axioms all_low_port_model
end Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
