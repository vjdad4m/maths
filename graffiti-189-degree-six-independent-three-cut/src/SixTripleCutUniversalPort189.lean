import SixTripleCutTerminalRank189
import SixTripleCutComponents189

namespace Graffiti189LongestPath.ThresholdSix.ThreeCut
open Finset SimpleGraph SimpleGraph.Walk
open scoped BigOperators
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

private theorem bad_terminal_low_only
    (conn : ThreeConnected G) {S : Finset V} (ss : S.card=3)
    (A : Fin 3→Finset V) (sh : ∀ i,Shore G S (A i))
    {a : V} (as' : a∈S) (bad : ¬Good G A a) :
    ∃ i,∃ s∈A i, G.Adj a s ∧ G.degree s<6 ∧
      ∀ x∈A i,G.Adj a x → G.degree x<6 := by
  classical
  have ex : ∃ i, ∀ x∈ports G (A i) a,G.degree x<6 := by
    by_contra! h
    exact bad h
  obtain ⟨i,b⟩ := ex
  obtain ⟨s,sm,sa⟩ := (sh i).hit ss conn as'
  exact ⟨i,s,sm,sa,b s (mem_filter.mpr ⟨sm,sa⟩),fun x xm ax=>b x (mem_filter.mpr ⟨xm,ax⟩)⟩

private theorem degree_le_inside_add_rank {S A : Finset V} (sh : Shore G S A)
    {x : V} (xm : x∈A) : G.degree x≤A.card-1+rank G S x := by
  have sub : G.neighborFinset x⊆A.erase x ∪ S.filter (G.Adj x) := by
    intro y ym
    have adj := (G.mem_neighborFinset ..).mp ym
    rcases sh.closed x xm y adj with ya|ys
    · exact mem_union_left _ (mem_erase.mpr ⟨adj.ne.symm,ya⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨ys,adj⟩)
  have h := (card_le_card sub).trans (card_union_le _ _)
  unfold rank
  rwa [card_neighborFinset_eq_degree,card_erase_of_mem xm] at h

private theorem sum_ranks_eq_sum_ports (S A : Finset V) :
    (∑ x∈A,rank G S x)=∑ s∈S,(ports G A s).card := by
  classical
  have counter (T : Finset V) (p : V→Prop) [DecidablePred p] :
      (T.filter p).card=(∑ v∈T,if p v then (1:Nat) else 0) := by
    rw [←sum_filter]
    simp
  simp only [rank,ports,counter]
  rw [sum_comm]
  apply sum_congr rfl
  intro s _
  apply sum_congr rfl
  intro x _
  by_cases h : G.Adj x s
  · simp [h,h.symm]
  · have k : ¬G.Adj s x := fun e=>h e.symm
    simp [h,k]

/-- If a three-vertex deletion at d=6 gives three components, at least
one vertex outside the cut sees all three cut vertices. No hypothesis
on edges inside the cut is needed. -/
theorem universal_port_of_three_shores
    (hc : G.Connected) (cap : ∀ v,(EvenFrom G v).card≤7)
    (conn : ThreeConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {S : Finset V} (ss : S.card=3) (A : Fin 3→Finset V)
    (sh : ∀ i,Shore G S (A i)) (cont : ∀ i,(G.induce (↑(A i) : Set V)).Connected)
    (dis : Pairwise fun i j=>Disjoint (A i) (A j)) :
    ∃ i,∃ x∈A i,∀ t∈S,G.Adj x t := by
  classical
  by_contra! none
  have two (i : Fin 3) (x : V) (xm : x∈A i) : rank G S x≤2 := by
    obtain ⟨t,ts,miss⟩ := none i x xm
    exact rank_le_two_of_missing ss ts miss
  have unique {x y : V} (xl : G.degree x<6) (yl : G.degree y<6) : x=y := by
    by_contra ne
    rcases degree x y ne with h|h <;> omega
  have same {i j : Fin 3} {x y : V} (xm : x∈A i) (ym : y∈A j)
      (xl : G.degree x<6) (yl : G.degree y<6) : i=j := by
    by_contra ne
    exact disjoint_left.mp (dis ne) xm ((unique xl yl).symm ▸ ym)
  have lost {a : V} (as' : a∈S) (bad : ¬Good G A a) :=
    bad_terminal_low_only conn ss A sh as' bad
  have one : ∃ a∈S,Good G A a := by
    by_cases yes : ∃ a∈S,Good G A a
    · exact yes
    exfalso
    obtain ⟨a,as'⟩ := card_pos.mp (show 0<S.card by omega)
    obtain ⟨i,x,xi,ax,xl,_⟩ := lost as' (fun h=>yes ⟨a,as',h⟩)
    obtain ⟨b,bs,bad⟩ := none i x xi
    obtain ⟨j,y,yj,by',yl,_⟩ := lost bs (fun h=>yes ⟨b,bs,h⟩)
    exact bad ((unique xl yl).symm ▸ by'.symm)
  obtain ⟨a,as',goodA⟩ := one
  have aData := good_terminal_exact_five hc cap A sh cont dis two as' goodA
  have second : ∃ b∈S,b≠a ∧ Good G A b := by
    by_cases yes : ∃ b∈S,b≠a ∧ Good G A b
    · exact yes
    exfalso
    obtain ⟨b,bs,ba⟩ := exists_ne_of_one_lt_card (by omega : 1<S.card) a
    obtain ⟨i,s,si,bs',sl,_⟩ := lost bs (fun h=>yes ⟨b,bs,ba,h⟩)
    obtain ⟨x,xp,xh⟩ := goodA i
    have xi := (mem_filter.mp xp).1
    have sub : S.filter (G.Adj x)⊆({a}:Finset V) := by
      intro t tm
      obtain ⟨ts,xt⟩ := mem_filter.mp tm
      by_cases ta : t=a
      · exact mem_singleton.mpr ta
      obtain ⟨j,v,vj,_,vl,only⟩ := lost ts (fun h=>yes ⟨t,ts,ta,h⟩)
      have eq := same si vj sl vl
      subst j
      exact (not_lt_of_ge xh (only x xi xt.symm)).elim
    have r : rank G S x≤1 := (card_le_card sub).trans (by simp)
    have cost := (sh i).port_cost_rank hc as' xp
    rw [(aData i).1,(aData i).2.1] at cost
    omega
  obtain ⟨b,bs,ba,goodB⟩ := second
  have bData := good_terminal_exact_five hc cap A sh cont dis two bs goodB
  let P := ({a,b}:Finset V)
  have ps : P⊆S := insert_subset as' (singleton_subset_iff.mpr bs)
  have p2 : P.card=2 := card_pair ba.symm
  obtain ⟨c,cm⟩ := card_pos.mp (show 0<(S\P).card by rw [card_sdiff ps,ss,p2]; decide)
  obtain ⟨cs,cp⟩ := mem_sdiff.mp cm
  have ca : c≠a := fun e=>cp (e ▸ mem_insert_self ..)
  have cb : c≠b := fun e=>cp (e ▸ mem_insert_of_mem (mem_singleton_self _))
  have sRepr : S={a,b,c} := by
    symm
    apply eq_of_subset_of_card_le (insert_subset as' (insert_subset bs (singleton_subset_iff.mpr cs)))
    rw [ss,card_insert_of_not_mem (by simp [ba.symm,ca.symm]),card_pair cb.symm]
  let p (i : Fin 3) := (ports G (A i) c).card
  have low_of_small (i : Fin 3) (pi : p i≤3) : ∃ x∈A i,G.degree x<6 := by
    by_contra! nh
    have d (x : V) (xm : x∈A i) : 2≤rank G S x := by
      have d := degree_le_inside_add_rank (sh i) xm
      have g := nh x xm
      rw [(aData i).2.2] at d
      omega
    have all := (sum_le_sum (s:=A i) (f:=fun _=>(2:Nat)) (g:=rank G S) d)
    rw [sum_ranks_eq_sum_ports S (A i),sum_const,(aData i).2.2,nsmul_eq_mul] at all
    have r : (∑ t∈S,(ports G (A i) t).card)=3+3+p i := by
      rw [sRepr,sum_insert (by simp [ba.symm,ca.symm]),sum_insert (by simpa using cb.symm),
        sum_singleton,(aData i).1,(bData i).1]
      change 3+(3+p i)=3+3+p i
      omega
    rw [r] at all
    omega
  have f (i : Fin 3) : (∑ j∈univ.erase i,p j)≤6 := by
    obtain ⟨x,xm,cx⟩ := (sh i).hit ss conn cs
    exact foreign_shore_port_sum hc cap A sh dis (mem_filter.mpr ⟨xm,cx⟩)
  have sumAll : (∑ i,p i)=p 0+p 1+p 2 := sum_fin_three p
  have adj (i : Fin 3) : (∑ j,p j)≤6+p i := by
    have t := sum_erase_add univ p (mem_univ i)
    have h := f i
    omega
  have pair : (p 0≤3 ∧ p 1≤3) ∨ (p 0≤3 ∧ p 2≤3) ∨ (p 1≤3 ∧ p 2≤3) := by
    have h0:=adj 0; have h1:=adj 1; have h2:=adj 2
    omega
  have clash {i j : Fin 3} (ne : i≠j) (pi : p i≤3) (pj : p j≤3) : False := by
    obtain ⟨x,xm,xl⟩ := low_of_small i pi
    obtain ⟨y,ym,yl⟩ := low_of_small j pj
    exact ne (same xm ym xl yl)
  rcases pair with ⟨p0,p1⟩|⟨p0,p2⟩|⟨p1,p2⟩
  · exact clash (show (0:Fin 3)≠1 by decide) p0 p1
  · exact clash (show (0:Fin 3)≠2 by decide) p0 p2
  · exact clash (show (1:Fin 3)≠2 by decide) p1 p2

theorem universal_port_of_three_components
    (hc : G.Connected) (cap : ∀ v,(EvenFrom G v).card≤7) (conn : ThreeConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {S : Finset V} (ss : S.card=3) (big : 3≤Nat.card (Removed G S).ConnectedComponent) :
    ∃ x∉S,∀ t∈S,G.Adj x t := by
  classical
  let C := (Removed G S).ConnectedComponent
  letI : Finite C := Finite.of_surjective (Removed G S).connectedComponentMk (fun y => y.exists_rep)
  letI : Fintype C := Fintype.ofFinite C
  have c : 3≤Fintype.card C := by
    change 3≤Nat.card C at big
    rwa [Nat.card_eq_fintype_card] at big
  let f : Fin 3 ↪ C := (Fin.castLEEmb c).trans (Fintype.equivFin C).symm.toEmbedding
  let A (i : Fin 3) := shoreSet (f i)
  obtain ⟨i,x,xm,h⟩ := universal_port_of_three_shores hc cap conn degree ss A
    (fun i=>shoreSet_shore (f i)) (fun i=>shoreSet_connected (f i))
    (fun _ _ ne=>shoreSet_disjoint (f.injective.ne ne))
  exact ⟨x,(mem_shoreSet.mp xm).choose,h⟩

#print axioms universal_port_of_three_shores
#print axioms universal_port_of_three_components
end Graffiti189LongestPath.ThresholdSix.ThreeCut
