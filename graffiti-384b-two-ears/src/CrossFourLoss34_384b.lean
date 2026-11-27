import CrossFourTable34_384b
import BoundaryFiber384b

namespace Graffiti384b.CrossFour34
open Finset SimpleGraph
open private FiniteRange.bad FiniteRange.count_bad from FiniteRange384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem marked (n : Fintype.card V=34) {s : Finset V} {w b e z : V}
    (priv : G.neighborFinset w∩G.neighborFinset b={e})
    (wz : ¬G.Adj w z) (bz : ¬G.Adj b z) (ws : w∉s) (bs : b∉s) (zs : z∉s) {k : ℕ}
    (sk : s.card+k=29) :
    G.degree w+G.degree b≤(s.filter (fun v => ∃ x∉s,G.Adj v x)).card+5+k := by
  classical
  let U := G.neighborFinset w∪G.neighborFinset b
  have add := card_union_add_card_inter (G.neighborFinset w) (G.neighborFinset b)
  rw [priv,card_singleton,card_neighborFinset_eq_degree,card_neighborFinset_eq_degree] at add
  change U.card+1=_ at add
  have zu : z∉U := by simp [U,wz,bz]
  have small : U\s⊆sᶜ.erase z := fun _ vm => mem_erase.mpr
    ⟨fun eq => zu (eq ▸ (mem_sdiff.mp vm).1),mem_compl.mpr (mem_sdiff.mp vm).2⟩
  have limit := card_le_card small
  rw [card_erase_of_mem (mem_compl.mpr zs),card_compl,n] at limit
  have share : U∩s⊆s.filter (fun v => ∃ x∉s,G.Adj v x) := by
    intro v vm
    obtain ⟨inU,vs⟩ := mem_inter.mp vm
    apply mem_filter.mpr ⟨vs,?_⟩
    rcases mem_union.mp inU with h|h
    · exact ⟨w,ws,((G.mem_neighborFinset _ _).mp h).symm⟩
    · exact ⟨b,bs,((G.mem_neighborFinset _ _).mp h).symm⟩
  have parts := card_sdiff_add_card_inter U s
  have le := card_le_card share
  omega

theorem loss (s : Finset V) (sh : s⊆high G) (k : Fin 8) (sz : s.card=29-k.val)
    (room : 9<s.card) (n : Fintype.card V=34) :
    let m := 29-k.val
    (∑ T∈s.powersetCard 10,(FiniteRange.bad G s T).card)+(s.filter (fun v => ∃ x∉s,G.Adj v x)).card*refund m ≤
      charge m (fun j => (s.filter (fun v => G.degree v≤j)).card) := by
  classical
  let m := 29-k.val
  let opts := s.powersetCard 10
  let fiber (v : V) := (opts.filter (fun T => v∈FiniteRange.bad G s T)).card
  let pay (v : V) := if ∃ x∉s,G.Adj v x then refund m else 0
  have each (v : V) (vs : v∈s) : fiber v+pay v≤base m+degreeRank m (G.degree v) := by
    have low := (mem_filter.mp (sh vs)).2
    have up : G.degree v<34 := n ▸ G.degree_lt_card_verts v
    obtain ⟨_,_,bare,paid⟩ := rates k false ⟨_,up⟩ low
    let a := min (G.degree v) 9
    have num : 3≤a ∧ a≤9 := by dsimp [a]; omega
    by_cases hit : ∃ x∉s,G.Adj v x
    · obtain ⟨x,xs,vx⟩ := hit
      have yes : ∃ i∉s,G.Adj v i := ⟨x,xs,vx⟩
      have raw := BoundaryFiber.count G s 10 a vs xs vx (min_le_left ..) (by omega)
      rw [sz] at raw
      simp only [pay,if_pos yes]
      exact (Nat.add_le_add_right raw _).trans paid
    · simp only [pay,if_neg hit,Nat.add_zero]
      have raw := FiniteRange.count_bad G s 10 a v vs (min_le_left ..) (by omega)
      rw [sz] at raw
      exact raw.trans bare
  have sum := sum_le_sum each
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,Nat.cast_id] at sum
  have mass : (∑ v∈s,pay v)=(s.filter (fun v => ∃ x∉s,G.Adj v x)).card*refund m := by simp [pay,←sum_filter]
  have by_degree : (∑ v∈s,degreeRank m (G.degree v)) =
      ∑ j∈range 9,rate m j*(s.filter (fun v => G.degree v≤j)).card := by
    unfold degreeRank
    rw [sum_comm]; apply sum_congr rfl
    intro j _
    rw [←sum_filter,sum_const,nsmul_eq_mul,Nat.mul_comm]; rfl
  have by_vertex : (∑ T∈opts,(FiniteRange.bad G s T).card)=∑ v∈s,fiber v := by
    calc
      _ = ∑ T∈opts,∑ v∈s,if v∈FiniteRange.bad G s T then 1 else 0 := by
        apply sum_congr rfl; intro T _
        simp only [sum_boole,Nat.cast_id,filter_mem_eq_inter]
        rw [inter_eq_right.mpr (show FiniteRange.bad G s T⊆s from (filter_subset _ _).trans sdiff_subset)]
      _ = _ := by rw [sum_comm]; simp [fiber]
  rw [←by_vertex,mass,by_degree,sz] at sum
  exact sum
end Graffiti384b.CrossFour34
#print axioms Graffiti384b.CrossFour34.marked
#print axioms Graffiti384b.CrossFour34.loss

