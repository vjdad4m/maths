import QuotaDense29
import VariableBlock384b
import BlockLoss384b

namespace Graffiti384b.Quota29.Finish
open Finset SimpleGraph CliqueChoice CliqueSample LowSample BlockGeometry BlockFibers Quota29.Dense
open private FiniteRange.bad FiniteRange.count_bad from FiniteRange384b
open private LowSample.delta LowSample.weight from LowSample384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def slotsAfter (h : ℕ) (f : Finset ℕ) (d j : ℕ) :=
  min (h-f.card-1) (h+slots f j Boundary.levels-29-(f.filter (· ≤ j)).card-(if d≤j then 1 else 0))
private def batch (_h : ℕ) (_f : Finset ℕ) := 11
def rebate (m b : ℕ) := 8*(m-10).choose (b-1)
private def Row (h : ℕ) (f : Finset ℕ) (d : ℕ) :=
  let m := h-f.card-1
  let b := batch h f
  9 < m ∧ 2 ≤ b ∧ d ≤ b ∧ reward m b ∧ BlockLoss.envelope m b ∧
  (∀ a : Fin 10, 3 ≤ a.val → (m-a.val).choose b + rebate m b ≤ FiniteRange.badCount m b a.val) ∧
  6*(14*m.choose b+BlockLoss.chargeAt m b (slotsAfter h f d)) <
    6*(m-b)*m.choose b + (31-h)*(6*(m-2).choose (b-2)) + 6*(∑ a ∈ f, bonus m b a) +
    6*income m b d (d-5) + 6*(d*rebate m b)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
private theorem table : ∀ h ∈ ({27,28} : Finset ℕ), ∀ f ∈ ({3,4} : Finset ℕ).powerset,
    ∀ d : Fin 9, 6 ≤ d.val → Row h f d := by
  unfold Row batch BlockLoss.chargeAt slotsAfter BlockLoss.envelope income BlockActivation.localCount LowSample.delta reward LowSample.weight FiniteRange.badCount bonus rebate slots Boundary.levels
  simp only [FiniteRange.badCount,Nat.choose_eq_fast_choose]
  decide

private theorem active_thresholds {p : Finset V} (ch : Choice G p Boundary.levels) {x : V}
    (xmem : x ∈ high G \ p) (t : (types G).card=29) (j : ℕ) (big : 3 ≤ j) :
    let s := high G \ insert x p
    (s.filter (fun z => G.degree z ≤ j)).card ≤ slotsAfter (high G).card (p.image (G.degree ·)) (G.degree x) j := by
  let S := high G \ p
  let s := high G \ insert x p
  let f := p.image (G.degree ·)
  have eq : s=S.erase x := by ext z; simp [s,S,and_assoc,and_left_comm,and_comm]
  have size : s.card=(high G).card-f.card-1 := by
    rw [eq,card_erase_of_mem xmem,card_sdiff ch.high_sub,card_image_of_injOn ch.unique]
  have prof := CliqueChoice.profile G ch j big
  dsimp only at prof
  rw [t] at prof
  change (S.filter (fun z => G.degree z ≤ j)).card+29+(f.filter (· ≤ j)).card ≤ (high G).card + slots f j Boundary.levels at prof
  have cap := card_filter_le s (fun z => G.degree z ≤ j)
  change (s.filter _).card ≤ _
  unfold slotsAfter
  apply le_min (cap.trans_eq size)
  change (s.filter _).card ≤ (high G).card+slots f j Boundary.levels-29-(f.filter (· ≤ j)).card-_
  by_cases inside : G.degree x ≤ j
  · have diff : s.filter (fun z => G.degree z ≤ j) = (S.filter (fun z => G.degree z ≤ j)).erase x := by
      ext z; simp [eq,and_assoc,and_left_comm,and_comm]
    rw [diff,card_erase_of_mem (mem_filter.mpr ⟨xmem,inside⟩),if_pos inside]
    dsimp only [S] at prof
    omega
  · rw [if_neg inside,Nat.sub_zero]
    have sub : s ⊆ S := eq ▸ erase_subset _ _
    have small := card_le_card (filter_subset_filter (fun z => G.degree z ≤ j) sub)
    omega

theorem many_nonleaves (t : (types G).card=29) (q : 31 ≤ (nonleaves G).card) : gamma G ≤ bound G := by
  by_contra! fail
  have hlim := type_bound G
  have miss : ((high G).card+1)/2 < ((types G).card+1)/2 :=
    Nat.lt_of_not_ge (fun le => (not_lt_of_ge (exact_of_high G le)) fail)
  have hh : (high G).card=27 ∨ (high G).card=28 := by omega
  letI : Nonempty V := by
    obtain ⟨v,_⟩ := card_pos.mp (show 0 < (high G).card by omega)
    exact ⟨v⟩
  obtain ⟨p,ch⟩ := choose_from G Boundary.levels (fun _ hd => (mem_Icc.mp hd).1)
  let h := (high G).card
  let f := p.image (G.degree ·)
  have hh' : h ∈ ({27,28} : Finset ℕ) := by simpa [h] using hh
  obtain ⟨x,lo,up,dense⟩ := Quota29.Dense.dense_vertex G ch t q hh fail
  let d := G.degree x
  change d ≤ cutoff h f at up
  have fp : f ⊆ ({3,4} : Finset ℕ) := by
    by_contra neg
    simp only [cutoff,if_neg neg] at up
    change 6 ≤ d at lo
    omega
  have du : d ≤ 8 := by simpa [cutoff,fp] using up
  have missing : (gaps G (G.neighborFinset x)).card ≤ d-5 := by
    have sum := gap_count G x
    change cap d < trianglesAt G x at dense
    change _ + trianglesAt G x=d.choose 2 at sum
    change 6≤d at lo
    have nums : ∀ a : Fin 9, 6 ≤ a.val → a.val.choose 2 ≤ cap a+1+(a.val-5) := by decide
    have bnd := nums ⟨d,by omega⟩ lo
    change d.choose 2 ≤ cap d+1+(d-5) at bnd
    omega
  have degP {v : V} (vp : v ∈ p) : G.degree v ≤ 4 := by
    have ok := fp (mem_image_of_mem (G.degree ·) vp)
    simp only [mem_insert,mem_singleton] at ok; omega
  have xh : x ∈ high G := mem_filter.mpr ⟨mem_univ _,by omega⟩
  have xp : x ∉ p := fun mem => by have := degP mem; omega
  let s := high G \ insert x p
  let N := G.neighborFinset x
  let m := h-f.card-1
  let b := batch h f
  have nx : N ⊆ s := by
    intro v vn
    have dg := neighbor_degree G x vn
    change d ≤ G.degree v+(gaps G N).card at dg
    change (gaps G N).card ≤ d-5 at missing
    change 6≤d at lo
    have v5 : 5 ≤ G.degree v := by omega
    refine mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _,by omega⟩,?_⟩
    intro pin
    rcases mem_insert.mp pin with rfl|vp
    · exact G.not_mem_neighborFinset_self _ vn
    · have := degP vp; omega
  have size : s.card=m := by
    dsimp only [s,m,h,f]; rw [card_sdiff (insert_subset xh ch.high_sub),card_insert_of_not_mem xp,
      card_image_of_injOn ch.unique]; omega
  have tab := table h hh' f (mem_powerset.mpr fp) ⟨d,by omega⟩ lo
  change Row h f d at tab
  obtain ⟨room,two,db,rew,env,paid,win⟩ := tab
  have balance := VariableBlock.balance G ch x xh xp nx b (d-5) two db missing (size ▸ rew) 14 (by rw [t]) fail
  let extra (v : V) := if v ∈ N then rebate m b else 0
  have outside : x ∉ s := fun mem => (mem_sdiff.mp mem).2 (mem_insert_self _ _)
  have refund (v : V) (vs : v ∈ s) :
      ((s.powersetCard b).filter (fun k => v ∈ FiniteRange.bad G s k)).card + extra v ≤ FiniteRange.badCount s.card b (min (G.degree v) 9) := by
    let a := min (G.degree v) 9
    have capA : 3 ≤ a ∧ a ≤ 9 := by
      have := (mem_filter.mp (mem_sdiff.mp vs).1).2
      dsimp [a]; omega
    by_cases vn : v ∈ N
    · have raw := BoundaryFiber.count G s b a vs outside ((G.mem_neighborFinset _ _).mp vn).symm (min_le_left _ _) (by omega)
      have bound := paid ⟨a,by omega⟩ capA.1
      change (m-a).choose b + rebate m b ≤ FiniteRange.badCount m b a at bound
      simp only [extra,if_pos vn]; rw [size] at raw ⊢
      exact (Nat.add_le_add_right raw _).trans bound
    · simp only [extra,if_neg vn,Nat.add_zero]
      exact FiniteRange.count_bad G s b a v vs (min_le_left _ _) (by omega)
  have loss := BlockLoss.pool_loss G s sdiff_subset b (slotsAfter h f d)
    (fun j _ pos => active_thresholds G ch (mem_sdiff.mpr ⟨xh,xp⟩) t j pos) extra refund (size ▸ env)
  have sumExtra : (∑ v ∈ s, extra v) = d*rebate m b := by
    simp only [extra,← sum_filter,filter_mem_eq_inter,inter_eq_right.mpr nx,sum_const,nsmul_eq_mul,Nat.cast_id]
    rw [show N.card=d from card_neighborFinset_eq_degree _ _]
  change 6*(s.card-b)*s.card.choose b + (twos G).card*(6*(s.card-2).choose (b-2)) +
    6*(∑ a ∈ f, bonus s.card b a) + 6*income s.card b d (d-5) ≤ 6*(14*s.card.choose b+∑ k ∈ s.powersetCard b,(FiniteRange.bad G s k).card) at balance
  rw [sumExtra,size] at loss
  rw [size] at balance
  change 6*(14*m.choose b+BlockLoss.chargeAt m b (slotsAfter h f d)) <
    6*(m-b)*m.choose b+(31-h)*(6*(m-2).choose (b-2))+6*(∑ a ∈ f,bonus m b a)+6*income m b d (d-5)+6*(d*rebate m b) at win
  have sub : high G ⊆ nonleaves G := fun v hv => mem_filter.mpr ⟨mem_univ _,by have := (mem_filter.mp hv).2; omega⟩
  have count : (twos G).card+h=(nonleaves G).card := card_sdiff_add_card_eq_card sub
  have low := Nat.mul_le_mul_right (6*(m-2).choose (b-2)) (show 31-h ≤ (twos G).card by omega)
  omega

end Graffiti384b.Quota29.Finish
#print axioms Graffiti384b.Quota29.Finish.many_nonleaves

