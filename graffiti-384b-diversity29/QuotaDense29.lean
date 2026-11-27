import ExposedQuota29
import QuotaFiber29

namespace Graffiti384b.Quota29.Dense
open Finset SimpleGraph CliqueChoice CliqueSample LowSample
open private Repair.triangles_le_choose from Repair384b
open private FiniteRange.bad FiniteRange.count_bad from FiniteRange384b
open private LowSample.delta LowSample.weight from LowSample384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def cutoff (_h : ℕ) (f : Finset ℕ) := if f ⊆ ({3,4} : Finset ℕ) then 8 else 0
def cap (d : ℕ) := if d=6 then 13 else if d=7 then 18 else if d=8 then 24 else d.choose 2
def limit (h : ℕ) (f : Finset ℕ) (j : ℕ) :=
  let a := slots f j Boundary.levels
  let n := if j≤cutoff h f then min a (cap j+1) else a
  min (h-f.card) (h+n-29-(f.filter (· ≤ j)).card)

private def batch (h : ℕ) (f : Finset ℕ) := if 21≤h-f.card then 11 else 10
def rebate (m b : ℕ) := 8*(m-10).choose (b-1)
def needed (h : ℕ) := if h=27 then 5 else 4
private def Row (h : ℕ) (f : Finset ℕ) :=
  let m := h-f.card
  let b := batch h f
  12 ≤ m ∧ 2 ≤ b ∧ BlockLoss.envelope m b ∧ reward m b ∧
    (∀ a : Fin 10, 3≤a.val → (m-a.val).choose b+rebate m b≤FiniteRange.badCount m b a.val) ∧
    6*(14*m.choose b + BlockLoss.chargeAt m b (limit h f)) <
    6*(m-b)*m.choose b + (31-h)*(6*(m-2).choose (b-2)) + 6*(∑ d ∈ f, bonus m b d)+6*(needed h*rebate m b)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem rows : ∀ h ∈ ({27,28} : Finset ℕ), ∀ f ∈ Boundary.levels.powerset, Row h f := by
  unfold Row batch limit cutoff cap BlockLoss.chargeAt BlockLoss.envelope reward needed rebate LowSample.delta LowSample.weight bonus slots Boundary.levels FiniteRange.badCount
  simp only [FiniteRange.badCount,Nat.choose_eq_fast_choose]
  decide

private theorem mono : ∀ d j : Fin 9, d.val ≤ j.val → cap d ≤ cap j := by decide

private theorem distribution {p : Finset V} (ch : Choice G p Boundary.levels) (t : (types G).card=29)
    (localBound : ∀ v, G.degree v ≤ cutoff (high G).card (p.image (G.degree ·)) → trianglesAt G v ≤ cap (G.degree v))
    (j : ℕ) (hj : 3 ≤ j) :
    ((high G \ p).filter (fun v => G.degree v ≤ j)).card ≤ limit (high G).card (p.image (G.degree ·)) j := by
  let h := (high G).card
  let f := p.image (G.degree ·)
  let s := high G \ p
  let a := (high G).filter (fun v => G.degree v ≤ j)
  let b := p.filter (fun v => G.degree v ≤ j)
  have size : s.card=h-f.card := by dsimp [s,h,f]; rw [card_image_of_injOn ch.unique,card_sdiff ch.high_sub]
  have prof := CliqueChoice.profile G ch j hj
  dsimp only at prof
  rw [t] at prof
  change (s.filter _).card+29+(f.filter (· ≤ j)).card ≤ h+slots f j Boundary.levels at prof
  have count := card_filter_le s (fun v => G.degree v ≤ j)
  change (s.filter _).card ≤ _
  unfold limit
  change (s.filter (fun v => G.degree v ≤ j)).card ≤ min (h-f.card) (h+(if j≤cutoff h f then min (slots f j Boundary.levels) (cap j+1) else slots f j Boundary.levels) -29-(f.filter (· ≤ j)).card)
  apply le_min (count.trans_eq size)
  split_ifs with small
  · have j9 : j<9 := by unfold cutoff at small; split_ifs at small <;> omega
    have cover : types G ⊆ ((high G)\a).image (trianglesAt G) ∪ range (cap j+1) := by
      intro z hz
      obtain ⟨v,_,rfl⟩ := mem_image.mp hz
      by_cases vd : G.degree v ≤ j
      · apply mem_union_right
        apply mem_range.mpr
        have bounded := localBound v (vd.trans small)
        have step := mono ⟨G.degree v,by omega⟩ ⟨j,j9⟩ vd
        exact Nat.lt_succ_of_le (bounded.trans step)
      · apply mem_union_left
        exact mem_image.mpr ⟨v,mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _,by omega⟩,
          fun eq => vd (mem_filter.mp eq).2⟩,rfl⟩
    have possible := (card_le_card cover).trans (card_union_le _ _)
    rw [t,card_range] at possible
    have distinct := card_image_le (s := high G \ a) (f := trianglesAt G)
    have total : (high G \ a).card+a.card=h := card_sdiff_add_card_eq_card (filter_subset _ _)
    have sub : b ⊆ a := fun w hw => mem_filter.mpr ⟨ch.high_sub (mem_filter.mp hw).1,(mem_filter.mp hw).2⟩
    have eq : s.filter (fun v => G.degree v ≤ j) = a\b := by ext v; simp only [s,a,b,mem_filter,mem_sdiff]; tauto
    have im : b.image (G.degree ·) = f.filter (· ≤ j) := by ext d; simp [b,f]; aesop
    have bs : b.card=(f.filter (· ≤ j)).card := by
      rw [← im,card_image_of_injOn (ch.unique.mono (show (b : Set V) ⊆ p from filter_subset _ _))]
    have join := card_sdiff_add_card_eq_card sub
    rw [← eq,bs] at join
    omega
  · omega

/-- At diversity 29 with at least 31 nonleaves, all remaining saturated representatives have degree
at most four and there is a common dense center of degree six to eight. -/
theorem dense_vertex {p : Finset V} (ch : Choice G p Boundary.levels)
    (t : (types G).card=29) (q : 31 ≤ (nonleaves G).card)
    (hh : (high G).card=27 ∨ (high G).card=28) (fail : bound G < gamma G) :
    ∃ v, 6 ≤ G.degree v ∧ G.degree v ≤ cutoff (high G).card (p.image (G.degree ·)) ∧
      cap (G.degree v) < trianglesAt G v := by
  let h := (high G).card
  let f := p.image (G.degree ·)
  let m := h-f.card
  let b := batch h f
  have mem : h ∈ ({27,28} : Finset ℕ) := by simpa [h] using hh
  obtain ⟨room,two,env,rew,paid,win⟩ := rows h mem f (mem_powerset.mpr ch.levels)
  change 12 ≤ m at room
  by_contra! no
  have localBound (v : V) (deg : G.degree v ≤ cutoff h f) : trianglesAt G v ≤ cap (G.degree v) := by
    by_cases six : 6 ≤ G.degree v
    · exact no v six deg
    · simpa [cap,show G.degree v≠6 by omega,show G.degree v≠7 by omega,show G.degree v≠8 by omega] using
        Repair.triangles_le_choose G v
  have size : (high G \ p).card=m := by dsimp [m,h,f]; rw [card_image_of_injOn ch.unique,card_sdiff ch.high_sub]
  obtain ⟨E,subE,countE,cross⟩ := Quota29.exposed G ch t q hh fail
  let S := high G\p
  let extra (v : V) := if v∈E then rebate m b else 0
  have refund (v : V) (vs : v∈S) :
      ((S.powersetCard b).filter (fun k => v∈FiniteRange.bad G S k)).card+extra v≤
        FiniteRange.badCount S.card b (min (G.degree v) 9) := by
    let a := min (G.degree v) 9
    have a3 : 3≤a := le_min (mem_filter.mp (mem_sdiff.mp vs).1).2 (by decide)
    have a9 : a≤9 := min_le_right ..
    by_cases ve : v∈E
    · obtain ⟨w,ws,edge⟩ := cross v ve
      have raw := BoundaryFiber.count G S b a vs ws edge (min_le_left _ _) (by omega)
      have pb := paid ⟨a,by omega⟩ a3
      change (m-a).choose b+rebate m b≤FiniteRange.badCount m b a at pb
      change S.card=m at size
      rw [size] at raw ⊢
      simpa only [extra,if_pos ve] using (Nat.add_le_add_right raw _).trans pb
    · simp only [extra,if_neg ve,Nat.add_zero]
      exact FiniteRange.count_bad G S b a v vs (min_le_left _ _) (by change S.card=m at size; omega)
  have obs := Quota29.Sample.extraObstruction G ch b (limit h f) (fun j _ pos => distribution G ch t localBound j pos)
    extra refund two (size ▸ env) (size ▸ rew) fail
  have sumE : (∑ v∈S,extra v)=E.card*rebate m b := by
    simp only [extra,←sum_filter,filter_mem_eq_inter,inter_eq_right.mpr (show E⊆S from subE),sum_const,nsmul_eq_mul,Nat.cast_id]
  dsimp only at obs
  rw [t] at obs
  change 6*(m-b)*m.choose b + (twos G).card*(6*(m-2).choose (b-2)) + 6*(∑ d∈f,bonus m b d)+6*(∑ v∈S,extra v)≤
    6*(14*m.choose b+BlockLoss.chargeAt m b (limit h f)) at obs
  rw [sumE] at obs
  change 6*(14*m.choose b+BlockLoss.chargeAt m b (limit h f)) <
    6*(m-b)*m.choose b+(31-h)*(6*(m-2).choose (b-2))+6*(∑ d∈f,bonus m b d)+6*(needed h*rebate m b) at win
  change needed h≤E.card at countE
  have cr := Nat.mul_le_mul_right (rebate m b) countE
  have sub : high G ⊆ nonleaves G := by
    intro v hv; exact mem_filter.mpr ⟨mem_univ _,by have := (mem_filter.mp hv).2; omega⟩
  have sum : (twos G).card+h=(nonleaves G).card := card_sdiff_add_card_eq_card sub
  have val := Nat.mul_le_mul_right (6*(m-2).choose (b-2)) (show 31-h ≤ (twos G).card by omega)
  omega

end Graffiti384b.Quota29.Dense
#print axioms Graffiti384b.Quota29.Dense.dense_vertex

