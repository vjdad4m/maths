import CliqueSample384b

namespace Graffiti384b.Diversity30
open Finset SimpleGraph CliqueSample CliqueChoice LowSample
open private LowSample.delta LowSample.weight from LowSample384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The tested degrees are 3, 4, 5 and 6. Include one representative
of each realized saturated degree and sample eleven more vertices. -/
def Row (f : Finset ℕ) : Prop :=
  let m := 28-f.card
  12≤m ∧ envelope m 11 ∧ reward m 11 ∧
    6*(14*m.choose 11+charge 30 28 m 11 f) <
      6*(m-11)*m.choose 11+2*(6*(m-2).choose 9)+6*(∑ d∈f,bonus m 11 d)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem rows : ∀ f∈degrees.powerset,Row f := by
  unfold Row degrees envelope reward charge LowSample.delta LowSample.weight bonus slots FiniteRange.badCount
  simp only [FiniteRange.badCount,Nat.choose_eq_fast_choose]
  decide

/-- Thirty types and at least thirty nonleaves suffice, regardless of
graph order or connectivity. -/
theorem many_nonleaves (t : (types G).card=30) (q : 30≤(nonleaves G).card) : gamma G≤bound G := by
  classical
  by_contra! fail
  have lim := type_bound G
  have miss : ((high G).card+1)/2<((types G).card+1)/2 :=
    Nat.lt_of_not_ge (fun le => (not_lt_of_ge (exact_of_high G le)) fail)
  have h : (high G).card=28 := by omega
  letI : Nonempty V := by
    obtain ⟨z,_⟩ := card_pos.mp (show 0<(high G).card by omega)
    exact ⟨z⟩
  obtain ⟨p,ch⟩ := choose_from G degrees (by intro d dm; simp [degrees] at dm; omega)
  let f := p.image (G.degree ·)
  let m := 28-f.card
  obtain ⟨room,env,rew,win⟩ := rows f (mem_powerset.mpr ch.levels)
  have sz : (high G\p).card=m := by
    dsimp [m,f]; rw [card_image_of_injOn ch.unique,card_sdiff ch.high_sub,h]
  have obs := CliqueSample.obstruction G ch 11 (sz ▸ room) (by decide) (sz ▸ env) (sz ▸ rew) fail
  dsimp only at obs
  rw [h,t] at obs
  change 6*(m-11)*m.choose 11+(twos G).card*(6*(m-2).choose 9)+6*(∑ d∈f,bonus m 11 d)≤
    6*(14*m.choose 11+charge 30 28 m 11 f) at obs
  change 6*(14*m.choose 11+charge 30 28 m 11 f) <
    6*(m-11)*m.choose 11+2*(6*(m-2).choose 9)+6*(∑ d∈f,bonus m 11 d) at win
  have sub : high G⊆nonleaves G := fun v hv => mem_filter.mpr ⟨mem_univ _,by have := (mem_filter.mp hv).2; omega⟩
  have total : (twos G).card+(high G).card=(nonleaves G).card := card_sdiff_add_card_eq_card sub
  have extra := Nat.mul_le_mul_right (6*(m-2).choose 9) (show 2≤(twos G).card by omega)
  omega

end Graffiti384b.Diversity30
#print axioms Graffiti384b.Diversity30.rows
#print axioms Graffiti384b.Diversity30.many_nonleaves
