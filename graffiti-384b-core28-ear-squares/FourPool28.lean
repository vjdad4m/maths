import CoreFrontier28
namespace Graffiti384b.Four28
open Finset SimpleGraph
open private FiniteRange.bad from FiniteRange384b
open private Repair.nbr_mono from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def fibers (W : Finset V) (b : ℕ) (v : V) :=
  ((W.powersetCard b).filter (fun k => v∈FiniteRange.bad G W k)).card

/-- The vertices outside W are retained. Each deficient vertex can be promoted. -/
theorem pool_budget (W : Finset V) (b : ℕ) :
    W.card.choose b*(gamma G-Wᶜ.card-b)≤∑ v,fibers G W b v := by
  classical
  let opts := W.powersetCard b
  let fail := fun k => FiniteRange.bad G W k
  have each (k : Finset V) (km : k∈opts) : gamma G-Wᶜ.card-b≤(fail k).card := by
    have sz := (mem_powersetCard.mp km).2
    let B := Wᶜ∪k
    let D := B∪fail k
    have dom : TwoDominates G D := by
      intro v vd
      have vb : v∉B := fun h => vd (mem_union_left _ h)
      have vm : v∈W := Classical.byContradiction (fun no => vb (mem_union_left k (mem_compl.mpr no)))
      have vk : v∉k := fun h => vb (mem_union_right _ h)
      have enough : 2≤nbr G v B := Nat.le_of_not_gt (fun low =>
        vd (mem_union_right _ (mem_filter.mpr ⟨mem_sdiff.mpr ⟨vm,vk⟩,low⟩)))
      exact enough.trans (Repair.nbr_mono G v subset_union_left)
    have up : gamma G≤D.card := Nat.sInf_le ⟨D,dom,rfl⟩
    have a : D.card≤B.card+(fail k).card := card_union_le ..
    have c : B.card≤Wᶜ.card+k.card := card_union_le ..
    omega
  have total : (∑ k∈opts,(fail k).card)=∑ v,fibers G W b v := by
    calc _ = ∑ k∈opts,∑ v,if v∈fail k then 1 else 0 := by simp
         _ = _ := by rw [sum_comm]; simp [fibers,opts,fail,sum_boole]
  have many := sum_le_sum each
  rw [total] at many
  simpa [opts,card_powersetCard] using many

end Graffiti384b.Four28
#print axioms Graffiti384b.Four28.pool_budget
