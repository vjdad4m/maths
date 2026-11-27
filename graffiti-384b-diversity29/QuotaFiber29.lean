import BlockLoss384b

namespace Graffiti384b.Quota29.Sample
open Finset SimpleGraph CliqueChoice CliqueSample LowSample
open private FiniteRange.bad from FiniteRange384b
open private LowSample.delta LowSample.eligible LowSample.anchors LowSample.weight LowSample.anchor_samples LowSample.two_degree from LowSample384b
open private CliqueSample.trial CliqueSample.active_fiber from CliqueSample384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Combine the degree-nine pool-loss estimate with the saturated
representative sampler. The double count follows UnifiedSample.extraObstruction. -/
theorem extraObstruction {p : Finset V} {tested : Finset ℕ} (choice : Choice G p tested) (b : ℕ) (limit : ℕ → ℕ)
    (dist : ∀ j ∈ range 9, 3 ≤ j → ((high G \ p).filter (fun v => G.degree v ≤ j)).card ≤ limit j)
    (extra : V → ℕ)
    (refund : ∀ v ∈ high G \ p, (((high G \ p).powersetCard b).filter (fun k => v ∈ FiniteRange.bad G (high G \ p) k)).card + extra v ≤
      FiniteRange.badCount (high G \ p).card b (min (G.degree v) 9)) (two : 2 ≤ b)
    (env : BlockLoss.envelope (high G \ p).card b) (rew : reward (high G \ p).card b)
    (fail : bound G < gamma G) :
    let f := p.image (fun v => G.degree v)
    let h := (high G).card
    let m := h-f.card
    6*(m-b)*m.choose b + (twos G).card*(6*(m-2).choose (b-2)) + 6*(∑ d ∈ f, bonus m b d) + 6*(∑ v ∈ high G \ p, extra v) ≤
      6*((((types G).card+1)/2-1)*m.choose b + BlockLoss.chargeAt m b limit) := by
  let s := high G \ p
  let f := p.image (fun v => G.degree v)
  let opts := s.powersetCard b
  let z := twos G
  let W (v : V) := LowSample.weight (LowSample.anchors G v).card
  have mass : z.card * (6*(s.card-2).choose (b-2)) ≤ ∑ k ∈ opts, ∑ v ∈ LowSample.eligible G k, W v := by
    calc
      _ = ∑ _v ∈ z, (6*(s.card-2).choose (b-2)) := by simp
      _ ≤ ∑ v ∈ z, ∑ k ∈ opts, if LowSample.anchors G v ⊆ k then W v else 0 := by
        apply sum_le_sum
        intro v hv
        have count : (LowSample.anchors G v).card ≤ 2 := by
          have sub : LowSample.anchors G v ⊆ G.neighborFinset v := fun x hx =>
            (G.mem_neighborFinset _ _).mpr (mem_filter.mp hx).2
          simpa only [card_neighborFinset_eq_degree,LowSample.two_degree G hv] using card_le_card sub
        have a := rew ⟨(LowSample.anchors G v).card,by omega⟩
        have keep : LowSample.anchors G v ⊆ s := by
          intro w hw
          obtain ⟨wh,vw⟩ := mem_filter.mp hw
          exact mem_sdiff.mpr ⟨wh,fun wp => (mem_sdiff.mp hv).2
            (mem_sdiff.mp (neighbors_in_pool G choice wp ((G.mem_neighborFinset _ _).mpr vw.symm))).1⟩
        have q := LowSample.anchor_samples s (LowSample.anchors G v) b keep (by omega)
        rw [← sum_filter,sum_const,nsmul_eq_mul,Nat.cast_id]
        simpa only [Nat.mul_comm (W v),W,opts,s] using a.trans (Nat.mul_le_mul_left _ q)
      _ = _ := by rw [sum_comm]; simp [LowSample.eligible,z,sum_filter]

  have credit : ∑ d ∈ f, bonus s.card b d ≤ ∑ k ∈ opts, (active G p k).card := by
    calc
      _ = ∑ v ∈ p, bonus s.card b (G.degree v) := sum_image (fun _ hx _ hy eq => choice.unique hx hy eq)
      _ ≤ ∑ v ∈ p, (opts.filter (fun k => v ∈ active G p k)).card :=
        sum_le_sum (fun v hv => CliqueSample.active_fiber G choice b hv)
      _ = ∑ v ∈ p, ∑ k ∈ opts, (if v ∈ active G p k then 1 else 0 : ℕ) := by simp
      _ = _ := by
        rw [sum_comm]; apply sum_congr rfl
        intro k _
        simp only [sum_boole,Nat.cast_id,filter_mem_eq_inter]
        rw [inter_eq_right.mpr (show active G p k ⊆ p from filter_subset _ _)]
  have point (k : Finset V) (hk : k ∈ opts) : 6*(s.card-b) + (∑ v ∈ LowSample.eligible G k, W v) + 6*(active G p k).card ≤
      6*((((types G).card+1)/2-1) + (FiniteRange.bad G s k).card) := by
    obtain ⟨sub,sz⟩ := mem_powersetCard.mp hk
    have tr := CliqueSample.trial G choice k sub fail
    dsimp only at tr
    rwa [sz] at tr
  have tot := sum_le_sum point
  simp only [sum_add_distrib,Nat.mul_add,← mul_sum,sum_const,nsmul_eq_mul,opts,card_powersetCard,Nat.cast_id] at tot
  have bad := BlockLoss.pool_loss G s sdiff_subset b limit dist extra refund env
  change (∑ k ∈ s.powersetCard b, (FiniteRange.bad G s k).card) + (∑ v ∈ s, extra v) ≤ BlockLoss.chargeAt s.card b limit at bad
  dsimp only [opts] at mass credit
  have sz : (high G).card - f.card = s.card := by rw [show f.card = p.card from card_image_of_injOn choice.unique]; exact (card_sdiff choice.high_sub).symm
  dsimp only
  change 6*((high G).card-f.card-b)*((high G).card-f.card).choose b + z.card*(6*((high G).card-f.card-2).choose (b-2)) +
    6*(∑ d ∈ f, bonus ((high G).card-f.card) b d) + 6*(∑ v ∈ s, extra v) ≤ 6*(_*((high G).card-f.card).choose b + BlockLoss.chargeAt ((high G).card-f.card) b limit)
  rw [sz,Nat.mul_comm (6*(s.card-b)) (s.card.choose b),Nat.mul_left_comm (s.card.choose b) 6 (s.card-b),
    Nat.mul_comm (((types G).card+1)/2-1) (s.card.choose b)]
  omega

end Graffiti384b.Quota29.Sample
#print axioms Graffiti384b.Quota29.Sample.extraObstruction

