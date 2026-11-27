import OffFiveConnectedTwinGraphShape189

namespace Graffiti189LongestPath.TwoCut.SmallOrderFour
open SimpleGraph SimpleGraph.Walk Finset
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false
open private pin_data pin_pos LeftMarks RightMarks no_endpoints same_support_optimal reverse_long reverse_pin from SmallOrderFour189
open private length_ten_two_pin_shape pins_gap_at_four from FourOffGraphSupport189
open private off_five_pin_set_eq from OffFiveMixedClose189
open private hamilton_of_labeled_chain from FourOffGraphCore189
open private off_five_disconnected_single_marks off_five_single_pre_forward off_five_single_pre_exact model_d2_cap_any from DisconnectedSingleGraphVerified
open private path_neighbor_is_pin_of_off from OffFiveMixedMarks189
open private two_pin_flanks_path_only two_pin_universal_in_omitted_component from FourOffGraphSupport189
open private two_pins_choose_ordered left_boundary_porters_at_most_two right_boundary_porters_at_most_two from FourOffGraphCore189
open private off_five_tail_four off_five_tail_relabel off_five_tail_relabel_tail off_five_tail_relabel_low off_five_tail_relabel_inj from DisconnectedSingleGraphVerified

open private off_five_connected_twin_mask off_five_connected_twin_internal from OffFiveConnectedTwinGraphShape189
open OffFive16ConnectedTwin in
private theorem off_five_connected_twin_base
    (j : ℕ) (m : Marks) (C : Codes) (M : List Bool) {v w : Fin 16}
    (vl : v.val<12) (wl : w.val<12)
    (h : OffFive16DisconnectedSingle.edge j m ⟨v.val,vl⟩ ⟨w.val,wl⟩=true) :
    edge j m C M v w=true := by
  have vw : v.val<12 ∧ w.val<12 := ⟨vl,wl⟩
  have wv : w.val<12 ∧ v.val<12 := ⟨wl,vl⟩
  simp only [OffFive16DisconnectedSingle.edge,Bool.or_eq_true] at h
  simp only [edge,dir,Bool.or_eq_true,dif_pos vw,dif_pos wv]
  exact h.elim (fun e => .inl (.inl (.inl e))) (fun e => .inr (.inl (.inl e)))

open OffFive16ConnectedTwin in
private theorem off_five_connected_twin_forward
    {a b : V} {p : G.Walk a b}
    (φ : Fin 16→V) (value : ∀ k : Fin 16,k.val≤10 → φ k=p.getVert k.val)
    (j : ℕ) (jhi : j≤9) (m : Marks) (C : Codes)
    (portModel : ∀ k : Fin 16,11≤k.val →
        (portL (code C k.val) ↔ 1∈Pins p (φ k)) ∧
        (portR (code C k.val) ↔ j∈Pins p (φ k)))
    (univCore : ∀ u v : Fin 16,11≤u.val → 11≤v.val → u≠v →
      (code C u.val=3 ∨ code C v.val=3) → G.Adj (φ u) (φ v))
    (baseF : ∀ v w : Fin 12, OffFive16DisconnectedSingle.edge j m v w=true →
      G.Adj (φ (Fin.castLE (by decide : 12≤16) v)) (φ (Fin.castLE (by decide : 12≤16) w))) :
    ∀ u v,edge j m C (off_five_connected_twin_mask G φ C) u v=true → G.Adj (φ u) (φ v) := by
  have one (u v : Fin 16) (e : dir j m C (off_five_connected_twin_mask G φ C) u v=true) :
      G.Adj (φ u) (φ v) := by
    simp only [dir,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at e
    rcases e with ((base|contact)|⟨order,paired⟩)
    · by_cases low : u.val<12 ∧ v.val<12
      · simp only [dif_pos low] at base
        exact baseF ⟨u.val,low.1⟩ ⟨v.val,low.2⟩
          (by simp [OffFive16DisconnectedSingle.edge,base])
      · simp only [dif_neg low] at base
        contradiction
    · rcases contact with ⟨eq,vh,lp⟩|⟨eq,vh,rp⟩
      · rw [value u (by omega),eq]
        exact (pin_data ((portModel v (by omega)).1.mp lp)).2.symm
      · rw [value u (by omega),eq]
        exact (pin_data ((portModel v (by omega)).2.mp rp)).2.symm
    have pr : (decide (code C u.val=3 ∨ code C v.val=3) ||
        tailBit (off_five_connected_twin_mask G φ C) u.val v.val)=true := by
      simpa only [Bool.or_eq_true,decide_eq_true_eq] using paired
    exact (off_five_connected_twin_internal φ C univCore order.1 order.2).mp pr
  intro u v e
  simp only [edge,Bool.or_eq_true] at e
  exact e.elim (one _ _) (fun h => (one _ _ h).symm)

open OffFive16ConnectedTwin in
private theorem off_five_connected_twin_exact_core
    {a b : V} {p : G.Walk a b} (hp : IsLongest p) (len : p.length=10)
    (φ : Fin 16→V) (value : ∀ k : Fin 16,k.val≤10 → φ k=p.getVert k.val)
    (offH : ∀ k : Fin 16,11≤k.val → φ k∉p.support)
    (j : ℕ) (m : Marks) (C : Codes)
    (portModel : ∀ k : Fin 16,11≤k.val →
        (portL (code C k.val) ↔ 1∈Pins p (φ k)) ∧
        (portR (code C k.val) ↔ j∈Pins p (φ k)))
    (ports : ∀ k : Fin 16,11≤k.val → Pins p (φ k)⊆({1,j}:Finset ℕ))
    (univCore : ∀ u v : Fin 16,11≤u.val → 11≤v.val → u≠v →
      (code C u.val=3 ∨ code C v.val=3) → G.Adj (φ u) (φ v))
    (at11 : ∀ v : Fin 12,G.Adj (φ 11) (φ (Fin.castLE (by decide : 12≤16) v)) →
      OffFive16DisconnectedSingle.edge j m 11 v=true)
    (u : Fin 16) (uh : 11≤u.val) :
    ∀ v,G.Adj (φ u) (φ v) → edge j m C (off_five_connected_twin_mask G φ C) u v=true := by
  intro v e
  by_cases large : 11≤v.val
  · have ne : u.val≠v.val := fun h => G.loopless _ ((Fin.ext h : u=v) ▸ e)
    rcases lt_or_gt_of_ne ne with h|h
    · simp only [edge,Bool.or_eq_true]
      left
      simp only [dir,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq]
      refine .inr ⟨⟨uh,h⟩,?_⟩
      have pr := (off_five_connected_twin_internal φ C univCore uh h).mpr e
      simpa only [Bool.or_eq_true,decide_eq_true_eq] using pr
    · simp only [edge,Bool.or_eq_true]
      right
      simp only [dir,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq]
      refine .inr ⟨⟨large,h⟩,?_⟩
      have pr := (off_five_connected_twin_internal φ C univCore large h).mpr e.symm
      simpa only [Bool.or_eq_true,decide_eq_true_eq] using pr
  by_cases one : u.val=11
  · have eq : u=11 := Fin.ext one
    subst u
    exact off_five_connected_twin_base j m C _ (by decide) (by omega)
      (at11 ⟨v.val,by omega⟩ e)
  have ul : 12≤u.val := by omega
  have vl : v.val≤10 := by omega
  have pin := path_neighbor_is_pin_of_off hp (offH u uh) (show v.val≤p.length by omega)
    (by rwa [←value v vl])
  have alt : v.val=1 ∨ v.val=j := by simpa using ports u uh pin
  simp only [edge,Bool.or_eq_true]
  right
  simp only [dir,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq]
  refine .inl (.inr ?_)
  rcases alt with h|h
  · exact .inl ⟨h,ul,(portModel u uh).1.mpr (h ▸ pin)⟩
  · exact .inr ⟨h,ul,(portModel u uh).2.mpr (h ▸ pin)⟩

open OffFive16ConnectedTwin in
private theorem off_five_connected_twin_exact_ends
    {a b : V} {p : G.Walk a b} (hp : IsLongest p) (len : p.length=10)
    (φ : Fin 16→V) (value : ∀ k : Fin 16,k.val≤10 → φ k=p.getVert k.val)
    (offH : ∀ k : Fin 16,11≤k.val → φ k∉p.support)
    (j : ℕ) (m : Marks) (C : Codes) (u : Fin 12) (low : u=0 ∨ u=10)
    (exactAt : ∀ v : Fin 12,G.Adj (φ (Fin.castLE (by decide : 12≤16) u))
      (φ (Fin.castLE (by decide : 12≤16) v)) → OffFive16DisconnectedSingle.edge j m u v=true) :
    ∀ w,G.Adj (φ (Fin.castLE (by decide : 12≤16) u)) (φ w) →
      edge j m C (off_five_connected_twin_mask G φ C)
        (Fin.castLE (by decide : 12≤16) u) w=true := by
  intro w e
  have wl : w.val<12 := by
    by_cases yes : w.val<12
    · exact yes
    · exfalso
      have wo := offH w (by omega)
      rcases low with rfl|rfl
      · have ea : φ (Fin.castLE (by decide : 12≤16) (0:Fin 12))=a :=
          (value 0 (by decide)).trans p.getVert_zero
        exact (no_endpoints hp wo).1 (ea ▸ e.symm)
      · have eb : φ (Fin.castLE (by decide : 12≤16) (10:Fin 12))=b := by
          change φ 10=b
          rw [value 10 (by decide)]
          simpa only [len] using p.getVert_length
        exact (no_endpoints hp wo).2 (eb ▸ e.symm)
  exact off_five_connected_twin_base j m C _ u.isLt wl (exactAt ⟨w.val,wl⟩ e)

#print axioms off_five_connected_twin_forward
#print axioms off_five_connected_twin_exact_core
#print axioms off_five_connected_twin_exact_ends

end Graffiti189LongestPath.TwoCut.SmallOrderFour
