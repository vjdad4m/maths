import Reused

namespace Chain5169
open SimpleGraph Finset Graffiti326 AutoGraphForge378 BullCover1125 TriangleMatching1078

abbrev V (k : ℕ) := Fin (4*k+1)

/-- A spanning path with the shortcut 4i+1 -- 4i+3 in each block. -/
def link (a b : ℕ) := a+1=b ∨ b+1=a ∨
    (a%4=1 ∧ a+2=b) ∨ (b%4=1 ∧ b+2=a)

def chain (k : ℕ) : SimpleGraph (V k) where
  Adj a b := link a.val b.val
  symm := by intro a b h; unfold link at *; tauto
  loopless := by intro x h; unfold link at h; omega

instance (k) : DecidableRel (chain k).Adj := fun x y => by
  change Decidable (link x.val y.val)
  unfold link
  infer_instance

theorem connected (k : ℕ) : (chain k).Connected := by
  let zero : V k := ⟨0,by omega⟩
  have reach (n : ℕ) (h : n < 4*k+1) : (chain k).Reachable zero ⟨n,h⟩ := by
    induction n with
    | zero => exact .rfl
    | succ n ih =>
      have hn : n < 4*k+1 := by omega
      have e : (chain k).Adj ⟨n,hn⟩ ⟨n+1,h⟩ := Or.inl rfl
      exact (ih hn).trans e.reachable
  exact ⟨fun x y => (reach x x.isLt).symm.trans (reach y y.isLt)⟩

theorem subcubic (k : ℕ) (v : V k) : (chain k).degree v ≤ 3 := by
  let x := v.val
  let labels : Finset ℕ := {x-1,x+1,if x%4=1 then x+2 else x-2}
  have into : ∀ w ∈ (chain k).neighborFinset v, w.val ∈ labels := by
    intro w hw
    have adj := ((chain k).mem_neighborFinset v w).mp hw
    change link x w.val at adj
    unfold link at adj
    simp only [labels,mem_insert,mem_singleton]
    split <;> omega
  have size : labels.card ≤ 3 := (card_insert_le _ _).trans (by
    have h := card_insert_le (x+1) ({if x%4=1 then x+2 else x-2} : Finset ℕ)
    simpa using Nat.add_le_add_right h 1)
  exact (card_le_card_of_injOn Fin.val into Fin.val_injective.injOn).trans size

/-- Neighbors on the same side of the center are adjacent. -/
theorem same_side {x a b : ℕ} (ha : link x a) (hb : link x b) (ne : a ≠ b)
    (side : (a < x ∧ b < x) ∨ (x < a ∧ x < b)) : link a b := by
  unfold link at *
  omega

theorem claw_free (k : ℕ) : Free (chain k) claw := by
  rintro ⟨f⟩
  let label (i : Fin 4) := (f i).val
  have inj : Function.Injective label := Fin.val_injective.comp f.injective
  have spoke (i : Fin 4) (h : claw.Adj 0 i) : link (label 0) (label i) := f.map_rel_iff.mpr h
  have separate (i j : Fin 4) (ij : i ≠ j) (h : ¬claw.Adj i j)
      (a : claw.Adj 0 i) (b : claw.Adj 0 j) :
      ¬ ((label i < label 0 ∧ label j < label 0) ∨ (label 0 < label i ∧ label 0 < label j)) :=
    fun side => h (f.map_rel_iff.mp (same_side (spoke i a) (spoke j b) (fun eq => ij (inj eq)) side))
  have h₁ := separate 1 2 (by decide) (by decide) (by decide) (by decide)
  have h₂ := separate 1 3 (by decide) (by decide) (by decide) (by decide)
  have h₃ := separate 2 3 (by decide) (by decide) (by decide) (by decide)
  have ne (i : Fin 4) (h : i ≠ 0) : label i ≠ label 0 := fun eq => h (inj eq)
  have := ne 1 (by decide)
  have := ne 2 (by decide)
  have := ne 3 (by decide)
  omega

def tip {k} (i : Fin k) (b : Bool) : V k := ⟨4*i.val + (if b then 3 else 1),
  by have := i.isLt; split <;> omega⟩

theorem joins {k} (i : Fin k) : (chain k).Adj (tip i false) (tip i true) := by
  change link (4*i.val+1) (4*i.val+3)
  unfold link
  omega

theorem bridge_matching (k) : HasMaximalMatching (chain k) k := by
  let f : Fin k × Bool ↪ V k := ⟨fun p => tip p.1 p.2,by
    rintro ⟨i,b⟩ ⟨j,c⟩ eq
    have e : (tip i b).val = (tip j c).val := congrArg Fin.val eq
    cases b <;> cases c
    · exact Prod.ext (Fin.ext (by change 4*i.val+1=4*j.val+1 at e; change i.val=j.val; omega)) rfl
    · change 4*i.val+1=4*j.val+3 at e
      omega
    · change 4*i.val+3=4*j.val+1 at e
      omega
    · exact Prod.ext (Fin.ext (by change 4*i.val+3=4*j.val+3 at e; change i.val=j.val; omega)) rfl⟩
  have used (i : Fin k) (b : Bool) : tip i b ∈ support f :=
    (Graffiti326.mem_support f).mpr ⟨i,b,rfl⟩
  have outside (v : V k) (hv : v ∉ support f) : v.val % 2 = 0 := by
    apply Classical.byContradiction
    intro odd
    let i : Fin k := ⟨v.val/4,by have := v.isLt; omega⟩
    have hit : v = tip i false ∨ v = tip i true := by
      by_cases h : v.val%4 = 1
      · exact Or.inl (Fin.ext (by dsimp [tip,i]; omega))
      · exact Or.inr (Fin.ext (by dsimp [tip,i]; omega))
    exact hit.elim (fun eq => hv (eq ▸ used i false)) (fun eq => hv (eq ▸ used i true))
  refine ⟨f,joins,fun v hv w hw e => ?_⟩
  have a := outside v hv
  have b := outside w hw
  change link v.val w.val at e
  unfold link at e
  omega

/-- A selected shortcut dominates its block. Distinct shortcuts form an
induced matching, so one graph edge cannot dominate two of them. -/
theorem matching_exact (k) : lineDomination (chain k) = k ∧ minMaximalMatching (chain k) = k := by
  let chord (i : Fin k) : (chain k).edgeSet := ⟨s(tip i false,tip i true),joins i⟩
  have apart (e : (chain k).edgeSet) (i j : Fin k)
      (hits : ∃ v, v ∈ e.val ∧ v ∈ (chord i).val)
      (hits' : ∃ w, w ∈ e.val ∧ w ∈ (chord j).val) : i=j := by
    obtain ⟨v,ve,vi⟩ := hits
    obtain ⟨w,we,wj⟩ := hits'
    have close : v.val=w.val ∨ link v.val w.val := by
      by_cases eq : v=w
      · exact Or.inl (congrArg Fin.val eq)
      · exact Or.inr (show s(v,w) ∈ (chain k).edgeSet from
          ((Sym2.mem_and_mem_iff eq).mp ⟨ve,we⟩) ▸ e.property)
    have pos (t : Fin k) (u : V k) (hu : u ∈ (chord t).val) :
        u.val = 4*t.val+1 ∨ u.val = 4*t.val+3 := by
      rcases Sym2.mem_iff.mp hu with rfl|rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    have pi := pos i v vi
    have pj := pos j w wj
    apply Fin.ext
    unfold link at close
    omega
  have lo : k ≤ lineDomination (chain k) := by simpa using packing_lower (chain k) chord apart
  have mid := lineDomination_le_matching (chain k)
  have hi : minMaximalMatching (chain k) ≤ k := Nat.sInf_le (bridge_matching k)
  omega

theorem cover_exact {k} (hk : 0 < k) : edgeCoverValue (chain k) = some (2*k+1) := by
  have iso : IsolateFree (chain k) := by
    intro v
    by_cases h : v.val = 0
    · exact ⟨⟨1,by omega⟩,Or.inl (by change v.val+1=1; omega)⟩
    · exact ⟨⟨v.val-1,by have := v.isLt; omega⟩,Or.inr (Or.inl (by change v.val-1+1=v.val; omega))⟩
  have hi := spanning_cover (G:=chain k) (m:=4*k) (by omega) (Equiv.refl _) (fun _ _ h => Or.inl h)
  have lo := vertices_le_twice_cover iso
  rw [Fintype.card_fin] at lo
  have eq : edgeCoverNumber (chain k) = 2*k+1 := by omega
  simp [edgeCoverValue,iso,eq]

end Chain5169
