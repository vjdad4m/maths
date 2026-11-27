import Independent

namespace ThetaIndependent2527.Crown
open Finset SimpleGraph TriangleMatching1078 AutoGraphForge378 Graffiti326

/-- Each part has n+3 vertices. Across the two parts, only equal indices
are nonadjacent. The index none is reserved for the unmatched pair. -/
abbrev Index (n : ℕ) := Option (Fin (n+2))
abbrev V (n : ℕ) := Bool × Index n
def g (n : ℕ) : SimpleGraph (V n) where
  Adj a b := a.1 ≠ b.1 ∧ a.2 ≠ b.2
  symm := fun _ _ h => ⟨h.1.symm,h.2.symm⟩
  loopless := fun _ h => h.1 rfl

instance {n} : DecidableRel (g n).Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
variable {n : ℕ}

theorem bipartite : (g n).Colorable 2 := by
  let color (b : Bool) : Fin 2 := if b then 1 else 0
  have inj : Function.Injective color := by intro a b eq; cases a <;> cases b <;> simp_all [color]
  exact ⟨Coloring.mk (fun v => color v.1) (fun h eq => h.1 (inj eq))⟩

theorem triangleFree : TriangleFree (g n) := by
  intro a b c ab bc ca
  exact (by decide : ∀ x y z : Bool, x≠y → y≠z → ¬z≠x) _ _ _ ab.1 bc.1 ca.1

theorem degree (v : V n) : (g n).degree v = n+2 := by
  classical
  let opp (j : Index n) : V n := (!v.1,j)
  have inj : Function.Injective opp := fun _ _ eq => congrArg Prod.snd eq
  have equal : (g n).neighborFinset v = (univ.erase v.2).image opp := by
    ext w
    rw [mem_image,mem_neighborFinset]
    constructor
    · intro h
      have eq : w.1 = !v.1 := by
        have ne := h.1
        cases ha : v.1 <;> cases hb : w.1 <;> simp_all
      exact ⟨w.2,mem_erase.mpr ⟨h.2.symm,mem_univ _⟩,Prod.ext eq.symm rfl⟩
    · rintro ⟨j,h,rfl⟩
      exact ⟨by change v.1 ≠ !v.1; cases v.1 <;> decide,(mem_erase.mp h).1.symm⟩
  rw [← card_neighborFinset_eq_degree,equal,card_image_of_injective _ inj,card_erase_of_mem (mem_univ _)]
  simp [Index]

theorem paired : HasMaximalMatching (g n) (n+2) := by
  let f : Fin (n+2) × Bool ↪ V n := ⟨fun (i,b) => (b,some (if b then i+1 else i)),by
    rintro ⟨i,b⟩ ⟨j,c⟩ eq
    have same := congrArg Prod.fst eq
    change b=c at same
    subst c
    have nums := Option.some.inj (congrArg Prod.snd eq)
    cases b <;> simp_all⟩
  have present (b : Bool) (i : Fin (n+2)) : (b,some i) ∈ support f := by
    apply (Graffiti326.mem_support f).mpr
    cases b
    · exact ⟨i,false,rfl⟩
    · refine ⟨i-1,true,?_⟩
      simp [f]
  refine ⟨f,fun i => ⟨by change false ≠ true; decide,?_⟩,?_⟩
  · change some i ≠ some (i+1)
    intro same
    have eq := Option.some.inj same
    have z : (0 : Fin (n+2)) = 1 := add_left_cancel (show i+0 = i+1 by rw [add_zero]; exact eq)
    have := congrArg Fin.val z
    simp at this
  · rintro ⟨b,_|i⟩ hu ⟨c,_|j⟩ hv adj
    · exact adj.2 rfl
    · exact hv (present _ _)
    · exact hu (present _ _)
    · exact hu (present _ _)

theorem independent_exact : independentDomination (g n) = 2 := by
  let a : V n := (false,none)
  let b : V n := (true,none)
  let S : Finset (V n) := {a,b}
  have size : S.card = 2 := by simp [S,a,b]
  have indice {u : V n} (h : u ∈ S) : u.2=none := by
    rcases (show u=a ∨ u=b by simpa [S] using h) with rfl|rfl <;> rfl
  have indep : (g n).IsIndepSet S := fun u hu v hv _ adj => adj.2 ((indice hu).trans (indice hv).symm)
  have dom : Dominates (g n) S := by
    rintro ⟨c,_|i⟩
    · left; cases c <;> simp [S,a,b]
    · right
      refine ⟨(!c,none),by cases c <;> simp [S,a,b],by cases c <;> simp [g]⟩
  have ub : independentDomination (g n) ≤ 2 := Nat.sInf_le ⟨S,size,indep,dom⟩
  obtain ⟨T,sz,_,valid⟩ := attained (g n)
  have nz : T.card ≠ 0 := by
    intro h
    rcases valid a with ht|⟨_,ht,_⟩ <;> simp [card_eq_zero.mp h] at ht
  have notOne : independentDomination (g n) ≠ 1 := by
    intro h
    obtain ⟨⟨c,j⟩,all⟩ := universal_of_one (g n) h
    have ne : (!c,j) ≠ (c,j) := by cases c <;> simp
    exact (all (!c,j) ne).2 rfl
  omega

/-- On the crown graph with side n+3 the edge optimum is n+2; deleting
one nonadjacent cross-pair leaves a perfect matching by a cyclic shift. -/
theorem values (n : ℕ) : (g n).Colorable 2 ∧ independentDomination (g n) = 2 ∧
    lineDomination (g n) = n+2 ∧ minMaximalMatching (g n) = n+2 := by
  have low := ((g n).le_minDegree_of_forall_le_degree _ (fun v => (degree v).ge)).trans
    (minDegree_le_lineDomination (g n) triangleFree)
  have hi : minMaximalMatching (g n) ≤ n+2 := Nat.sInf_le paired
  have cmp := lineDomination_le_matching (g n)
  exact ⟨bipartite,independent_exact,by omega,by omega⟩

#print axioms values
end ThetaIndependent2527.Crown
