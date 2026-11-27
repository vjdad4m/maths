import NearPerfectEquivalence

open SimpleGraph
namespace KelmansCactus.NearPerfectReplica.Layout
noncomputable section
variable {U J : Type*} {A : SimpleGraph U} {B : SimpleGraph J} {r : U}
variable (L : Layout A B r)

/-- Two cross edges from the same host vertex are the same edge. -/
theorem unique_external_of_vertex {a b c : Host J r}
    (ab : L.graph.Adj a b) (ac : L.graph.Adj a c)
    (sepAb : a.1≠b.1) (sepAc : a.1≠c.1) : b=c := by
  obtain ⟨s,sa,sb⟩ := (L.external_adj sepAb).mp ab
  obtain ⟨t,ta,tc⟩ := (L.external_adj sepAc).mp ac
  have e := L.p_inj (sa.trans ta.symm)
  exact sb.symm.trans (e ▸ tc)

/-- A simple base graph has at most one seam edge between any
specified ordered pair of distinct host cells. -/
theorem unique_external_of_cells {a b c d : Host J r}
    (ab : L.graph.Adj a b) (cd : L.graph.Adj c d)
    (sepAb : a.1≠b.1) (ac : a.1=c.1) (bd : b.1=d.1) : a=c ∧ b=d := by
  have cdDiff : c.1≠d.1 := fun e=>sepAb (ac.trans (e.trans bd.symm))
  obtain ⟨s,sa,sb⟩ := (L.external_adj sepAb).mp ab
  obtain ⟨t,tc,td⟩ := (L.external_adj cdDiff).mp cd
  have p1 : s.1=t.1 := (congrArg Prod.fst sa).trans (ac.trans (congrArg Prod.fst tc).symm)
  have p2 : L.target s=L.target t :=
    (congrArg Prod.fst sb).trans (bd.trans (congrArg Prod.fst td).symm)
  have e := L.slot_eq_of_target p1 p2
  exact ⟨sa.symm.trans (e ▸ tc),sb.symm.trans (e ▸ td)⟩

/-- A cyclically enumerated simple cycle; edges not in the cycle are
allowed. This will be used only at lengths 3, 4 and 5. -/
def CycleList {V : Type*} (G : SimpleGraph V) (n : ℕ) [NeZero n] (f : Fin n→V) : Prop :=
  Function.Injective f ∧ ∀ i,G.Adj (f i) (f (i+1))

def HasShortCycle {V : Type*} (G : SimpleGraph V) (n : ℕ) [NeZero n] : Prop :=
  ∃ f : Fin n→V,CycleList G n f

private theorem labels_differ {V : Type*} {n : ℕ} {f : Fin n→V}
    (inj : Function.Injective f) {i j : Fin n} (ne : i≠j) : f i≠f j :=
  fun e=>ne (inj e)

private theorem first_inside3 {f : Fin 3→Host J r} (cy : CycleList L.graph 3 f) :
    (f 0).1=(f 1).1 := by
  by_contra h
  have f01 := cy.2 0
  have f12 := cy.2 1
  have f20 : L.graph.Adj (f 2) (f 0) := cy.2 2
  have f02 := f20.symm
  have one : (f 1).1=(f 2).1 := by
    by_contra diff
    exact labels_differ cy.1 (by decide : (0:Fin 3)≠2)
      (L.unique_external_of_vertex f01.symm f12 (Ne.symm h) diff)
  have two : (f 0).1=(f 2).1 := by
    by_contra diff
    exact labels_differ cy.1 (by decide : (1:Fin 3)≠2)
      (L.unique_external_of_vertex f01 f02 h diff)
  exact h (two.trans one.symm)

private theorem first_inside4 {f : Fin 4→Host J r} (cy : CycleList L.graph 4 f) :
    (f 0).1=(f 1).1 := by
  by_contra h
  have f01 := cy.2 0
  have f12 := cy.2 1
  have f23 := cy.2 2
  have f30 : L.graph.Adj (f 3) (f 0) := cy.2 3
  have one : (f 1).1=(f 2).1 := by
    by_contra diff
    exact labels_differ cy.1 (by decide : (0:Fin 4)≠2)
      (L.unique_external_of_vertex f01.symm f12 (Ne.symm h) diff)
  have two : (f 0).1=(f 3).1 := by
    by_contra diff
    exact labels_differ cy.1 (by decide : (1:Fin 4)≠3)
      (L.unique_external_of_vertex f01 f30.symm h diff)
  exact labels_differ cy.1 (by decide : (0:Fin 4)≠3)
    (L.unique_external_of_cells f01 f23.symm h two one).1

private theorem first_inside5 {f : Fin 5→Host J r} (cy : CycleList L.graph 5 f) :
    (f 0).1=(f 1).1 := by
  by_contra h
  have f01 := cy.2 0
  have f12 := cy.2 1
  have f23 := cy.2 2
  have f34 := cy.2 3
  have f40 : L.graph.Adj (f 4) (f 0) := cy.2 4
  have one : (f 1).1=(f 2).1 := by
    by_contra diff
    exact labels_differ cy.1 (by decide : (0:Fin 5)≠2)
      (L.unique_external_of_vertex f01.symm f12 (Ne.symm h) diff)
  have two : (f 0).1=(f 4).1 := by
    by_contra diff
    exact labels_differ cy.1 (by decide : (1:Fin 5)≠4)
      (L.unique_external_of_vertex f01 f40.symm h diff)
  by_cases mid : (f 3).1=(f 2).1
  · exact labels_differ cy.1 (by decide : (0:Fin 5)≠4)
      (L.unique_external_of_cells f01 f34.symm h two (one.trans mid.symm)).1
  by_cases last : (f 3).1=(f 4).1
  · exact labels_differ cy.1 (by decide : (1:Fin 5)≠2)
      (L.unique_external_of_cells f01 f23.symm h (two.trans last.symm) one).2
  exact labels_differ cy.1 (by decide : (2:Fin 5)≠4)
    (L.unique_external_of_vertex f23.symm f34 mid last)

theorem cycle_shift {V : Type*} {G : SimpleGraph V} {n : ℕ} [NeZero n]
    {f : Fin n→V} (cy : CycleList G n f) (i : Fin n) :
    CycleList G n (fun j=>f (j+i)) := by
  refine ⟨fun _ _ e=>add_right_cancel (cy.1 e),?_⟩
  intro j
  have h := cy.2 (j+i)
  convert h using 1
  ac_rfl

theorem identity_cells {n : ℕ} [NeZero n] {f : Fin n→Host J r}
    (next : ∀ i,(f i).1=(f (i+1)).1) (i : Fin n) : (f i).1=(f 0).1 := by
  obtain ⟨k,hk⟩ := i
  induction k with
  | zero => rfl
  | succ k ih =>
    have shorter : k<n := by omega
    have h := next ⟨k,shorter⟩
    have t : ((⟨k,shorter⟩ : Fin n)+1)=⟨k+1,hk⟩ := by
      apply Fin.ext
      rw [Fin.add_def]
      have p : (1 : Fin n).val=1 := by
        simp [Nat.mod_eq_of_lt (by omega : 1<n)]
      simp only [p,Nat.mod_eq_of_lt hk]
    rw [t] at h
    exact h.symm.trans (ih shorter)

def rootDeleted : SimpleGraph (Cell r) := A.induce {x | x≠r}

private theorem exact_short_cycle {n : ℕ} [NeZero n] [Nonempty J]
    (atFirst : ∀ f : Fin n→Host J r,CycleList L.graph n f → (f 0).1=(f 1).1) :
    HasShortCycle L.graph n ↔ HasShortCycle (rootDeleted (A:=A) (r:=r)) n := by
  constructor
  · rintro ⟨f,hf⟩
    have goe (i : Fin n) : (f i).1=(f (i+1)).1 := by
      have e := atFirst _ (cycle_shift hf i)
      simpa only [zero_add,add_comm (1:Fin n) i] using e
    have t := identity_cells goe
    refine ⟨fun j=>(f j).2,⟨?_,?_⟩⟩
    · intro i j e
      exact hf.1 (Prod.ext ((t i).trans (t j).symm) e)
    · intro i
      exact (L.internal_adj (goe i)).mp (hf.2 i)
  · rintro ⟨f,hf⟩
    obtain ⟨j⟩ := ‹Nonempty J›
    refine ⟨fun i=>(j,f i),⟨fun _ _ eq=>hf.1 (congrArg (fun v : Host J r=>v.2) eq),?_⟩⟩
    intro i
    exact Or.inl ⟨rfl,hf.2 i⟩

/-- Every triangle stays wholly in one replica cell. -/
theorem triangle_iff [Nonempty J] :
    HasShortCycle L.graph 3 ↔ HasShortCycle (rootDeleted (A:=A) (r:=r)) 3 :=
  L.exact_short_cycle (fun _=>L.first_inside3)

/-- Every four-cycle stays wholly in one replica cell. -/
theorem square_iff [Nonempty J] :
    HasShortCycle L.graph 4 ↔ HasShortCycle (rootDeleted (A:=A) (r:=r)) 4 :=
  L.exact_short_cycle (fun _=>L.first_inside4)

/-- Every five-cycle stays wholly in one replica cell. The base itself
may have triangles or four-cycles; they create no cycle of order < 6. -/
theorem pentagon_iff [Nonempty J] :
    HasShortCycle L.graph 5 ↔ HasShortCycle (rootDeleted (A:=A) (r:=r)) 5 :=
  L.exact_short_cycle (fun _=>L.first_inside5)

#print axioms triangle_iff
#print axioms square_iff
#print axioms pentagon_iff
end
end KelmansCactus.NearPerfectReplica.Layout
