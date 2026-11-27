import CubicMinCut
import SingleThreeCut

open Finset
namespace KelmansCactus.AtomicBridge.OddUncross
open FourRingCutAux
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

def colourOf (s : Finset V) (v : V) : Bool := decide (v∈s)

omit [Fintype V] in
@[simp] theorem colour_true {s : Finset V} {v : V} : colourOf s v=true ↔ v∈s := by
  simp [colourOf]

omit [Fintype V] in
@[simp] theorem colour_false {s : Finset V} {v : V} : colourOf s v=false ↔ v∉s := by
  simp [colourOf]

theorem colour_compl (s : Finset V) : colourOf sᶜ=fun x=> !(colourOf s x) := by
  funext x
  by_cases h : x∈s <;> simp [colourOf,h]

omit [Fintype V] [DecidableEq V] in
theorem not_trivial_flip {c : V→Bool} (n : ¬TrivialCut c) :
    ¬TrivialCut (fun x=> !(c x)) := by
  intro ht
  apply n
  rcases ht with a|a
  · right
    intro x y hx hy
    exact a x y (by simp [hx]) (by simp [hy])
  · left
    intro x y hx hy
    exact a x y (by simp [hx]) (by simp [hy])

omit [Fintype V] [DecidableEq V] in
theorem both_colours_of_nontrivial {c : V→Bool} (n : ¬TrivialCut c) :
    (∃ x,c x=true) ∧ (∃ x,c x=false) := by
  classical
  constructor
  · by_contra w
    apply n
    left
    intro x _ h _
    exact (w ⟨x,h⟩).elim
  · by_contra w
    apply n
    right
    intro x _ h _
    exact (w ⟨x,h⟩).elim

def ShoreThree (s : Finset V) : Prop :=
  (boundary G (colourOf s)).card=3 ∧ ¬TrivialCut (colourOf s)

def MinimalShore (s : Finset V) : Prop :=
  ShoreThree G s ∧ ∀ t,ShoreThree G t→t⊆s→t=s

/-- Both orientations of each nontrivial three-cut appear in the
family; this symmetry is essential to the two-minimal-shore theorem. -/
theorem shore_compl {s : Finset V} (h : ShoreThree G s) : ShoreThree G sᶜ := by
  unfold ShoreThree
  rw [colour_compl,boundary_flip_card]
  exact ⟨h.1,not_trivial_flip h.2⟩

theorem shore_nonempty {s : Finset V} (h : ShoreThree G s) : s.Nonempty := by
  obtain ⟨⟨a,ha⟩,_⟩ := both_colours_of_nontrivial h.2
  exact ⟨a,colour_true.mp ha⟩

/-- A minimal shore can be chosen inside any given shore, by
minimizing cardinality among the same family contained in it. -/
theorem exists_minimal_below {s : Finset V} (h : ShoreThree G s) :
    ∃ m,MinimalShore G m ∧ m⊆s := by
  classical
  let P : ℕ→Prop := fun k=>∃ u,ShoreThree G u ∧ u⊆s ∧ u.card=k
  have e : ∃ k,P k := ⟨s.card,s,h,subset_refl _,rfl⟩
  obtain ⟨m,m3,ms,em⟩ := Nat.find_spec e
  refine ⟨m,⟨m3,?_⟩,ms⟩
  intro t t3 tm
  apply Finset.eq_of_subset_of_card_le tm
  rw [em]
  exact Nat.find_min' e (show P t.card from ⟨t,t3,tm.trans ms,rfl⟩)

/-- Distinct minimal oriented shores are disjoint. If two overlapped,
minimality excludes nesting, and odd uncrossing forces their union
to be everything. The complement of one would then be a proper
nontrivial three-shore inside the other, again violating minimality. -/
theorem minimals_disjoint (min : MinBoundaryThree G) {a b : Finset V}
    (A : MinimalShore G a) (B : MinimalShore G b) (ne : a≠b) : Disjoint a b := by
  classical
  apply disjoint_left.mpr
  intro x xa xb
  have ab : ¬a⊆b := fun h=>ne (B.2 a A.1 h)
  have ba : ¬b⊆a := fun h=>ne (A.2 b B.1 h).symm
  have ex (u v : Finset V) (h : ¬u⊆v) : ∃ y,y∈u∧y∉v := by
    by_contra! none
    exact h (fun y hy=>none y hy)
  obtain ⟨p,pa,pb⟩ := ex a b ab
  obtain ⟨q,qb,qa⟩ := ex b a ba
  have union (z : V) : z∈a ∨ z∈b := by
    by_contra! h
    have bad := no_crossing_minimum_three_cuts G min (colourOf a) (colourOf b) A.1.1 B.1.1
    apply bad
    intro i j
    cases i <;> cases j
    · exact ⟨z,colour_false.mpr h.1,colour_false.mpr h.2⟩
    · exact ⟨q,colour_false.mpr qa,colour_true.mpr qb⟩
    · exact ⟨p,colour_true.mpr pa,colour_false.mpr pb⟩
    · exact ⟨x,colour_true.mpr xa,colour_true.mpr xb⟩
  have k : aᶜ⊆b := by
    intro z za
    exact (union z).resolve_left (mem_compl.mp za)
  have eq := B.2 aᶜ (shore_compl G A.1) k
  exact (mem_compl.mp (eq.symm ▸ xb)) xa

/-- The three-shore obstruction is stated with actual edge boundaries,
not with a chosen decomposition tree. -/
def ThreeDisjointShoreThree : Prop :=
  ∃ a b c : Finset V,ShoreThree G a ∧ ShoreThree G b ∧ ShoreThree G c ∧
    Disjoint a b ∧ Disjoint a c ∧ Disjoint b c

theorem minimal_shores_two (min : MinBoundaryThree G)
    (no : ¬ThreeDisjointShoreThree G) {s : Finset V} (some : ShoreThree G s) :
    ∃ a b : Finset V, MinimalShore G a ∧ MinimalShore G b ∧ Disjoint a b ∧
      ∀ c,MinimalShore G c→c=a ∨ c=b := by
  classical
  obtain ⟨a,ha,as⟩ := exists_minimal_below G some
  obtain ⟨b,hb,bs⟩ := exists_minimal_below G (shore_compl G some)
  have ab : Disjoint a b := by
    apply disjoint_left.mpr
    intro x xa xb
    exact (mem_compl.mp (bs xb)) (as xa)
  refine ⟨a,b,ha,hb,ab,?_⟩
  intro c hc
  by_contra! other
  have ac := minimals_disjoint G min ha hc other.1.symm
  have bc := minimals_disjoint G min hb hc other.2.symm
  exact no ⟨a,b,c,ha.1,hb.1,hc.1,ab,ac,bc⟩

/-- If there are at most two minimal shores, these same shores lie
wholly on opposite sides of every nontrivial three-cut. -/
theorem minimal_shores_oppose {a b s : Finset V}
    (all : ∀ u,MinimalShore G u→u=a ∨ u=b)
    (S : ShoreThree G s) :
    (a⊆s ∧ b⊆sᶜ) ∨ (b⊆s ∧ a⊆sᶜ) := by
  classical
  obtain ⟨p,P,ps⟩ := exists_minimal_below G S
  obtain ⟨q,Q,qs⟩ := exists_minimal_below G (shore_compl G S)
  have ne : p≠q := by
    intro e
    obtain ⟨x,xp⟩ := shore_nonempty G P.1
    exact (mem_compl.mp (qs (e ▸ xp))) (ps xp)
  rcases all p P with hp|hp <;> rcases all q Q with hq|hq
  · exact (ne (hp.trans hq.symm)).elim
  · exact Or.inl ⟨hp ▸ ps,hq ▸ qs⟩
  · exact Or.inr ⟨hp ▸ ps,hq ▸ qs⟩
  · exact (ne (hp.trans hq.symm)).elim

#print axioms minimals_disjoint
#print axioms minimal_shores_two
#print axioms minimal_shores_oppose
end
end KelmansCactus.AtomicBridge.OddUncross
