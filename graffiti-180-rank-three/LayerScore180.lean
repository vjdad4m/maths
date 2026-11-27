import ParentBudget180
import ParentFiber180

set_option warningAsError true
namespace Minimal180.HigherRank
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 CutGain
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A parent choice can start a component of D and can give a child to B.
The same parent must witness both credits to count twice. -/
noncomputable def reward (D B : Finset V) (x y : V) : ℕ :=
  (if x∈D ∧ y∉D then 1 else 0)+(if y∈B then 1 else 0)

noncomputable def localScore (G : SimpleGraph V) (r : V) (D B : Finset V) (x : V) : ℕ :=
  (univ.filter (Pred G r x)).sup (reward D B x)

noncomputable def score (G : SimpleGraph V) (r : V) (D B : Finset V) : ℕ :=
  ∑ x∈univ.erase r, localScore G r D B x

theorem realizing_parents (G : SimpleGraph V) (hc : G.Connected) (r : V) (D B : Finset V) :
    ∃ p : V→V, (∀ x≠r, Pred G r x (p x)) ∧
      ∀ x≠r, localScore G r D B x=reward D B x (p x) := by
  classical
  have sel (x : V) (xr : x≠r) : ∃ y, Pred G r x y ∧ localScore G r D B x=reward D B x y := by
    obtain ⟨z,zp⟩ := Graffiti169.exists_predecessor G hc r x xr
    have nz : (univ.filter (Pred G r x)).Nonempty := ⟨z,mem_filter.mpr ⟨mem_univ _,zp⟩⟩
    obtain ⟨y,hy,e⟩ := exists_mem_eq_sup (s:=univ.filter (Pred G r x)) (f:=reward D B x) nz
    exact ⟨y,(mem_filter.mp hy).2,e⟩
  let p (x : V) := if h : x=r then r else (sel x h).choose
  have ok (x : V) (xr : x≠r) := (sel x xr).choose_spec
  exact ⟨p,fun x xr => by simpa [p,xr] using (ok x xr).1,
    fun x xr => by simpa [p,xr] using (ok x xr).2⟩

theorem reward_sum (r : V) (D B : Finset V) (p : V→V) :
    (∑ x∈univ.erase r, reward D B x (p x))=
      ((D.erase r).filter (fun x => p x∉D)).card+
      ∑ v∈B, ((univ.erase r).filter (fun x => p x=v)).card := by
  classical
  have eq : ((univ.erase r).filter (fun x => x∈D ∧ p x∉D))=
      ((D.erase r).filter (fun x => p x∉D)) := by ext x; simp [and_assoc]
  rw [sum_card_fiberwise_eq_card_filter]
  simp [reward,sum_add_distrib,eq]

/-- Every branch set gives a lower bound on the positive part of the child
count minus one. Taking precisely the nonleaf centers attains equality. -/
theorem branch_linearization (T : SimpleGraph V) [DecidableRel T.Adj] (tree : T.IsTree)
    (r : V) (p : V→V) (d : V→ℕ) (down : ∀ x≠r, d (p x)<d x)
    (take : ∀ x≠r, T.Adj x (p x)) (Y : Finset V) (nr : r∉Y) :
    (∀ B⊆Y, (∑ v∈B, ((univ.erase r).filter (fun x => p x=v)).card) ≤
      B.card+∑ v∈Y,(T.degree v-2)) ∧
    ∃ B⊆Y, (∑ v∈B, ((univ.erase r).filter (fun x => p x=v)).card)=
      B.card+∑ v∈Y,(T.degree v-2) := by
  classical
  let h (v : V) := ((univ.erase r).filter (fun x => p x=v)).card
  have degree (v : V) (hv : v∈Y) : T.degree v=h v+1 :=
    parent_neighbors T tree r p d down take v (fun eq => nr (eq ▸ hv))
  constructor
  · intro B inc
    have ub : ∑ v∈B, h v ≤ ∑ v∈B, (1+(T.degree v-2)) := by
      apply sum_le_sum
      intro v hv
      rw [degree v (inc hv)]
      omega
    have sub := sum_le_sum_of_subset_of_nonneg (f:=fun v => T.degree v-2) inc (fun _ _ _ => Nat.zero_le _)
    simp only [sum_add_distrib,sum_const,smul_eq_mul,mul_one] at ub
    exact ub.trans (Nat.add_le_add_left sub _)
  · let B := Y.filter (fun v => 0<h v)
    refine ⟨B,filter_subset ..,?_⟩
    have hsum : ∑ v∈B, h v = ∑ v∈B, (1+(T.degree v-2)) := by
      apply sum_congr rfl
      intro v hv
      obtain ⟨vy,pos⟩ := mem_filter.mp hv
      rw [degree v vy]
      omega
    have mass : ∑ v∈B, (T.degree v-2)=∑ v∈Y,(T.degree v-2) := by
      apply sum_subset (filter_subset ..)
      intro v vy nb
      have z : ¬0<h v := fun pos => nb (mem_filter.mpr ⟨vy,pos⟩)
      rw [degree v vy]
      omega
    simpa only [sum_add_distrib,sum_const,smul_eq_mul,mul_one,mass] using hsum

#print axioms realizing_parents
#print axioms reward_sum
#print axioms branch_linearization
end Minimal180.HigherRank
