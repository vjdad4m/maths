import AdjacentCutFiveTopArithmetic189
import AdjacentCutFiveMetric189
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset
open scoped BigOperators
open private CutGraph Shore shore_closed shore_connected shore_off shore_disjoint shore_hit_a shore_hit_b
  from AdjacentCutFiveActual189
open private mem_positive from AdjacentCutFiveBound189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false
private abbrev Cmp (G : SimpleGraph V) (a b : V) := (CutGraph (G:=G) a b).ConnectedComponent

private noncomputable def key (G : SimpleGraph V) (a b v : V) : Fin 6 := by
  classical
  exact if G.dist a v<G.dist b v then
    if Even (G.dist a v) then 0 else 3
  else if G.dist b v<G.dist a v then
    if Even (G.dist b v) then 1 else 4
  else if Even (G.dist a v) then 2 else 5

private def sa (i : Fin 6) : ℕ := if i=1 ∨ i=4 then 1 else 0
private def sb (i : Fin 6) : ℕ := if i=0 ∨ i=3 then 1 else 0
private def pa (i : Fin 6) : ℕ := if i=3 ∨ i=4 ∨ i=5 then 1 else 0

private theorem key_facts (hc : G.Connected) (ab : G.Adj a b) (v : V) :
    G.dist a v=depth G a b v+sa (key G a b v) ∧
    G.dist b v=depth G a b v+sb (key G a b v) ∧
    (depth G a b v)%2=pa (key G a b v) := by
  classical
  have u := hc.dist_triangle (u:=a) (v:=b) (w:=v)
  have w := hc.dist_triangle (u:=b) (v:=a) (w:=v)
  rw [dist_eq_one_iff_adj.mpr ab] at u
  rw [dist_eq_one_iff_adj.mpr ab.symm] at w
  by_cases e : G.dist a v<G.dist b v
  · have h : G.dist a v≤G.dist b v := e.le
    by_cases f : Even (G.dist a v) <;>
      simp [key,e,f,sa,sb,pa,depth,min_eq_left h] <;>
      simp only [Nat.even_iff] at * <;> omega
  by_cases e' : G.dist b v<G.dist a v
  · have h : G.dist b v≤G.dist a v := e'.le
    by_cases f : Even (G.dist b v) <;>
      simp [key,e,e',f,sa,sb,pa,depth,min_eq_right h] <;>
      simp only [Nat.even_iff] at * <;> omega
  have eq : G.dist a v=G.dist b v := by omega
  by_cases f : Even (G.dist a v) <;>
    simp [key,e,e',f,sa,sb,pa,depth,min_eq_left (show G.dist a v≤G.dist b v from eq.le)] <;>
    simp only [Nat.even_iff] at * <;> omega

private noncomputable def classSet (C : Cmp G a b) (i : Fin 6) : Finset V :=
  (Shore C).filter (fun v=>key G a b v=i)

private noncomputable def prof (C : Cmp G a b) : AdjProfile :=
  ⟨(classSet C 0).card,(classSet C 1).card,(classSet C 2).card,
    (classSet C 3).card,(classSet C 4).card,(classSet C 5).card⟩

private theorem profile_size (C : Cmp G a b) : (prof C).size=(Shore C).card := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (f:=key G a b) (s:=Shore C) (t:=univ) (fun _ _=>mem_univ _)
  simpa only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,prof,AdjProfile.size,
    classSet,add_assoc] using h.symm

private def paysA (i : Fin 6) : Prop := i=0 ∨ i=2 ∨ i=4
private def paysB (i : Fin 6) : Prop := i=1 ∨ i=2 ∨ i=3
private def compat (i j : Fin 6) : Prop :=
  (pa i+pa j+min (sa i+sa j) (sb i+sb j))%2=0

private instance (i : Fin 6) : Decidable (paysA i) := inferInstanceAs (Decidable (_ ∨ _ ∨ _))
private instance (i : Fin 6) : Decidable (paysB i) := inferInstanceAs (Decidable (_ ∨ _ ∨ _))
private instance (i j : Fin 6) : Decidable (compat i j) := inferInstanceAs (Decidable (_ = _))

private def cnt (i : Fin 6) : ℕ := (if paysA i then 1 else 0)+(if paysB i then 1 else 0)

private theorem checked_charge (i : Fin 6) :
    (paysA i ↔ (pa i+sa i)%2=0) ∧ (paysB i ↔ (pa i+sb i)%2=0) := by
  fin_cases i <;> decide

private theorem terminal_charges (hc : G.Connected) (ab : G.Adj a b) {w : V} :
    (paysA (key G a b w) ↔ Even (G.dist a w)) ∧
    (paysB (key G a b w) ↔ Even (G.dist b w)) := by
  obtain ⟨a',b',p'⟩ := key_facts hc ab w
  have cl := checked_charge (key G a b w)
  rw [cl.1,cl.2,Nat.even_iff,Nat.even_iff,a',b']
  omega

private theorem foreign_charges (hc : G.Connected) (ab : G.Adj a b)
    {C D : Cmp G a b} (cd : C≠D) {x y : V}
    (xc : x∈Shore C) (yd : y∈Shore D) :
    compat (key G a b x) (key G a b y) ↔ Even (G.dist x y) := by
  have out : y∉Shore C := fun h=>disjoint_left.mp (shore_disjoint cd) h yd
  obtain ⟨ax,bx,px⟩ := key_facts hc ab x
  obtain ⟨ay,by',py⟩ := key_facts hc ab y
  have h := cross_metric (Shore C) hc xc out (shore_closed C)
  rw [dist_comm (G:=G) (u:=x) (v:=a),dist_comm (G:=G) (u:=x) (v:=b),ax,bx,ay,by'] at h
  have e : G.dist x y=depth G a b x+depth G a b y+
      min (sa (key G a b x)+sa (key G a b y)) (sb (key G a b x)+sb (key G a b y)) := by
    rw [h]
    simp only [←Nat.add_min_add_left]
    ac_rfl
  simp only [compat,Nat.even_iff,e]
  omega

private theorem selected_card (C : Cmp G a b) (s : Fin 6→Prop) [DecidablePred s] :
    ((Shore C).filter (fun v=>s (key G a b v))).card =
      ∑ i : Fin 6, if s i then (classSet C i).card else 0 := by
  classical
  let T : Finset (Fin 6) := univ.filter s
  have eq := Finset.sum_card_fiberwise_eq_card_filter (Shore C) T (key G a b)
  simpa only [T, Finset.sum_filter,mem_filter,mem_univ,true_and,classSet] using eq.symm

end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
