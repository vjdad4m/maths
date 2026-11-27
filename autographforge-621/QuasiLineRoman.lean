import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FinCases
import Mathlib.Data.Nat.Lattice

/-! AutoGraphForge normalized row 621, generated ID 0ec32efb. -/
namespace QuasiLineRoman621
open SimpleGraph Finset
variable {V : Type*} (G : SimpleGraph V)

/-- The induced-claw predicate and Roman optimizer used in the row 372 proof. -/
def ClawFree := ∀ v a b c : V, G.Adj v a → G.Adj v b → G.Adj v c →
  a ≠ b → a ≠ c → b ≠ c → G.Adj a b ∨ G.Adj a c ∨ G.Adj b c

def Roman (f : V → Fin 3) : Prop := ∀ v, f v = 0 → ∃ u, G.Adj v u ∧ f u = 2

noncomputable def romanNumber [Fintype V] :=
  sInf {n | ∃ f : V → Fin 3, Roman G f ∧ ∑ v, (f v : ℕ) = n}

/-- Every open neighborhood can be partitioned into two cliques, allowing empty parts. -/
def QuasiLine := ∀ v : V, ∃ side : V → Bool, ∀ x y, G.Adj v x → G.Adj v y →
  x ≠ y → side x = side y → G.Adj x y

/-- GraphCalc colors the complement optimally and counts its nonempty color classes. -/
noncomputable def vertexCliqueCover [Fintype V] := sInf {n : ℕ | Gᶜ.Colorable n}

theorem cover_eq_chromatic [Fintype V] : (vertexCliqueCover G : ℕ∞) = Gᶜ.chromaticNumber := by
  exact Gᶜ.colorable_of_fintype.chromaticNumber_eq_sInf.symm

/-- One unit of Roman weight provides one clique slot. A zero is sent to one
of the two slots of its chosen defender according to that defender's local partition. -/
theorem cover_of_roman [Fintype V] (hq : QuasiLine G) {f : V → Fin 3} (hf : Roman G f) :
    Gᶜ.Colorable (∑ v, (f v : ℕ)) := by
  classical
  choose side sameSide using hq
  let owner (v : V) := if h : f v = 0 then (hf v h).choose else v
  have zeroOwner {v : V} (h : f v = 0) : G.Adj v (owner v) ∧ f (owner v) = 2 := by
    simpa [owner,h] using (hf v h).choose_spec
  have own {v : V} (h : f v ≠ 0) : owner v = v := by simp [owner,h]
  let place (v : V) : ℕ := if f v = 0 ∧ side (owner v) v = true then 1 else 0
  have fits (v : V) : place v < (f (owner v)).val := by
    by_cases h : f v = 0
    · rw [(zeroOwner h).2]
      unfold place
      split <;> decide
    · simp [place,h,own h]
      exact Nat.pos_of_ne_zero (fun eq => h (Fin.ext eq))
  let slot (v : V) : Σ u : V, Fin (f u).val := ⟨owner v, ⟨place v, fits v⟩⟩
  have proper : ∀ {x y}, Gᶜ.Adj x y → slot x ≠ slot y := by
    intro x y nonedge eq
    obtain ⟨ne,na⟩ := (G.compl_adj x y).mp nonedge
    have owners : owner x = owner y := congrArg Sigma.fst eq
    have places : place x = place y := congrArg (fun t : Σ u : V, Fin (f u).val => t.2.val) eq
    by_cases hx : f x = 0
    · by_cases hy : f y = 0
      · have vx := (zeroOwner hx).1.symm
        have vy := (zeroOwner hy).1.symm
        rw [← owners] at vy
        apply na (sameSide (owner x) x y vx vy ne ?_)
        simp only [place,hx,hy,true_and,← owners] at places
        cases h1 : side (owner x) x <;> cases h2 : side (owner x) y <;> simp_all
      · exact na (by simpa [owners, own hy] using (zeroOwner hx).1)
    · by_cases hy : f y = 0
      · exact na (by simpa [← owners, own hx] using (zeroOwner hy).1.symm)
      · exact ne (by simpa [own hx, own hy] using owners)
  let coloring : Gᶜ.Coloring (Σ u : V, Fin (f u).val) := Coloring.mk slot proper
  simpa using coloring.colorable

theorem quasiline_bound [Fintype V] (hq : QuasiLine G) :
    vertexCliqueCover G ≤ romanNumber G := by
  let sizes := {n | ∃ f : V → Fin 3, Roman G f ∧ ∑ v, (f v : ℕ) = n}
  have feasible : sizes.Nonempty :=
    ⟨_, fun _ => 1, fun _ h => False.elim ((by decide : (1 : Fin 3) ≠ 0) h), rfl⟩
  obtain ⟨f,hf,cost⟩ := Nat.sInf_mem feasible
  apply Nat.sInf_le
  rw [← show ∑ v, (f v : ℕ) = romanNumber G from cost]
  exact cover_of_roman G hq hf

/-- Six bits record the unordered pairs on four slots. The diagonal is compatible. -/
private def pairBit (b : Fin 6 → Bool) : Fin 4 → Fin 4 → Bool
  | 0,1 | 1,0 => b 0
  | 0,2 | 2,0 => b 1
  | 0,3 | 3,0 => b 2
  | 1,2 | 2,1 => b 3
  | 1,3 | 3,1 => b 4
  | 2,3 | 3,2 => b 5
  | _,_ => true

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem four_slots : ∀ b : Fin 6 → Bool,
    (∀ i j k, pairBit b i j = true ∨ pairBit b i k = true ∨ pairBit b j k = true) →
    ∃ side : Fin 4 → Bool, ∀ i j, side i = side j → pairBit b i j = true := by decide

/-- A claw-free neighborhood of at most four vertices has a two-clique partition. -/
theorem quasiline_of_degree_four [Fintype V] [DecidableRel G.Adj]
    (hf : ClawFree G) (deg : ∀ v, G.degree v ≤ 4) : QuasiLine G := by
  classical
  intro v
  let N := ↥(G.neighborFinset v)
  by_cases hn : Nonempty N
  · letI := hn
    have bound : Fintype.card N ≤ Fintype.card (Fin 4) := by
      rw [Fintype.card_fin]
      change Fintype.card ↥(G.neighborFinset v) ≤ 4
      rw [Fintype.card_coe]
      exact deg v
    let index : N ↪ Fin 4 := (Function.Embedding.nonempty_of_card_le bound).some
    let lift := Function.invFun index
    have keep : ∀ x, lift (index x) = x := Function.leftInverse_invFun index.injective
    let vertex (i : Fin 4) : V := (lift i).val
    let R (i j : Fin 4) := vertex i = vertex j ∨ G.Adj (vertex i) (vertex j)
    have symm (i j : Fin 4) : R i j ↔ R j i := or_congr eq_comm (G.adj_comm _ _)
    let b : Fin 6 → Bool := ![decide (R 0 1), decide (R 0 2), decide (R 0 3),
      decide (R 1 2), decide (R 1 3), decide (R 2 3)]
    have decode (i j : Fin 4) : pairBit b i j = true ↔ R i j := by
      fin_cases i <;> fin_cases j <;> first
        | exact iff_of_true (by rfl) (Or.inl rfl)
        | exact decide_eq_true_iff
        | exact decide_eq_true_iff.trans (symm _ _)
    have neighbor (i : Fin 4) : G.Adj v (vertex i) :=
      (G.mem_neighborFinset _ _).mp (lift i).property
    have triple (i j k : Fin 4) : R i j ∨ R i k ∨ R j k := by
      by_cases ij : vertex i = vertex j
      · exact Or.inl (Or.inl ij)
      by_cases ik : vertex i = vertex k
      · exact Or.inr (Or.inl (Or.inl ik))
      by_cases jk : vertex j = vertex k
      · exact Or.inr (Or.inr (Or.inl jk))
      rcases hf v _ _ _ (neighbor i) (neighbor j) (neighbor k) ij ik jk with e | e | e
      · exact Or.inl (Or.inr e)
      · exact Or.inr (Or.inl (Or.inr e))
      · exact Or.inr (Or.inr (Or.inr e))
    obtain ⟨side, hs⟩ := four_slots b (fun i j k => by simpa only [decode] using triple i j k)
    refine ⟨fun x => if h : x ∈ G.neighborFinset v then side (index ⟨x,h⟩) else false, ?_⟩
    intro x y vx vy ne eq
    have mx := (G.mem_neighborFinset v x).mpr vx
    have my := (G.mem_neighborFinset v y).mpr vy
    simp only [dif_pos mx,dif_pos my] at eq
    have comp := (decode _ _).mp (hs _ _ eq)
    change (lift (index ⟨x,mx⟩)).val = (lift (index ⟨y,my⟩)).val ∨
      G.Adj (lift (index ⟨x,mx⟩)).val (lift (index ⟨y,my⟩)).val at comp
    simpa only [keep, ne, false_or] using comp
  · exact ⟨fun _ => false, fun x _ vx _ _ _ => (hn ⟨⟨x,(G.mem_neighborFinset _ _).mpr vx⟩⟩).elim⟩

theorem row621 [Fintype V] [DecidableRel G.Adj] (_hn : 2 ≤ Fintype.card V)
    (hf : ClawFree G) (deg : ∀ v, G.degree v ≤ 3) :
    vertexCliqueCover G ≤ romanNumber G :=
  quasiline_bound G (quasiline_of_degree_four G hf (fun v => (deg v).trans (by decide)))

/-- Hub 0 joined to the cycle 1,2,3,4,5,1. -/
private def rimOrSpoke (u v : Fin 6) : Prop :=
  u = 0 ∨ u.val + 1 = v.val ∨ (u = 5 ∧ v = 1)

def wheel : SimpleGraph (Fin 6) := SimpleGraph.fromRel rimOrSpoke

instance : DecidableRel wheel.Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧
    ((u = 0 ∨ u.val + 1 = v.val ∨ (u = 5 ∧ v = 1)) ∨
      (v = 0 ∨ v.val + 1 = u.val ∨ (v = 5 ∧ u = 1)))))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
set_option synthInstance.maxSize 2048 in
/-- The degree threshold 4 cannot be extended to 5. -/
theorem degree_five_boundary : ClawFree wheel ∧ wheel.degree 0 = 5 ∧
    (∀ v, wheel.degree v ≤ 5) ∧ vertexCliqueCover wheel = 3 ∧ romanNumber wheel = 2 := by
  refine ⟨?_, by decide, by decide, ?_, ?_⟩
  · unfold ClawFree
    decide
  · let color : Fin 6 → Fin 3 := ![0,0,0,1,1,2]
    have proper : ∀ u v, wheelᶜ.Adj u v → color u ≠ color v := by decide
    have three : wheelᶜ.Colorable 3 := ⟨Coloring.mk color (fun h => proper _ _ h)⟩
    have collision : ∀ f : Fin 6 → Fin 2, ∃ x y, wheelᶜ.Adj x y ∧ f x = f y := by decide
    have noc : ¬wheelᶜ.Colorable 2 := by
      rintro ⟨c⟩
      obtain ⟨x,y,xy,eq⟩ := collision c
      exact c.valid xy eq
    have upper : vertexCliqueCover wheel ≤ 3 := Nat.sInf_le three
    have att : wheelᶜ.Colorable (vertexCliqueCover wheel) :=
      Nat.sInf_mem (s := {k | wheelᶜ.Colorable k}) ⟨3,three⟩
    exact le_antisymm upper (Nat.le_of_not_lt fun h => noc (att.mono (Nat.le_of_lt_succ h)))
  · let f : Fin 6 → Fin 3 := fun v => if v=0 then 2 else 0
    have valid : Roman wheel f := by unfold Roman; decide
    let sizes := {n | ∃ g : Fin 6 → Fin 3, Roman wheel g ∧ ∑ v, (g v : ℕ) = n}
    have two : 2 ∈ sizes := ⟨f,valid,by decide⟩
    have lb (g : Fin 6 → Fin 3) (hg : Roman wheel g) : 2 ≤ ∑ v, (g v : ℕ) := by
      by_cases h : ∃ v, g v = 2
      · obtain ⟨v,hv⟩ := h
        have bound := Finset.single_le_sum (f := fun u : Fin 6 => (g u : ℕ))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
        simpa [hv] using bound
      · have positive (v : Fin 6) : 1 ≤ (g v : ℕ) := by
          apply Nat.pos_of_ne_zero
          intro zero
          obtain ⟨u,_,two⟩ := hg v (Fin.ext zero)
          exact h ⟨u,two⟩
        have bound := Finset.sum_le_sum (s := (univ : Finset (Fin 6)))
          (f := fun _ => 1) (g := fun u => (g u : ℕ)) (fun u _ => positive u)
        exact le_trans (by decide : 2 ≤ 6) (by simpa using bound)
    obtain ⟨g,hg,cost⟩ := Nat.sInf_mem (show sizes.Nonempty from ⟨_,two⟩)
    exact le_antisymm (Nat.sInf_le two) ((lb g hg).trans_eq cost)

#print axioms cover_eq_chromatic
#print axioms quasiline_bound
#print axioms quasiline_of_degree_four
#print axioms row621
#print axioms degree_five_boundary
end QuasiLineRoman621
