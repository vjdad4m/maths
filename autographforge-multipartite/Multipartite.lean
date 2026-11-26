import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Data.Nat.Lattice
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Sigma

/-! Four normalized Eulerian rows in Ján Pastorek's AutoGraphForge, using one
complete multipartite clique-cover theorem and the same biclique family. -/
namespace Multipartite
open SimpleGraph Finset
open scoped BigOperators

def CliquePartition {U : Type*} (G : SimpleGraph U) (k : ℕ) : Prop :=
  ∃ f : U → Fin k, ∀ a b, f a = f b → a ≠ b → G.Adj a b

noncomputable def vertexCliqueCover {U : Type*} (G : SimpleGraph U) : ℕ :=
  sInf {k | CliquePartition G k}

theorem cliquePartition_iff_complement_colorable {U : Type*} (G : SimpleGraph U) (k : ℕ) :
    CliquePartition G k ↔ Nonempty (Gᶜ →g (⊤ : SimpleGraph (Fin k))) := by
  constructor
  · rintro ⟨f,h⟩
    exact ⟨⟨f,fun {a b} e eq =>
      ((G.compl_adj a b).mp e).2 (h a b eq ((G.compl_adj a b).mp e).1)⟩⟩
  · rintro ⟨f⟩
    refine ⟨f,fun a b eq ne => ?_⟩
    by_contra missing
    exact f.map_rel ((G.compl_adj a b).mpr ⟨ne,missing⟩) eq


/-- A clique color can occur at most once in each part. Conversely, each part
can label its own vertices independently with any sufficiently large palette. -/
theorem partition_iff_parts_fit {I : Type*} (P : I → Type*) [∀ i, Fintype (P i)] (k : ℕ) :
    CliquePartition (completeMultipartiteGraph P) k ↔ ∀ i, Fintype.card (P i) ≤ k := by
  classical
  constructor
  · rintro ⟨color,proper⟩ i
    have inj : Function.Injective (fun x : P i => color ⟨i,x⟩) := by
      intro x y eq
      by_contra ne
      have edge := proper ⟨i,x⟩ ⟨i,y⟩ eq (fun h => ne (by simpa using h))
      exact edge rfl
    simpa using Fintype.card_le_of_injective _ inj
  · intro capacity
    let label (i : I) (x : P i) : Fin k := Fin.castLE (capacity i) (Fintype.equivFin (P i) x)
    refine ⟨fun v => label v.1 v.2,?_⟩
    rintro ⟨i,x⟩ ⟨j,y⟩ same distinct (rfl : i=j)
    have eq : Fintype.equivFin (P i) x = Fintype.equivFin (P i) y := Fin.ext (congrArg (fun c : Fin k => c.val) same)
    exact distinct (by rw [(Fintype.equivFin (P i)).injective eq])

theorem clique_cover_complete_multipartite {I : Type*} [Fintype I] (P : I → Type*)
    [∀ i, Fintype (P i)] :
    vertexCliqueCover (completeMultipartiteGraph P) = univ.sup (fun i => Fintype.card (P i)) := by
  classical
  let G := completeMultipartiteGraph P
  let largest := univ.sup (fun i => Fintype.card (P i))
  have good : CliquePartition G largest := (partition_iff_parts_fit P _).mpr
    (fun i => le_sup (s := univ) (f := fun i => Fintype.card (P i)) (mem_univ i))
  apply Nat.le_antisymm (Nat.sInf_le (s := {k | CliquePartition G k}) good)
  have opt := Nat.sInf_mem (s := {k | CliquePartition G k}) ⟨_,good⟩
  exact Finset.sup_le (fun i _ => (partition_iff_parts_fit P _).mp opt i)

inductive Observed {V : Type*} (G : SimpleGraph V) (S : Finset V) : V → Prop where
  | root {v} (h : v ∈ S) : Observed G S v
  | neighbor {v w} (h : w ∈ S) (hvw : G.Adj v w) : Observed G S v
  | force {v w} (hvw : G.Adj v w) (hw : Observed G S w)
      (rest : ∀ u, G.Adj w u → u ≠ v → Observed G S u) : Observed G S v

noncomputable def power {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {n | ∃ S : Finset V, n = S.card ∧ ∀ v, Observed G S v}

def Roman {U : Type*} (G : SimpleGraph U) (f : U → Fin 3) : Prop :=
  ∀ v, f v=0 → ∃ u, G.Adj v u ∧ f u=2
noncomputable def romanNumber {U : Type*} [Fintype U] (G : SimpleGraph U) :=
  sInf {n | ∃ f : U → Fin 3, Roman G f ∧ ∑ v, (f v:ℕ) = n}

def TotalDominates {U : Type*} (G : SimpleGraph U) (D : Finset U) : Prop :=
  ∀ v, ∃ w ∈ D, G.Adj v w
noncomputable def totalDominationNumber {U : Type*} (G : SimpleGraph U) : ℕ :=
  sInf {k | ∃ D : Finset U, TotalDominates G D ∧ D.card = k}

def IsDominatingSet {U : Type*} (G : SimpleGraph U) (s : Finset U) : Prop :=
  ∀ v, v ∈ s ∨ ∃ w ∈ s, G.Adj v w
noncomputable def dominationNumber {U : Type*} (G : SimpleGraph U) : ℕ :=
  sInf {n | ∃ s : Finset U, s.card = n ∧ IsDominatingSet G s}

def Eulerian {U : Type*} [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj] : Prop :=
  G.Connected ∧ ∀ v, Even (G.degree v)

abbrev parts (n : ℕ) (b : Bool) := Fin (if b then n else 2)

abbrev V (n : ℕ) := Σ b, parts n b
abbrev K (n : ℕ) := completeMultipartiteGraph (parts n)
abbrev left {n : ℕ} (i : Fin 2) : V n := ⟨false,i⟩
abbrev right {n : ℕ} (i : Fin n) : V n := ⟨true,i⟩

theorem cover_biclique {n : ℕ} (hn : 2 ≤ n) : vertexCliqueCover (K n) = n := by
  rw [clique_cover_complete_multipartite]
  apply le_antisymm
  · apply Finset.sup_le
    intro b _
    cases b
    · simpa [parts] using hn
    · simp [parts]
  · calc
      n = Fintype.card (parts n true) := by simp [parts]
      _ ≤ _ := Finset.le_sup (s := (univ : Finset Bool)) (f := fun b => Fintype.card (parts n b)) (mem_univ true)

private def romanPaint {n : ℕ} (v : V n) : Fin 3 :=
  if v=left 0 then 2 else if v=left 1 then 1 else 0

theorem roman_bound (n : ℕ) : romanNumber (K n) ≤ 3 := by
  apply Nat.sInf_le (s := {k | ∃ f : V n → Fin 3, Roman (K n) f ∧ ∑ v, (f v:ℕ) = k})
  refine ⟨romanPaint,?_,?_⟩
  · rintro ⟨b,i⟩ blank
    cases b
    · change Fin 2 at i
      have e : i = (0 : Fin 2) ∨ i = (1 : Fin 2) := by
        omega
      rcases e with rfl | rfl <;> simp [romanPaint] at blank
    · refine ⟨left 0, ?_, ?_⟩
      · intro h
        cases h
      · simp [romanPaint]
  · have values (v : V n) : (romanPaint v : ℕ) =
        (if v=left 0 then 2 else 0) + (if v=left 1 then 1 else 0) := by
      unfold romanPaint
      split_ifs <;> simp_all [left]
    simp_rw [values]
    simp [sum_add_distrib]

theorem total_domination_bounds {n : ℕ} (j : Fin n) :
    totalDominationNumber (K n) ≤ 2 ∧ dominationNumber (K n) ≤ 2 := by
  let D : Finset (V n) := {left 0, right j}
  have td : TotalDominates (K n) D := by
    rintro ⟨b,i⟩
    cases b
    · exact ⟨right j,by simp [D],by intro h; cases h⟩
    · exact ⟨left 0,by simp [D],by intro h; cases h⟩
  have ct : D.card = 2 := by simp [D]
  exact ⟨Nat.sInf_le (s := {k | ∃ S : Finset (V n), TotalDominates (K n) S ∧ S.card=k}) ⟨D,td,ct⟩,
    Nat.sInf_le (s := {k | ∃ S : Finset (V n), S.card=k ∧ IsDominatingSet (K n) S})
      ⟨D,ct,fun v => Or.inr (td v)⟩⟩

theorem power_bound {n : ℕ} (j : Fin n) : power (K n) ≤ 1 := by
  let S : Finset (V n) := {left 0}
  apply Nat.sInf_le (s := {k | ∃ S : Finset (V n), k=S.card ∧ ∀ v, Observed (K n) S v})
  refine ⟨S,by simp [S],?_⟩
  have seed : left 0 ∈ S := mem_singleton_self _
  have seen (i : Fin n) : Observed (K n) S (right i) := Observed.neighbor seed (by intro h; cases h)
  rintro ⟨b,i⟩
  cases b
  · change Fin 2 at i
    by_cases eq : i = (0 : Fin 2)
    · subst i
      exact Observed.root seed
    · refine Observed.force (w := right j) (by intro h; cases h) (seen j) ?_
      rintro ⟨b',u⟩ adj ne
      cases b'
      · change Fin 2 at u
        have diff : (u : Fin 2) ≠ i := fun h => ne (by rw [h])
        have zero : (u : Fin 2)=0 := by omega
        subst u
        exact Observed.root seed
      · exact (adj rfl).elim
  · exact seen i

private theorem deg_left {n : ℕ} (i : Fin 2) : (K n).degree (left i) = n := by
  let f (j : Fin n) : (K n).neighborSet (left i) := ⟨right j,by intro h; cases h⟩
  have bij : Function.Bijective f := by
    constructor
    · intro a b eq
      simpa [f] using congrArg Subtype.val eq
    · rintro ⟨⟨b,j⟩,edge⟩
      cases b
      · exact (edge rfl).elim
      · exact ⟨j,rfl⟩
  rw [← card_neighborSet_eq_degree]
  exact (Fintype.card_congr (Equiv.ofBijective f bij)).symm.trans (Fintype.card_fin _)

private theorem deg_right {n : ℕ} (j : Fin n) : (K n).degree (right j) = 2 := by
  let f (i : Fin 2) : (K n).neighborSet (right j) := ⟨left i,by intro h; cases h⟩
  have bij : Function.Bijective f := by
    constructor
    · intro a b eq
      simpa [f] using congrArg Subtype.val eq
    · rintro ⟨⟨b,i⟩,edge⟩
      cases b
      · exact ⟨i,rfl⟩
      · exact (edge rfl).elim
  rw [← card_neighborSet_eq_degree]
  exact (Fintype.card_congr (Equiv.ofBijective f bij)).symm.trans (Fintype.card_fin _)

theorem even_biclique {n : ℕ} (hn : 0 < n) (even : Even n) : Eulerian (K n) := by
  let j : Fin n := ⟨0,hn⟩
  have reach (v : V n) : (K n).Reachable v (left 0) := by
    rcases v with ⟨b,i⟩
    cases b
    · exact (show (K n).Adj (left i) (right j) from fun h => by cases h).reachable.trans
        (show (K n).Adj (right j) (left 0) from fun h => by cases h).reachable
    · exact (show (K n).Adj (right i) (left 0) from fun h => by cases h).reachable
  haveI : Nonempty (V n) := ⟨left 0⟩
  refine ⟨⟨fun x y => (reach x).trans (reach y).symm⟩,?_⟩
  rintro ⟨b,i⟩
  cases b
  · change Even ((K n).degree (left i))
    rw [deg_left]
    exact even
  · change Even ((K n).degree (right i))
    rw [deg_right]
    decide

theorem triangle_free (n : ℕ) : (K n).CliqueFree 3 :=
  cliqueFree_completeMultipartiteGraph (parts n) (by decide)

theorem family_violations {n : ℕ} (hn : 11 ≤ n) (he : Even n) :
    Eulerian (K n) ∧ (K n).CliqueFree 3 ∧
    romanNumber (K n) + 7 < vertexCliqueCover (K n) ∧
    totalDominationNumber (K n) + 8 < vertexCliqueCover (K n) ∧
    2 * power (K n) + 8 < vertexCliqueCover (K n) ∧
    2 * dominationNumber (K n) + 6 < vertexCliqueCover (K n) := by
  let j : Fin n := ⟨0,by omega⟩
  have roman := roman_bound n
  obtain ⟨total,dom⟩ := total_domination_bounds j
  have pow := power_bound j
  rw [cover_biclique (by omega)]
  exact ⟨even_biclique (by omega) he,triangle_free n,by omega,by omega,by omega,by omega⟩


/-- Three domination certificates that apply to any universal vertex with a neighbor. -/
theorem universal_bounds {U : Type*} [Fintype U] (G : SimpleGraph U) (hub other : U)
    (distinct : hub ≠ other) (universal : ∀ v, v ≠ hub → G.Adj v hub) :
    romanNumber G ≤ 2 ∧ totalDominationNumber G ≤ 2 ∧ power G ≤ 1 := by
  classical
  let f (v : U) : Fin 3 := if v=hub then 2 else 0
  have valid : Roman G f := by
    intro v zero
    have ne : v ≠ hub := by rintro rfl; simp [f] at zero
    exact ⟨hub,universal v ne,by simp [f]⟩
  have wt : ∑ v, (f v : ℕ) = 2 := by
    have val (v : U) : (f v : ℕ) = if v=hub then 2 else 0 := by
      by_cases h : v=hub <;> simp [f,h]
    simp_rw [val]
    simp
  let pair : Finset U := {hub,other}
  have total : TotalDominates G pair := by
    intro v
    by_cases h : v=hub
    · subst v
      exact ⟨other,by simp [pair],(universal other distinct.symm).symm⟩
    · exact ⟨hub,by simp [pair],universal v h⟩
  let single : Finset U := {hub}
  have obs (v : U) : Observed G single v := by
    by_cases h : v=hub
    · subst v
      exact Observed.root (mem_singleton_self _)
    · exact Observed.neighbor (mem_singleton_self _) (universal v h)
  exact ⟨Nat.sInf_le (s := {k | ∃ g : U → Fin 3, Roman G g ∧ ∑ v, (g v:ℕ)=k}) ⟨f,valid,wt⟩,
    Nat.sInf_le (s := {k | ∃ S : Finset U, TotalDominates G S ∧ S.card=k})
      ⟨pair,total,by simp [pair,distinct]⟩,
    Nat.sInf_le (s := {k | ∃ S : Finset U, k=S.card ∧ ∀ v, Observed G S v})
      ⟨single,by simp [single],obs⟩⟩

abbrev threeParts (i : Fin 3) := Fin (if i = 2 then 11 else 1)
abbrev smallGraph := completeMultipartiteGraph threeParts
abbrev smallHub : Σ i, threeParts i := ⟨0,0⟩
abbrev smallOther : Σ i, threeParts i := ⟨1,0⟩

/-- A smaller, triangle-containing witness for precisely the first three domains. -/
theorem smaller_tripartite :
    2 ≤ Fintype.card (Σ i, threeParts i) ∧ Eulerian smallGraph ∧
    ¬ smallGraph.CliqueFree 3 ∧ vertexCliqueCover smallGraph = 11 ∧
    romanNumber smallGraph + 7 < vertexCliqueCover smallGraph ∧
    totalDominationNumber smallGraph + 8 < vertexCliqueCover smallGraph ∧
    2 * power smallGraph + 8 < vertexCliqueCover smallGraph := by
  have uni : ∀ v, v ≠ smallHub → smallGraph.Adj v smallHub := by decide
  have reach (v) : smallGraph.Reachable v smallHub := by
    by_cases h : v=smallHub
    · subst v
      exact .refl _
    · exact (uni v h).reachable
  haveI : Nonempty (Σ i, threeParts i) := ⟨smallHub⟩
  have eu : Eulerian smallGraph := ⟨⟨fun v w => (reach v).trans (reach w).symm⟩,by decide⟩
  have tri : smallGraph.IsNClique 3 {smallHub,smallOther,⟨2,0⟩} := by decide
  have cover : vertexCliqueCover smallGraph = 11 := by rw [clique_cover_complete_multipartite]; decide
  obtain ⟨r,t,p⟩ := universal_bounds smallGraph smallHub smallOther (by decide) uni
  exact ⟨by decide,eu,fun free => free _ tri,cover,by omega,by omega,by omega⟩

private abbrev witness := @family_violations 12 (by decide) (by decide)
private theorem nontrivial_witness : 2 ≤ Fintype.card (V 12) := by decide

theorem row2452_false : ¬ (∀ (U : Type) [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj],
    2 ≤ Fintype.card U → Eulerian G → vertexCliqueCover G ≤ romanNumber G + 7) := by
  intro claim
  exact (Nat.not_le_of_gt witness.2.2.1) (claim (V 12) (K 12) nontrivial_witness witness.1)

theorem row2453_false : ¬ (∀ (U : Type) [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj],
    2 ≤ Fintype.card U → Eulerian G → vertexCliqueCover G ≤ totalDominationNumber G + 8) := by
  intro claim
  exact (Nat.not_le_of_gt witness.2.2.2.1) (claim (V 12) (K 12) nontrivial_witness witness.1)

theorem row2474_false : ¬ (∀ (U : Type) [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj],
    2 ≤ Fintype.card U → Eulerian G → vertexCliqueCover G ≤ 2 * power G + 8) := by
  intro claim
  exact (Nat.not_le_of_gt witness.2.2.2.2.1) (claim (V 12) (K 12) nontrivial_witness witness.1)

theorem row2482_false : ¬ (∀ (U : Type) [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj],
    2 ≤ Fintype.card U → Eulerian G → G.CliqueFree 3 → vertexCliqueCover G ≤ 2 * dominationNumber G + 6) := by
  intro claim
  exact (Nat.not_le_of_gt witness.2.2.2.2.2) (claim (V 12) (K 12) nontrivial_witness witness.1 witness.2.1)

#print axioms clique_cover_complete_multipartite
#print axioms family_violations
#print axioms smaller_tripartite
#print axioms row2452_false
#print axioms row2453_false
#print axioms row2474_false
#print axioms row2482_false
end Multipartite
