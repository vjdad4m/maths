import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Data.Nat.Lattice
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega

/-! Ján Pastorek's AutoGraphForge, pinned normalized line 1080, ID fa7f6f9d.
We reproduce just the operation definitions from lines 373 and 357 so the
file replays independently. The PSD biclique formula is due to prior work; see
Hogben, Lin and Shader, Theorem 9.44 (doi:10.1090/surv/270). -/
namespace AutoGraphForge373
open SimpleGraph Finset
open Classical
noncomputable section
variable {V : Type*} (G : SimpleGraph V)

/-- Same predicate as upstream IsCographClass and published line 378. -/
def Cograph := ∀ a b c d : V, G.Adj a b → G.Adj b c → G.Adj c d →
  ¬G.Adj a c → ¬G.Adj b d → G.Adj a d

/-- Two vertices in the same component of the induced white graph. -/
def WhiteConnected (B : Set V) (a b : V) : Prop :=
  ∃ (ha : a ∉ B) (hb : b ∉ B),
    (G.induce Bᶜ).Reachable ⟨a, ha⟩ ⟨b, hb⟩

def step (B : Set V) : Set V := {w | w ∈ B ∨ w ∉ B ∧ ∃ v ∈ B, G.Adj v w ∧
  ∀ u, G.Adj v u → WhiteConnected G B w u → u = w}

def round (S : Finset V) : ℕ → Set V
  | 0 => ↑S
  | n+1 => step G (round S n)

def PSDSet (S : Finset V) : Prop := ∃ n, ∀ v, v ∈ round G S n

def psd : ℕ := sInf {n | ∃ S : Finset V, n = S.card ∧ PSDSet G S}

end
end AutoGraphForge373

namespace AutoGraphForge357
open Finset SimpleGraph
/-- GraphCalc permits exactly one of the three colors, or 0 (uncolored).
An uncolored vertex sees all three colors. -/
def Rainbow {U : Type*} (G : SimpleGraph U) (f : U → Fin 4) : Prop :=
  ∀ v, f v = 0 → ∀ c : Fin 4, c ≠ 0 → ∃ w, G.Adj v w ∧ f w = c
def weight {U : Type*} [Fintype U] (f : U → Fin 4) : ℕ := (univ.filter (fun v => f v ≠ 0)).card
noncomputable def rainbowNumber {U : Type*} [Fintype U] (G : SimpleGraph U) :=
  sInf {k | ∃ f : U → Fin 4, weight f = k ∧ Rainbow G f}
end AutoGraphForge357

namespace AutoGraphForge1080
open Finset SimpleGraph AutoGraphForge373 AutoGraphForge357
open Classical
noncomputable section
abbrev Vertex (n : ℕ) := Bool × Fin n

def biclique (n : ℕ) : SimpleGraph (Vertex n) where
  Adj x y := x.1 ≠ y.1
  symm := fun _ _ h => h.symm
  loopless := fun _ => not_ne_iff.mpr rfl

private theorem opp {a b : Bool} (h : a ≠ b) : a = !b := by
  cases a <;> cases b <;> simp_all

theorem biclique_class (n : ℕ) : Cograph (biclique n) ∧
    Nonempty (biclique n →g (⊤ : SimpleGraph (Fin 2))) := by
  have chain : ∀ a b c d : Bool, a ≠ b → b ≠ c → c ≠ d → a ≠ d := by decide
  refine ⟨fun a b c d ab bc cd _ _ => chain a.1 b.1 c.1 d.1 ab bc cd, ?_⟩
  let sideColor (b : Bool) : Fin 2 := if b then 1 else 0
  have proper : ∀ a b, a ≠ b → sideColor a ≠ sideColor b := by decide
  exact ⟨⟨fun x => sideColor x.1, fun {x y} e => proper x.1 y.1 e⟩⟩

variable {n : ℕ}

private def part (b : Bool) : Finset (Vertex n) :=
  univ.map ⟨fun i => (b,i), fun _ _ h => congrArg Prod.snd h⟩

@[simp] private theorem mem_part {b : Bool} {x : Vertex n} : x ∈ part b ↔ x.1 = b := by
  rcases x with ⟨a,i⟩
  simp [part, Prod.mk.injEq, eq_comm]

@[simp] private theorem card_part (b : Bool) : (part (n := n) b).card = n := by simp [part]

private theorem missing (S : Finset (Vertex n)) (small : S.card < n) (b : Bool) :
    ∃ w ∈ part b, w ∉ S := by
  by_contra! no
  have h := card_le_card (show part b ⊆ S from no)
  simp only [card_part] at h
  omega

/-- Fewer than n seeds leave the white subgraph connected. A first force would
require the forcer and all but one vertex of the opposite part among the seeds. -/
private theorem no_growth (S : Finset (Vertex n)) (small : S.card < n) :
    AutoGraphForge373.step (biclique n) (↑S) = (↑S : Set (Vertex n)) := by
  ext w
  constructor
  · rintro (old | ⟨white,v,hv,vw,unique⟩)
    · exact old
    · obtain ⟨a,ha,aw⟩ := missing S small v.1
      have av := mem_part.mp ha
      have vw' : v.1 ≠ w.1 := vw
      have rest : (part w.1).erase w ⊆ S := by
        intro u hu
        obtain ⟨diff,mem⟩ := mem_erase.mp hu
        have uw := mem_part.mp mem
        by_contra un
        have e₁ : ((biclique n).induce (↑S : Set (Vertex n))ᶜ).Adj ⟨w,white⟩ ⟨a,aw⟩ :=
          show w.1 ≠ a.1 from av ▸ vw'.symm
        have e₂ : ((biclique n).induce (↑S : Set (Vertex n))ᶜ).Adj ⟨a,aw⟩ ⟨u,un⟩ :=
          show a.1 ≠ u.1 from by rwa [av,uw]
        exact diff (unique u (show v.1 ≠ u.1 from uw ▸ vw')
          ⟨white,un,e₁.reachable.trans e₂.reachable⟩)
      have hvnot : v ∉ (part w.1).erase w := fun h => vw' (mem_part.mp (mem_erase.mp h).2)
      have count := card_le_card (insert_subset (show v ∈ S from hv) rest)
      have er := card_erase_add_one (s := part w.1) (show w ∈ part w.1 from mem_part.mpr rfl)
      rw [card_insert_of_not_mem hvnot] at count
      rw [card_part] at er
      omega
  · exact fun h => Or.inl h

/-- The established balanced-biclique PSD formula, using the source's parallel rounds. -/
theorem psd_biclique (hn : 0 < n) : psd (biclique n) = n := by
  classical
  let G := biclique n
  let S := part (n := n) true
  have full : PSDSet G S := by
    refine ⟨1, fun w => ?_⟩
    by_cases hw : w ∈ S
    · exact Or.inl hw
    · have sw : w.1 = false := by
        have h : w.1 ≠ true := fun e => hw (mem_part.mpr e)
        simpa only [Bool.not_true] using (opp h)
      let v : Vertex n := (true,⟨0,hn⟩)
      refine Or.inr ⟨hw,v,mem_part.mpr rfl,show true ≠ w.1 from by simp [sw],?_⟩
      rintro u _ ⟨ww,uw,⟨p⟩⟩
      have allWhite (x : ↥((↑S : Set (Vertex n))ᶜ)) : x.val.1 = false := by
        have no : x.val.1 ≠ true := fun e => x.property (mem_part.mpr e)
        simpa only [Bool.not_true] using (opp no)
      have trivial {x y : ↥((↑S : Set (Vertex n))ᶜ)}
          (q : (G.induce (↑S : Set (Vertex n))ᶜ).Walk x y) : x = y := by
        cases q with
        | nil => rfl
        | @cons x z _ e _ =>
          exact False.elim ((show x.val.1 ≠ z.val.1 from e) ((allWhite x).trans (allWhite z).symm))
      exact (congrArg Subtype.val (trivial p)).symm
  let sizes := {k | ∃ A : Finset (Vertex n), k = A.card ∧ PSDSet G A}
  have hit : n ∈ sizes := ⟨S,(card_part true).symm,full⟩
  obtain ⟨A,cost,k,all⟩ := Nat.sInf_mem (show sizes.Nonempty from ⟨n,hit⟩)
  apply Nat.le_antisymm (Nat.sInf_le (s := sizes) hit)
  change psd (biclique n) = A.card at cost
  change n ≤ psd (biclique n)
  rw [cost]
  apply Nat.le_of_not_gt
  intro small
  have stays (t : ℕ) : round G A t = (↑A : Set (Vertex n)) := by
    induction t with
    | zero => rfl
    | succ t ih => exact (congrArg (AutoGraphForge373.step G) ih).trans (no_growth A small)
  obtain ⟨v,_,absent⟩ := missing A small false
  have h := all v
  rw [stays k] at h
  exact absent h

private def paint (v : Vertex n) : Fin 4 :=
  if h : v.2.val < 3 then ⟨v.2.val+1, by omega⟩ else 0

private theorem paint_rainbow (hn : 3 ≤ n) : Rainbow (biclique n) (paint (n := n)) := by
  intro v _ c nz
  have pos : 0 < c.val := Nat.pos_of_ne_zero (fun h => nz (Fin.ext h))
  let j : Fin n := ⟨c.val - 1, by omega⟩
  refine ⟨(!v.1,j),show v.1 ≠ !v.1 from by cases v.1 <;> decide,?_⟩
  apply Fin.ext
  simp [paint,j,show c.val - 1 < 3 by omega]
  omega

private theorem paint_cost : weight (paint (n := n)) ≤ 6 := by
  let T := univ.filter (fun v : Vertex n => paint v ≠ 0)
  have small (v : T) : v.val.2.val < 3 := by
    have nonzero := (mem_filter.mp v.property).2
    by_contra h
    exact nonzero (by simp [paint,h])
  let index (v : T) : Bool × Fin 3 := (v.val.1,⟨v.val.2.val,small v⟩)
  have inj : Function.Injective index := by
    intro a b e
    exact Subtype.ext (Prod.ext (congrArg (Prod.fst : Bool × Fin 3 → Bool) e) (Fin.ext (congrArg (fun p : Bool × Fin 3 => p.2.val) e)))
  have bound := Fintype.card_le_of_injective index inj
  change T.card ≤ 6
  simpa only [Fintype.card_coe,Fintype.card_prod,Fintype.card_bool,Fintype.card_fin] using bound

/-- With fewer than six colored vertices each part has an uncolored vertex,
so each opposite part must contain all three singleton colors. -/
private theorem rainbow_lower (hn : 6 ≤ n) {f : Vertex n → Fin 4} (hf : Rainbow (biclique n) f) :
    6 ≤ weight f := by
  let T := univ.filter (fun v => f v ≠ 0)
  change 6 ≤ T.card
  by_contra! low
  have witnesses (b : Bool) (c : Fin 3) : ∃ v : T, v.val.1 = b ∧ f v = c.succ := by
    obtain ⟨u,hu,un⟩ := missing T (by omega) (!b)
    have zero : f u = 0 := by
      by_contra h
      exact un (mem_filter.mpr ⟨mem_univ _,h⟩)
    obtain ⟨v,e,h⟩ := hf u zero c.succ (Fin.succ_ne_zero c)
    have side := opp (show v.1 ≠ u.1 from e.symm)
    rw [mem_part.mp hu,Bool.not_not] at side
    exact ⟨⟨v,mem_filter.mpr ⟨mem_univ _,h ▸ Fin.succ_ne_zero c⟩⟩,side,h⟩
  choose pick side color using witnesses
  let pickPair (p : Bool × Fin 3) := pick p.1 p.2
  have inj : Function.Injective pickPair := by
    rintro ⟨a,i⟩ ⟨b,j⟩ e
    change pick a i = pick b j at e
    apply Prod.ext
    · exact (side a i).symm.trans ((congrArg (fun v : T => v.val.1) e).trans (side b j))
    · exact Fin.succ_inj.mp ((color a i).symm.trans ((congrArg (fun v : T => f v) e).trans (color b j)))
  have bound := Fintype.card_le_of_injective pickPair inj
  simp only [Fintype.card_prod,Fintype.card_bool,Fintype.card_fin,Fintype.card_coe] at bound
  omega

theorem rainbow_biclique (hn : 6 ≤ n) : rainbowNumber (biclique n) = 6 := by
  let sizes := {k | ∃ f : Vertex n → Fin 4, weight f = k ∧ Rainbow (biclique n) f}
  have hit : weight (paint (n := n)) ∈ sizes := ⟨paint,rfl,paint_rainbow (by omega)⟩
  obtain ⟨f,cost,valid⟩ := Nat.sInf_mem (show sizes.Nonempty from ⟨_,hit⟩)
  change weight f = rainbowNumber (biclique n) at cost
  exact Nat.le_antisymm ((Nat.sInf_le (s := sizes) hit).trans paint_cost)
    ((rainbow_lower hn valid).trans cost.le)

/-- An infinite counterexample family for the release row. -/
theorem counterexample_family (hn : 7 ≤ n) :
    psd (biclique n) = n ∧ rainbowNumber (biclique n) = 6 ∧
      ¬ psd (biclique n) ≤ rainbowNumber (biclique n) := by
  have z := psd_biclique (show 0 < n by omega)
  have r := rainbow_biclique (show 6 ≤ n by omega)
  exact ⟨z,r,by omega⟩

theorem line1080_false : ¬ (∀ (U : Type) [Fintype U] (G : SimpleGraph U),
    2 ≤ Fintype.card U → Nonempty (G →g (⊤ : SimpleGraph (Fin 2))) → Cograph G →
    psd G ≤ rainbowNumber G) := by
  intro claim
  obtain ⟨cg,bip⟩ := biclique_class 7
  exact (counterexample_family (n := 7) (by decide)).2.2
    (claim (Vertex 7) (biclique 7) (by decide) bip cg)

#print axioms psd_biclique
#print axioms rainbow_biclique
#print axioms counterexample_family
#print axioms line1080_false
end
end AutoGraphForge1080
