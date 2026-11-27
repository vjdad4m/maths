import NoFiveHoles133
import Mathlib.Combinatorics.SimpleGraph.Maps

/-! Finite connected domination, following Camby–Schaudt (arXiv:1402.7213). -/
namespace Graffiti133Camby
open SimpleGraph Graffiti133 Graffiti133RevisitSix Finset
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

def CD (G : SimpleGraph V) (S : Finset V) : Prop :=
  (G.induce (S : Set V)).Connected ∧ ∀ x, x ∈ S ∨ ∃ y ∈ S, G.Adj x y

def MinimalSize (G : SimpleGraph V) (S : Finset V) : Prop :=
  CD G S ∧ ∀ T, CD G T → S.card ≤ T.card

theorem exists_minimalSize (hc : G.Connected) : ∃ S : Finset V, MinimalSize G S := by
  classical
  have hU : CD G (Finset.univ : Finset V) := by
    refine ⟨?_,by intro x; exact Or.inl (Finset.mem_univ _)⟩
    rw [connected_iff_exists_forall_reachable]
    obtain ⟨x⟩ := hc.nonempty
    refine ⟨⟨x,Finset.mem_univ _⟩,?_⟩
    let F : G →g G.induce ((Finset.univ : Finset V) : Set V) :=
      ⟨fun x => ⟨x,Finset.mem_univ _⟩,fun h => h⟩
    intro v
    obtain ⟨w⟩ := hc x v.val
    exact ⟨w.map F⟩
  let Q := Finset.univ.filter (CD G)
  have mem : ∀ T : Finset V, T∈Q ↔ CD G T := by intro T; simp [Q]
  obtain ⟨S,hS,lower⟩ := Finset.exists_min_image Q Finset.card ⟨_,(mem _).mpr hU⟩
  exact ⟨S,(mem _).mp hS,fun T h => lower T ((mem _).mpr h)⟩

def Inside (S : Finset V) {n : ℕ} (f : Fin n → V) : Prop := ∀ i, f i ∈ S
def NoPath (G : SimpleGraph V) (n : ℕ) : Prop := ¬∃ f : Fin n → V, InducedPath G f
def NoPathIn (G : SimpleGraph V) (S : Finset V) (n : ℕ) : Prop :=
  ¬∃ f : Fin n → V, InducedPath G f ∧ Inside S f
def PrivateAt (G : SimpleGraph V) (S : Finset V) (x y : V) : Prop :=
  y ∉ S ∧ G.Adj y x ∧ ∀ z ∈ S, z≠x → ¬G.Adj y z

theorem private_of_noncut {S : Finset V} (hS : MinimalSize G S)
    {x y : V} (hx : x∈S) (hy : y∈S.erase x) (e : G.Adj x y)
    (conn : (G.induce (↑(S.erase x) : Set V)).Connected) : ∃ z, PrivateAt G S x z := by
  classical
  have small := Finset.card_erase_add_one hx
  have fail : ¬(∀ z, z∈S.erase x ∨ ∃ w ∈ S.erase x, G.Adj z w) := by
    intro h
    have hh := hS.2 (S.erase x) ⟨conn,h⟩
    omega
  push_neg at fail
  obtain ⟨z,hz,hn⟩ := fail
  have zne : z ≠ x := fun eq => hn y hy (eq.symm ▸ e)
  have off : z∉S := fun h => hz (Finset.mem_erase.mpr ⟨zne,h⟩)
  obtain hit | ⟨w,hw,edge⟩ := hS.1.2 z
  · exact (off hit).elim
  · have ex : w=x := by
      by_contra no
      exact hn w (Finset.mem_erase.mpr ⟨no,hw⟩) edge
    exact ⟨z,off,ex ▸ edge,fun w hw hne => hn w (Finset.mem_erase.mpr ⟨hne,hw⟩)⟩

theorem cut_tip_witness {n : ℕ} (hn : 2 ≤ n) {f : Fin n → V}
    (hf : InducedPath G f) {S : Finset V} (hin : Inside S f)
    (conn : (G.induce (S : Set V)).Connected)
    (hcut : ¬(G.induce (↑(S.erase (f ⟨0,by omega⟩)) : Set V)).Connected) :
    ∃ y∈S, (∀ i, y≠f i) ∧ G.Adj y (f ⟨0,by omega⟩) ∧
      ∀ i : Fin n, 0 < i.val → ¬G.Adj y (f i) := by
  classical
  let i₀ : Fin n := ⟨0,by omega⟩
  let i₁ : Fin n := ⟨1,by omega⟩
  let a := f i₀
  let U := S.erase a
  let J := G.induce (U : Set V)
  have inU (i : Fin n) (hi : 0 < i.val) : f i∈U := by
    apply Finset.mem_erase.mpr
    refine ⟨fun e => ?_,hin i⟩
    have q := congrArg Fin.val (hf.1 e)
    change i.val=0 at q
    omega
  let p : (U : Set V) := ⟨f i₁,inU _ (by change 0 < 1; decide)⟩
  let R (x : V) : Prop := ∃ h : x∈U, J.Reachable p ⟨x,h⟩
  have move {x y : V} (hx : R x) (hy : y∈U) (e : G.Adj x y) : R y := by
    obtain ⟨hh,⟨w⟩⟩ := hx
    exact ⟨hy,⟨w.append (Walk.cons (show J.Adj ⟨x,hh⟩ ⟨y,hy⟩ from e) Walk.nil)⟩⟩
  have fR (j : ℕ) : ∀ (hj : j+1 < n), R (f ⟨j+1,hj⟩) := by
    induction j with
    | zero => intro hj; exact ⟨inU _ (by change 0 < 1; decide),⟨Walk.nil⟩⟩
    | succ j ih =>
      intro hj
      have pj : j+1 < n := by omega
      apply move (ih pj) (inU ⟨j+1+1,hj⟩ (by change 0 < j+1+1; omega))
      exact (hf.2 ⟨j+1,pj⟩ ⟨j+1+1,hj⟩ (by change j+1 < j+1+1; omega)).mpr rfl
  have pathR (i : Fin n) (hi : 0 < i.val) : R (f i) := by
    have h := fR (i.val-1) (by have := i.isLt; omega)
    have eq : (⟨i.val-1+1,by have := i.isLt; omega⟩ : Fin n)=i :=
      Fin.ext (by change i.val-1+1=i.val; omega)
    exact eq ▸ h
  apply Classical.byContradiction
  intro no
  have adj_a (y : V) (hy : y∈S) (e : G.Adj y a) : R y := by
    apply Classical.byContradiction
    intro nr
    have iny : y∈U := Finset.mem_erase.mpr ⟨e.ne,hy⟩
    have off (i : Fin n) : y≠f i := by
      intro eq
      by_cases he : i.val=0
      · exact e.ne (eq.trans (congrArg f (Fin.ext he)))
      · exact nr (eq.symm ▸ pathR i (by omega))
    exact no ⟨y,hy,off,e,fun i hi hit => nr (move (pathR i hi) iny hit.symm)⟩
  have step {x y : (S : Set V)} (e : (G.induce (S : Set V)).Adj x y)
      (rx : x.val=a ∨ R x.val) : y.val=a ∨ R y.val := by
    have edge : G.Adj x.val y.val := e
    by_cases h : y.val=a
    · exact Or.inl h
    have hy : y.val∈U := Finset.mem_erase.mpr ⟨h,y.property⟩
    rcases rx with eq | hh
    · exact Or.inr (adj_a y.val y.property (eq ▸ edge.symm))
    · exact Or.inr (move hh hy edge)
  have walk {x y : (S : Set V)} (w : (G.induce (S : Set V)).Walk x y)
      (hh : x.val=a ∨ R x.val) : y.val=a ∨ R y.val := by
    induction w with
    | nil => exact hh
    | cons e w ih => exact ih (step e hh)
  apply hcut
  rw [connected_iff_exists_forall_reachable]
  refine ⟨p,?_⟩
  intro q
  let x : (S : Set V) := ⟨a,hin i₀⟩
  let y : (S : Set V) := ⟨q.val,Finset.erase_subset _ _ q.property⟩
  obtain ⟨w⟩ := conn x y
  have hh := walk w (Or.inl rfl)
  change q.val=a ∨ R q.val at hh
  rcases hh with eq | ⟨h,reach⟩
  · exact ((Finset.mem_erase.mp q.property).1 eq).elim
  · exact reach

#print axioms cut_tip_witness
end Graffiti133Camby
