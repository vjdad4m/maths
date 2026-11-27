import BicycleFigureModel133
import LocalDensity133

namespace Graffiti133Bicycle
open SimpleGraph Graffiti133 Graffiti133Revisit
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
variable {V : Type*} {G : SimpleGraph V} {n m : Nat}

def figurePathLabel (n i : Nat) : Nat :=
  if i < n-1 then n-1-i else if i=n-1 then 0 else i+1

private theorem figure_path_label_inj (n : Nat) {i j : Nat}
    (eq : figurePathLabel n i=figurePathLabel n j) : i=j := by
  unfold figurePathLabel at eq
  split_ifs at eq <;> omega

private theorem figure_path_label_adj (n m : Nat) (hn : 2≤n) (hm : 2≤m)
    {i j : Nat} (lt : i < j) (jb : j < n+m-1) :
    figureRel n m (figurePathLabel n i) (figurePathLabel n j) ↔ i+1=j := by

  have il (v : Nat) (hl : v < n-1) : figurePathLabel n v=n-1-v := if_pos hl
  have ie (v : Nat) (he : v=n-1) : figurePathLabel n v=0 := by
    unfold figurePathLabel
    rw [if_neg (by omega),if_pos he]
  have ig (v : Nat) (hg : n-1 < v) : figurePathLabel n v=v+1 := by
    unfold figurePathLabel
    rw [if_neg (by omega),if_neg (by omega)]
  rcases lt_trichotomy i (n-1) with u|u|u
  · rw [il i u]
    rcases lt_trichotomy j (n-1) with v|v|v
    · rw [il j v]
      unfold figureRel
      rw [if_neg (by omega),if_neg (by omega),if_pos (by omega)]
      omega
    · rw [ie j v]
      unfold figureRel
      rw [if_neg (by omega),if_pos rfl]
      omega
    · rw [ig j v]
      unfold figureRel
      rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
      constructor
      · exact False.elim
      · intro eq
        omega
  · rw [ie i u,ig j (by omega)]
    unfold figureRel
    rw [if_pos rfl]
    omega
  · rw [ig i u,ig j (by omega)]
    unfold figureRel
    rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_pos (by omega)]
    omega

theorem FigureModel.long_path (M : FigureModel G n m) (hn : 2≤n) (hm : 2≤m) :
    ∃ f : Fin (n+m-1) → V, InducedPath G f := by
  let labels (i : Fin (n+m-1)) : Fin (n+m+1) := ⟨figurePathLabel n i.val,by
    unfold figurePathLabel
    split_ifs <;> omega⟩
  refine ⟨M.f ∘ labels,fun i j e => Fin.ext (figure_path_label_inj n (congrArg Fin.val (M.inj e))),?_⟩
  intro i j lt
  exact (M.adj (labels i) (labels j)).trans (figure_path_label_adj n m hn hm lt j.isLt)

theorem FigureModel.left_order_ge_four (M : FigureModel G n m) (hn : 2≤n) (hm : 2≤m)
    (noTri : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (h4 : FourCycleFree G) : 4≤n := by
  rcases (show n=2 ∨ n=3 ∨ 4≤n by omega) with rfl|rfl|done
  · let u : Fin (2+m+1) := ⟨0,by omega⟩
    let v : Fin (2+m+1) := ⟨1,by omega⟩
    let w : Fin (2+m+1) := ⟨2,by omega⟩
    have a : G.Adj (M.f u) (M.f v) := (M.adj _ _).mpr (by simp [figureRel,u,v])
    have b : G.Adj (M.f v) (M.f w) := (M.adj _ _).mpr (by simp [figureRel,v,w])
    have c : G.Adj (M.f w) (M.f u) := (M.adj _ _).mpr (by simp [figureRel,w,u])
    exact (noTri _ _ _ a b c).elim
  · let u : Fin (3+m+1) := ⟨0,by omega⟩
    let v : Fin (3+m+1) := ⟨1,by omega⟩
    let w : Fin (3+m+1) := ⟨2,by omega⟩
    let z : Fin (3+m+1) := ⟨3,by omega⟩
    have a : G.Adj (M.f u) (M.f v) := (M.adj _ _).mpr (by simp [figureRel,u,v])
    have b : G.Adj (M.f w) (M.f v) := (M.adj _ _).mpr (by simp [figureRel,v,w])
    have c : G.Adj (M.f u) (M.f z) := (M.adj _ _).mpr (by simp [figureRel,z,u])
    have d : G.Adj (M.f w) (M.f z) := (M.adj _ _).mpr (by simp [figureRel,w,z])
    have uw : M.f u≠M.f w := fun e => by
      have q := congrArg Fin.val (M.inj e)
      change 0=2 at q
      omega
    have eq := congrArg Fin.val (M.inj (h4 _ _ _ _ uw a b c d))
    change 1=3 at eq
    omega
  · exact done

def TwoHubPaths.swap {h : V} (P : TwoHubPaths G h) : TwoHubPaths G h :=
  ⟨P.T,P.S,P.offT,P.offS,P.sep.symm,
    fun y hy x hx e => P.noCross x hx y hy e.symm,P.two,P.one⟩

theorem TwoHubPaths.small_figure_keys {h : V} (P : TwoHubPaths G h)
    (noTri : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (h4 : FourCycleFree G) (h9 : ¬∃ p : Fin 9 → V, InducedPath G p) :
    (P.one.n=4 ∧ P.two.n=4) ∨ (P.one.n=4 ∧ P.two.n=5) ∨ (P.one.n=5 ∧ P.two.n=4) := by
  have hn := P.figureModel.left_order_ge_four P.one.nontriv P.two.nontriv noTri h4
  have hm := P.swap.figureModel.left_order_ge_four P.two.nontriv P.one.nontriv noTri h4
  change 4≤P.two.n at hm
  have upper : P.one.n+P.two.n≤9 := by
    by_cases hb : P.one.n+P.two.n ≤ 9
    · exact hb
    exfalso
    obtain ⟨f,hf⟩ := P.figureModel.long_path P.one.nontriv P.two.nontriv
    exact h9 (trim_path (by omega) hf)
  omega

#print axioms TwoHubPaths.small_figure_keys
end Graffiti133Bicycle
