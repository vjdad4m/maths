import CubicCutShore

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

def RootOrdering {n : ℕ} (G : SimpleGraph V) (f : Fin n ↪ V) : Prop :=
  ∀ i, i.val ≠ 0 →
    ∃ j, G.Adj (f i) (f j) ∧ j < i ∧
      ∀ k, G.Adj (f i) (f k) → k < i → k = j

/-- A two-vertex induced path hanging from the root can be added to any
four-vertex rooted tree anticomplete to its two new vertices. -/
theorem six_le_treeNumber_of_rooted_four_and_tail [Fintype V]
    (f : Fin 4 ↪ V) (rooted : RootOrdering G f) {a t : V}
    (atEdge : G.Adj a t) (ra : G.Adj (f 0) a)
    (offA : ∀ i, a ≠ f i) (offT : ∀ i, t ≠ f i)
    (tOff : ∀ i, ¬ G.Adj (f i) t)
    (aOff : ∀ i, i ≠ 0 → ¬ G.Adj (f i) a) :
    6 ≤ treeNumber G := by
  let g : Fin 6 → V := @Fin.addCases 4 2 (fun _ => V) f (![a,t] : Fin 2 → V)
  have left (i : Fin 4) : g (Fin.castAdd 2 i) = f i := by simp [g,Fin.addCases_left]
  have right (i : Fin 2) : g (Fin.natAdd 4 i) = (![a,t] : Fin 2 → V) i := by
    simp [g,Fin.addCases_right]
  have inj : Function.Injective g := by
    intro i
    refine Fin.addCases (m := 4) (n := 2) ?_ ?_ i
    · intro x j
      refine Fin.addCases (m := 4) (n := 2) ?_ ?_ j
      · intro y eq
        rw [left,left] at eq
        exact congrArg (Fin.castAdd 2) (f.injective eq)
      · intro y eq
        rw [left,right] at eq
        fin_cases y
        · exact (offA x eq.symm).elim
        · exact (offT x eq.symm).elim
    · intro x j
      refine Fin.addCases (m := 4) (n := 2) ?_ ?_ j
      · intro y eq
        rw [right,left] at eq
        fin_cases x
        · exact (offA y eq).elim
        · exact (offT y eq).elim
      · intro y eq
        rw [right,right] at eq
        fin_cases x <;> fin_cases y <;> simp_all [atEdge.ne,atEdge.ne.symm]
  apply six_le_treeNumber_of_ordering ⟨g,inj⟩
  intro i hi
  revert hi
  refine Fin.addCases (m := 4) (n := 2) ?_ ?_ i
  · intro x hx
    have xn : x.val ≠ 0 := fun h => hx (Fin.ext h)
    obtain ⟨y,xy,ylt,only⟩ := rooted x xn
    refine ⟨Fin.castAdd 2 y,?_,ylt,?_⟩
    · change G.Adj (g (Fin.castAdd 2 x)) (g (Fin.castAdd 2 y))
      simpa only [left] using xy
    · intro k
      refine Fin.addCases (m := 4) (n := 2) ?_ ?_ k
      · intro z edge lt
        change G.Adj (g (Fin.castAdd 2 x)) (g (Fin.castAdd 2 z)) at edge
        rw [left,left] at edge
        exact congrArg (Fin.castAdd 2) (only z edge lt)
      · intro z _ lt
        have za := x.isLt
        change 4 + z.val < x.val at lt
        omega
  · intro x _
    fin_cases x
    · refine ⟨0,?_,by decide,?_⟩
      · change G.Adj (g (Fin.natAdd 4 (0 : Fin 2))) (g (Fin.castAdd 2 (0 : Fin 4)))
        rw [left,right]
        exact ra.symm
      · intro k
        refine Fin.addCases (m := 4) (n := 2) ?_ ?_ k
        · intro z edge _
          by_cases ze : z = 0
          · exact congrArg (Fin.castAdd 2) ze
          · change G.Adj (g (Fin.natAdd 4 (0 : Fin 2))) (g (Fin.castAdd 2 z)) at edge
            rw [right,left] at edge
            exact (aOff z ze edge.symm).elim
        · intro z _ lt
          change 4 + z.val < 4 at lt
          omega
    · refine ⟨Fin.natAdd 4 (0 : Fin 2),?_,by decide,?_⟩
      · change G.Adj (g (Fin.natAdd 4 (1 : Fin 2))) (g (Fin.natAdd 4 (0 : Fin 2)))
        rw [right,right]
        exact atEdge.symm
      · intro k
        refine Fin.addCases (m := 4) (n := 2) ?_ ?_ k
        · intro z edge _
          change G.Adj (g (Fin.natAdd 4 (1 : Fin 2))) (g (Fin.castAdd 2 z)) at edge
          rw [right,left] at edge
          exact (tOff z edge.symm).elim
        · intro z _ lt
          have zz : z = 0 := by
            apply Fin.ext
            change 4 + z.val < 5 at lt
            omega
          exact congrArg (Fin.natAdd 4) zz

/-- A four-vertex tree in its given order with a distinguished root. The
last two vertices are specified by their only neighbor earlier in the list. -/
theorem four_ordering {r x y z : V} (nd : [r,x,y,z].Nodup)
    (rx : G.Adj r x)
    (hy : (G.Adj y r ∧ ¬ G.Adj y x) ∨ (G.Adj y x ∧ ¬ G.Adj y r))
    (hz : (G.Adj z r ∧ ¬ G.Adj z x ∧ ¬ G.Adj z y) ∨
      (G.Adj z x ∧ ¬ G.Adj z r ∧ ¬ G.Adj z y) ∨
      (G.Adj z y ∧ ¬ G.Adj z r ∧ ¬ G.Adj z x)) :
    ∃ f : Fin 4 ↪ V, f 0 = r ∧ f 1 = x ∧ f 2 = y ∧ f 3 = z ∧ RootOrdering G f := by
  let f : Fin 4 ↪ V := ⟨fun i => [r,x,y,z].get i,List.nodup_iff_injective_get.mp nd⟩
  refine ⟨f,rfl,rfl,rfl,rfl,?_⟩
  intro i hi
  fin_cases i
  · exact (hi rfl).elim
  · refine ⟨0,rx.symm,by decide,?_⟩
    intro k _ lt
    exact Fin.ext (by have h : k.val < 1 := lt; omega)
  · rcases hy with ⟨yr,yx⟩|⟨yx,yr⟩
    · refine ⟨0,yr,by decide,?_⟩
      intro k e lt
      fin_cases k
      · rfl
      · exact (yx e).elim
      · exfalso; exact (by decide : ¬ (_ < _)) lt
      · exfalso; exact (by decide : ¬ (_ < _)) lt
    · refine ⟨1,yx,by decide,?_⟩
      intro k e lt
      fin_cases k
      · exact (yr e).elim
      · rfl
      · exfalso; exact (by decide : ¬ (_ < _)) lt
      · exfalso; exact (by decide : ¬ (_ < _)) lt
  · rcases hz with ⟨zr,zx,zy⟩|⟨zx,zr,zy⟩|⟨zy,zr,zx⟩
    · refine ⟨0,zr,by decide,?_⟩
      intro k e lt
      fin_cases k
      · rfl
      · exact (zx e).elim
      · exact (zy e).elim
      · exfalso; exact (by decide : ¬ (_ < _)) lt
    · refine ⟨1,zx,by decide,?_⟩
      intro k e lt
      fin_cases k
      · exact (zr e).elim
      · rfl
      · exact (zy e).elim
      · exfalso; exact (by decide : ¬ (_ < _)) lt
    · refine ⟨2,zy,by decide,?_⟩
      intro k e lt
      fin_cases k
      · exact (zr e).elim
      · exact (zx e).elim
      · rfl
      · exfalso; exact (by decide : ¬ (_ < _)) lt

#print axioms six_le_treeNumber_of_rooted_four_and_tail
#print axioms four_ordering

end Graffiti199Depleted.Catalogue
