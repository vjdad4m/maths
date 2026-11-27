import RootQuartet

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [DecidableEq V]

/-- The mixed cut at a cubic port after orienting the clique shore. -/
structure CubicMixedCut (G : SimpleGraph V) where
  r : V
  p : V
  q : V
  rp : r ≠ p
  rq : r ≠ q
  pq : p ≠ q
  A : Set V
  B : Set V
  apart : Disjoint A B
  offA : ∀ v ∈ ({r,p,q} : Finset V), v ∉ A
  offB : ∀ v ∈ ({r,p,q} : Finset V), v ∉ B
  boundA : ShoreBoundary G {r,p,q} A
  boundB : ShoreBoundary G {r,p,q} B
  cover : ∀ v, v ∈ A ∨ v ∈ B ∨ v ∈ ({r,p,q} : Finset V)
  cliqueA : A.Pairwise G.Adj
  connB : (G.induce B).Connected
  noncliqueB : ¬ B.Pairwise G.Adj
  a : V
  tail : V
  b : V
  c : V
  aA : a ∈ A
  tailA : tail ∈ A
  aTail : a ≠ tail
  bB : b ∈ B
  cB : c ∈ B
  bc : b ≠ c
  neighbors : ∀ x, G.Adj r x ↔ x = a ∨ x = b ∨ x = c

namespace CubicMixedCut

variable (F : CubicMixedCut G)

theorem r_not_A : F.r ∉ F.A := F.offA _ (by simp)
theorem r_not_B : F.r ∉ F.B := F.offB _ (by simp)

theorem apart_ne {x y : V} (xA : x ∈ F.A) (yB : y ∈ F.B) : x ≠ y :=
  fun h => Set.disjoint_left.mp F.apart xA (h.symm ▸ yB)

theorem anti {x y : V} (xA : x ∈ F.A) (yB : y ∈ F.B) : ¬ G.Adj x y := by
  intro edge
  have yD := F.boundA x xA y (fun h => Set.disjoint_left.mp F.apart h yB) edge
  exact F.offB y yD yB

theorem ra : G.Adj F.r F.a := (F.neighbors _).mpr (Or.inl rfl)
theorem rb : G.Adj F.r F.b := (F.neighbors _).mpr (Or.inr (Or.inl rfl))
theorem rc : G.Adj F.r F.c := (F.neighbors _).mpr (Or.inr (Or.inr rfl))

theorem rTail : ¬ G.Adj F.r F.tail := by
  intro edge
  rcases (F.neighbors _).mp edge with h|h|h
  · exact F.aTail h.symm
  · exact F.apart_ne F.tailA F.bB h
  · exact F.apart_ne F.tailA F.cB h

/-- Vertices on the nonclique side other than the two neighbors of the cubic port. -/
def inner : Set V := {x | x ∈ F.B ∧ x ≠ F.b ∧ x ≠ F.c}

theorem off_r_of_inner {x : V} (hx : x ∈ F.inner) : ¬ G.Adj F.r x := by
  intro edge
  rcases (F.neighbors _).mp edge with h|h|h
  · exact F.apart_ne F.aA hx.1 h.symm
  · exact hx.2.1 h
  · exact hx.2.2 h

theorem split_B {x : V} (hx : x ∈ F.B) : x = F.b ∨ x = F.c ∨ x ∈ F.inner := by
  classical
  by_cases hb : x = F.b
  · exact Or.inl hb
  · by_cases hc : x = F.c
    · exact Or.inr (Or.inl hc)
    · exact Or.inr (Or.inr ⟨hx,hb,hc⟩)

variable [Fintype V]

/-- The tail in the clique forbids every rooted four-vertex induced
tree on the other side. -/
theorem quad_forbidden (budget : treeNumber G ≤ 5) {x y z : V}
    (xB : x ∈ F.B) (yB : y ∈ F.B) (zB : z ∈ F.B)
    (xy : x ≠ y) (xz : x ≠ z) (yz : y ≠ z)
    (rx : G.Adj F.r x)
    (hy : (G.Adj y F.r ∧ ¬ G.Adj y x) ∨ (G.Adj y x ∧ ¬ G.Adj y F.r))
    (hz : (G.Adj z F.r ∧ ¬ G.Adj z x ∧ ¬ G.Adj z y) ∨
      (G.Adj z x ∧ ¬ G.Adj z F.r ∧ ¬ G.Adj z y) ∨
      (G.Adj z y ∧ ¬ G.Adj z F.r ∧ ¬ G.Adj z x)) : False := by
  have nox : F.r ≠ x := fun e => F.r_not_B (e.symm ▸ xB)
  have noy : F.r ≠ y := fun e => F.r_not_B (e.symm ▸ yB)
  have noz : F.r ≠ z := fun e => F.r_not_B (e.symm ▸ zB)
  have nd : [F.r,x,y,z].Nodup := by simp [nox,noy,noz,xy,xz,yz]
  obtain ⟨f,h0,h1,h2,h3,cert⟩ := four_ordering nd rx hy hz
  have cases4 (i : Fin 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by fin_cases i <;> decide
  have offA (i : Fin 4) : F.a ≠ f i := by
    rcases cases4 i with rfl|rfl|rfl|rfl
    · rw [h0]
      exact fun e => F.r_not_A (e ▸ F.aA)
    · rw [h1]
      exact F.apart_ne F.aA xB
    · rw [h2]
      exact F.apart_ne F.aA yB
    · rw [h3]
      exact F.apart_ne F.aA zB
  have offT (i : Fin 4) : F.tail ≠ f i := by
    rcases cases4 i with rfl|rfl|rfl|rfl
    · rw [h0]
      exact fun e => F.r_not_A (e ▸ F.tailA)
    · rw [h1]
      exact F.apart_ne F.tailA xB
    · rw [h2]
      exact F.apart_ne F.tailA yB
    · rw [h3]
      exact F.apart_ne F.tailA zB
  have tOff (i : Fin 4) : ¬ G.Adj (f i) F.tail := by
    rcases cases4 i with rfl|rfl|rfl|rfl
    · rw [h0]
      exact F.rTail
    · rw [h1]
      exact fun e => F.anti F.tailA xB e.symm
    · rw [h2]
      exact fun e => F.anti F.tailA yB e.symm
    · rw [h3]
      exact fun e => F.anti F.tailA zB e.symm
  have aOff (i : Fin 4) (i0 : i ≠ 0) : ¬ G.Adj (f i) F.a := by
    rcases cases4 i with rfl|rfl|rfl|rfl
    · exact (i0 rfl).elim
    · rw [h1]
      exact fun e => F.anti F.aA xB e.symm
    · rw [h2]
      exact fun e => F.anti F.aA yB e.symm
    · rw [h3]
      exact fun e => F.anti F.aA zB e.symm
  have six := six_le_treeNumber_of_rooted_four_and_tail f cert
    (F.cliqueA F.aA F.tailA F.aTail) (h0.symm ▸ F.ra) offA offT tOff aOff
  omega

/-- The two neighbors in the nonclique shore dominate that shore. -/
theorem dominates_inner (budget : treeNumber G ≤ 5) {x : V} (hx : x ∈ F.inner) :
    G.Adj F.b x ∨ G.Adj F.c x := by
  classical
  by_contra failure
  let U : Set F.B :=
    {z | z.val = F.b ∨ z.val = F.c ∨ G.Adj F.b z.val ∨ G.Adj F.c z.val}
  have xOff : (⟨x,hx.1⟩ : F.B) ∉ U := by
    rintro (eq|eq|e|e)
    · exact hx.2.1 eq
    · exact hx.2.2 eq
    · exact failure (Or.inl e)
    · exact failure (Or.inr e)
  obtain ⟨w⟩ := F.connB.preconnected ⟨F.b,F.bB⟩ ⟨x,hx.1⟩
  obtain ⟨u,uU,v,vU,uv⟩ := crossingOnWalk (U := U) w (Or.inl rfl) xOff
  have pu : u.val ≠ F.b := fun e => vU (Or.inr (Or.inr (Or.inl (e ▸ (show G.Adj u.val v.val from uv)))))
  have qu : u.val ≠ F.c := fun e => vU (Or.inr (Or.inr (Or.inr (e ▸ (show G.Adj u.val v.val from uv)))))
  have noB : ¬ G.Adj F.b v.val := fun e => vU (Or.inr (Or.inr (Or.inl e)))
  have noC : ¬ G.Adj F.c v.val := fun e => vU (Or.inr (Or.inr (Or.inr e)))
  have offV : v.val ∈ F.inner :=
    ⟨v.property,fun e => vU (Or.inl e),fun e => vU (Or.inr (Or.inl e))⟩
  have noRU := F.off_r_of_inner ⟨u.property,pu,qu⟩
  have noRV := F.off_r_of_inner offV
  rcases uU with e|e|bu|cu
  · exact pu e
  · exact qu e
  · exact F.quad_forbidden budget F.bB u.property v.property (Ne.symm pu)
      (Ne.symm offV.2.1) (show G.Adj u.val v.val from uv).ne F.rb
      (Or.inr ⟨bu.symm,fun e => noRU e.symm⟩)
      (Or.inr (Or.inr ⟨(show G.Adj u.val v.val from uv).symm,fun e => noRV e.symm,fun e => noB e.symm⟩))
  · exact F.quad_forbidden budget F.cB u.property v.property (Ne.symm qu)
      (Ne.symm offV.2.2) (show G.Adj u.val v.val from uv).ne F.rc
      (Or.inr ⟨cu.symm,fun e => noRU e.symm⟩)
      (Or.inr (Or.inr ⟨(show G.Adj u.val v.val from uv).symm,fun e => noRV e.symm,fun e => noC e.symm⟩))

/-- On either side of the two-neighbor cover, the interior neighborhood is a clique. -/
theorem inner_adjacent_of_common_contact (budget : treeNumber G ≤ 5) {s x y : V}
    (sr : G.Adj F.r s) (sB : s ∈ F.B) (xI : x ∈ F.inner) (yI : y ∈ F.inner) (xy : x ≠ y)
    (sx : G.Adj s x) (sy : G.Adj s y) : G.Adj x y := by
  apply Classical.byContradiction
  intro off
  exact F.quad_forbidden budget sB xI.1 yI.1 sx.ne sy.ne xy sr
    (Or.inr ⟨sx.symm,fun e => F.off_r_of_inner xI e.symm⟩)
    (Or.inr (Or.inl ⟨sy.symm,fun e => F.off_r_of_inner yI e.symm,fun e => off e.symm⟩))

theorem both_contacts_of_nonadjacent (budget : treeNumber G ≤ 5)
    (bcOff : ¬ G.Adj F.b F.c) {x : V} (hx : x ∈ F.inner) :
    G.Adj F.b x ∧ G.Adj F.c x := by
  classical
  rcases F.dominates_inner budget hx with bx|cx
  · refine ⟨bx,?_⟩
    by_contra cx
    exact F.quad_forbidden budget F.bB F.cB hx.1 F.bc (Ne.symm hx.2.1) (Ne.symm hx.2.2) F.rb
      (Or.inl ⟨F.rc.symm,fun e => bcOff e.symm⟩)
      (Or.inr (Or.inl ⟨bx.symm,fun e => F.off_r_of_inner hx e.symm,fun e => cx e.symm⟩))
  · refine ⟨?_,cx⟩
    by_contra bx
    exact F.quad_forbidden budget F.bB F.cB hx.1 F.bc (Ne.symm hx.2.1) (Ne.symm hx.2.2) F.rb
      (Or.inl ⟨F.rc.symm,fun e => bcOff e.symm⟩)
      (Or.inr (Or.inr ⟨cx.symm,fun e => F.off_r_of_inner hx e.symm,fun e => bx e.symm⟩))

theorem no_edge_between_exclusive (budget : treeNumber G ≤ 5) {x y : V}
    (xI : x ∈ F.inner) (yI : y ∈ F.inner) (bx : G.Adj F.b x) (byOff : ¬ G.Adj F.b y) :
    ¬ G.Adj x y := by
  intro xy
  exact F.quad_forbidden budget F.bB xI.1 yI.1 bx.ne (Ne.symm yI.2.1) xy.ne F.rb
    (Or.inr ⟨bx.symm,fun e => F.off_r_of_inner xI e.symm⟩)
    (Or.inr (Or.inr ⟨xy.symm,fun e => F.off_r_of_inner yI e.symm,fun e => byOff e.symm⟩))

#print axioms CubicMixedCut.dominates_inner
#print axioms CubicMixedCut.both_contacts_of_nonadjacent
#print axioms CubicMixedCut.no_edge_between_exclusive

end CubicMixedCut
end Graffiti199Depleted.Catalogue
