import Row1078
import Proof137

namespace BullCover1125
open SimpleGraph Finset
variable {V : Type*}

def listed {n : ℕ} (edges : List (Fin n × Fin n)) : SimpleGraph (Fin n) where
  Adj x y := x ≠ y ∧ ((x,y) ∈ edges ∨ (y,x) ∈ edges)
  symm := fun _ _ h => ⟨h.1.symm,h.2.symm⟩
  loopless := fun _ h => h.1 rfl

instance {n} (edges : List (Fin n × Fin n)) : DecidableRel (listed edges).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ (_ ∨ _)))

abbrev claw := listed (n:=4) [(0,1),(0,2),(0,3)]
/-- Triangle 0,1,4, with leaves 2 at 0 and 3 at 1. -/
abbrev bull := listed (n:=5) [(0,1),(0,2),(1,3),(0,4),(1,4)]

def Free {W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) := ¬ Nonempty (H ↪g G)

theorem free_subgraph {U W : Type*} {H : SimpleGraph U} {G : SimpleGraph V} {P : SimpleGraph W}
    (h : Free G P) (e : H ↪g G) : Free H P := fun ⟨f⟩ => h ⟨f.trans e⟩

theorem claw_neighbors {G : SimpleGraph V} (hc : Free G claw) {v a b c : V}
    (va : G.Adj v a) (vb : G.Adj v b) (vc : G.Adj v c)
    (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c) :
    G.Adj a b ∨ G.Adj a c ∨ G.Adj b c := by
  by_contra! bad
  obtain ⟨nab,nac,nbc⟩ := bad
  let f : Fin 4 → V := ![v,a,b,c]
  have neq (i j : Fin 4) (ne : i ≠ j) : f i ≠ f j := by
    fin_cases i <;> fin_cases j <;> simp_all [f,va.ne,vb.ne,vc.ne,ne_comm]
  have rel (i j : Fin 4) : G.Adj (f i) (f j) ↔ claw.Adj i j := by
    fin_cases i <;> fin_cases j <;>
      simp [f,listed,va,vb,vc,nab,nac,nbc,va.symm,vb.symm,vc.symm,
        G.adj_comm b a,G.adj_comm c a,G.adj_comm c b]
  exact hc ⟨⟨⟨f,fun _ _ h => Classical.byContradiction (fun ne => neq _ _ ne h)⟩,rel _ _⟩⟩

/-- The adjacency specifications uniquely distinguish all five rows of the
bull, so a map realizing these specifications is automatically injective. -/
theorem bull_pattern {G : SimpleGraph V} (hb : Free G bull) {a b x y z : V}
    (ab : G.Adj a b) (ax : G.Adj a x) (by' : G.Adj b y)
    (az : G.Adj a z) (bz : G.Adj b z)
    (bx : ¬ G.Adj b x) (ay : ¬ G.Adj a y) (xy : ¬ G.Adj x y)
    (xz : ¬ G.Adj x z) (yz : ¬ G.Adj y z) : False := by
  let f : Fin 5 → V := ![a,b,x,y,z]
  have rel (i j : Fin 5) : G.Adj (f i) (f j) ↔ bull.Adj i j := by
    fin_cases i <;> fin_cases j <;>
      simp [f,listed,ab,ax,by',az,bz,ab.symm,ax.symm,by'.symm,az.symm,bz.symm,bx,ay,xy,xz,yz,
        G.adj_comm x b,G.adj_comm y a,G.adj_comm y x,G.adj_comm z x,G.adj_comm z y]
  have rows : ∀ i j : Fin 5, i ≠ j → ∃ k, ¬ (bull.Adj i k ↔ bull.Adj j k) := by decide
  have inj : Function.Injective f := by
    intro i j eq
    apply Classical.byContradiction
    intro ne
    obtain ⟨k,h⟩ := rows _ _ ne
    exact h ((rel i k).symm.trans (eq ▸ rel j k))
  exact hb ⟨⟨⟨f,inj⟩,rel _ _⟩⟩

theorem cograph_bull_free {G : SimpleGraph V} (hp : ¬ Graffiti137.InducedPath G 4) : Free G bull := by
  rintro ⟨f⟩
  let p : Fin 4 → Fin 5 := ![2,0,1,3]
  have inj : ∀ i j, p i = p j → i=j := by decide
  have path : ∀ i j, bull.Adj (p i) (p j) ↔ Graffiti137.Consecutive i j := by
    unfold Graffiti137.Consecutive
    decide
  exact hp ⟨⟨fun i => f (p i),fun i j eq => inj i j (f.injective eq)⟩,
    fun i j => f.map_rel_iff.trans (path i j)⟩

end BullCover1125
