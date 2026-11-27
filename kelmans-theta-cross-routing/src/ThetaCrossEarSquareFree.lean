import ThetaCase
import TwinObstruction

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaCrossEarSquareFree
open PentagonCap (SmallFourTrivial)
open PentagonProfile (Port)
noncomputable section

private theorem square_forbidden
    {W : Type*} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (small4 : SmallFourTrivial H) (cub : ∀ w,H.degree w=3)
    {a b c d x y z : W} (ab : H.Adj a b) (bc : H.Adj b c)
    (cd : H.Adj c d) (da : H.Adj d a) (ac : a≠c) (bd : b≠d)
    (hx : x∉({a,b,c,d} : Finset W)) (hy : y∉({a,b,c,d} : Finset W))
    (hz : z∉({a,b,c,d} : Finset W)) (xy : x≠y) (xz : x≠z) (yz : y≠z) :
    False := by
  let S : Finset W := {a,b,c,d}
  let f : W→Bool := fun u=>decide (u∈S)
  have sa : a∈S := by simp [S]
  have sb : b∈S := by simp [S]
  have sc : c∈S := by simp [S]
  have sd : d∈S := by simp [S]
  have inside (u : W) (hu : u∈S) : ∃ v∈S, ∃ w∈S, v≠w ∧ H.Adj u v ∧ H.Adj u w := by
    simp only [S,mem_insert,mem_singleton] at hu
    rcases hu with rfl|rfl|rfl|rfl
    · exact ⟨b,sb,d,sd,bd,ab,da.symm⟩
    · exact ⟨a,sa,c,sc,ac,ab.symm,bc⟩
    · exact ⟨b,sb,d,sd,bd,bc.symm,cd⟩
    · exact ⟨a,sa,c,sc,ac,da,cd.symm⟩
  have hbound : (SquareCap.boundary H f).card≤S.card :=
    TwinObstruction.cut_le_exposed_vertices S S (fun _ ht _ _ _=>ht)
      (fun u _=>le_of_eq (cub u)) inside
  have len : S.card≤4 := by
    have e : S.card=4 := by
      simp [S,card_insert_of_not_mem,ab.ne,ac,da.ne.symm,bc.ne,bd,cd.ne]
    omega
  obtain ⟨w,triv⟩ := small4 f (hbound.trans len)
  cases w
  · exact (triv x y z (by simpa [f,S] using hx) (by simpa [f,S] using hy)
        (by simpa [f,S] using hz)).elim xy (fun h=>h.elim xz yz)
  · exact (triv a b c (by simp [f,sa]) (by simp [f,sb]) (by simp [f,sc])).elim
      ab.ne (fun h=>h.elim ac bc.ne)

/-- In the exact theta domain this uses only the ambient cut axiom
and cubicity; the three unmarked vertices can be taken inside the theta. -/
theorem no_exterior_square {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {p : Port↪V}
    [DecidableRel (ThetaCase.ambient G p).Adj]
    (cub : ∀ v,(ThetaCase.ambient G p).degree v=3)
    (small4 : SmallFourTrivial (ThetaCase.ambient G p)) :
    ∀ a b c d : V,G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a=c∨b=d := by
  intro a b c d ab bc cd da
  by_cases ac : a=c
  · exact Or.inl ac
  by_cases bd : b=d
  · exact Or.inr bd
  exfalso
  exact square_forbidden small4 cub (x:=Sum.inr 0) (y:=Sum.inr 1) (z:=Sum.inr 2)
    (a:=Sum.inl a) (b:=Sum.inl b) (c:=Sum.inl c) (d:=Sum.inl d)
    ab bc cd da (fun e=>ac (Sum.inl_injective e)) (fun e=>bd (Sum.inl_injective e))
    (by simp) (by simp) (by simp)
    (fun e=>(by decide : (0:Fin 7)≠1) (Sum.inr_injective e))
    (fun e=>(by decide : (0:Fin 7)≠2) (Sum.inr_injective e))
    (fun e=>(by decide : (1:Fin 7)≠2) (Sum.inr_injective e))

#print axioms no_exterior_square
end
end KelmansCactus.AtomicBridge.ThetaCrossEarSquareFree
