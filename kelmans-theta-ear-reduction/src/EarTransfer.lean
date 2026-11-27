import SquareCapFactor

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.EarTransfer
open SquareCap (FactorOn IsTile factor_map)
noncomputable section

variable {V : Type*}

private theorem factor_single {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {S : Finset V} (h : IsTile G S) : FactorOn G S := by
  refine ⟨{S},?_,?_,by simp⟩
  · intro A ha
    obtain rfl := mem_singleton.mp ha
    exact h
  · intro A ha B hb ne
    exact (ne ((mem_singleton.mp ha).trans (mem_singleton.mp hb).symm)).elim

private theorem factor_disjUnion {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {S T : Finset V} (hs : FactorOn G S) (ht : FactorOn G T)
    (d : Disjoint S T) : FactorOn G (S ∪ T) := by
  obtain ⟨P,p,q,r⟩ := hs
  obtain ⟨Q,u,v,w⟩ := ht
  have pq {A B : Finset V} (ha : A ∈ P) (hb : B ∈ Q) : Disjoint A B := by
    apply disjoint_left.mpr
    intro x xa xb
    exact disjoint_left.mp d (r ▸ mem_biUnion.mpr ⟨A,ha,xa⟩) (w ▸ mem_biUnion.mpr ⟨B,hb,xb⟩)
  refine ⟨P∪Q,?_,?_,?_⟩
  · intro A ha
    exact (mem_union.mp ha).elim (p A) (u A)
  · intro A ha B hb ne
    rcases mem_union.mp ha with hp|hq <;> rcases mem_union.mp hb with kp|kq
    · exact q A hp B kp ne
    · exact pq hp kq
    · exact (pq kp hq).symm
    · exact v A hq B kq ne
  · ext x
    rw [←r,←w,mem_union]
    constructor
    · intro hx
      obtain ⟨A,ha,hax⟩ := mem_biUnion.mp hx
      exact (mem_union.mp ha).elim (fun hp => Or.inl (mem_biUnion.mpr ⟨A,hp,hax⟩))
        (fun hq => Or.inr (mem_biUnion.mpr ⟨A,hq,hax⟩))
    · intro hx
      rcases hx with hp | hq
      · obtain ⟨A,ha,hm⟩ := mem_biUnion.mp hp
        exact mem_biUnion.mpr ⟨A,mem_union.mpr (Or.inl ha),hm⟩
      · obtain ⟨A,ha,hm⟩ := mem_biUnion.mp hq
        exact mem_biUnion.mpr ⟨A,mem_union.mpr (Or.inr ha),hm⟩


private theorem triple_card {T : Type*} [DecidableEq T] {a b c : T}
    (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c) :
    ({a,b,c} : Finset T).card = 3 := by
  simp [card_insert_of_not_mem,ab,ac,bc]


private theorem tile_path {T : Type*} [DecidableEq T]
    {G : SimpleGraph T} {x y z : T} (xy : G.Adj x y) (yz : G.Adj y z) (xz : x ≠ z) :
    IsTile G {x,y,z} := by
  refine ⟨triple_card xy.ne xz yz.ne,y,by simp,?_⟩
  intro w hw ne
  simp only [mem_insert,mem_singleton] at hw
  rcases hw with rfl|rfl|rfl
  · exact xy.symm
  · exact (ne rfl).elim
  · exact yz


private abbrev out (v : V) : V ⊕ Fin 9 := Sum.inl v
private abbrev ear (v : Fin 9) : V ⊕ Fin 9 := Sum.inr v

private theorem ear_ne (i j : Fin 9) (h : i ≠ j) : ear (V:=V) i ≠ ear j :=
  fun e => h (Sum.inr_injective e)

structure EarTarget (G : SimpleGraph V) (H : SimpleGraph (V ⊕ Fin 9)) : Prop where
  e01 : H.Adj (ear 0) (ear 1)
  e12 : H.Adj (ear 1) (ear 2)
  e34 : H.Adj (ear 3) (ear 4)
  e45 : H.Adj (ear 4) (ear 5)
  e78 : H.Adj (ear 7) (ear 8)
  exterior : ∀ x y,G.Adj x y → H.Adj (out x) (out y)

/-- After absorbing a pair of adjacent theta contacts, a factor in
the exterior minus either new contact transfers without using
any other wire. The old six vertices tile as two paths, and the
absorbed pair and the selected exterior contact form the third. -/
theorem close_after_absorbing_edge [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {H : SimpleGraph (V ⊕ Fin 9)} (target : EarTarget G H)
    (x : V) (outside : FactorOn G (univ.erase x))
    (wire : H.Adj (out x) (ear 7) ∨ H.Adj (out x) (ear 8)) :
    FactorOn H (univ.erase (ear 6)) := by
  let f : V ↪ V⊕Fin 9 := ⟨Sum.inl,Sum.inl_injective⟩
  let J := ((univ : Finset V).erase x).map f
  let A : Finset (V ⊕ Fin 9) := {ear 0,ear 1,ear 2}
  let B : Finset (V ⊕ Fin 9) := {ear 3,ear 4,ear 5}
  let C : Finset (V ⊕ Fin 9) := {out x,ear 7,ear 8}
  have A0 : IsTile H A := tile_path target.e01 target.e12 (ear_ne _ _ (by decide))
  have B0 : IsTile H B := tile_path target.e34 target.e45 (ear_ne _ _ (by decide))
  have C0 : IsTile H C := by
    rcases wire with p|q
    · exact tile_path p target.e78 (by simp)
    · have seen := tile_path q target.e78.symm (by simp)
      have eq : ({out x,ear 8,ear 7}:Finset (V⊕Fin 9))=C := by
        ext u
        simp [C,or_assoc,or_left_comm,or_comm]
      exact eq ▸ seen
  have dj1 : Disjoint A B := by simp [A,B,disjoint_left]
  have dj2 : Disjoint (A∪B) C := by simp [A,B,C,disjoint_left]
  have dj3 : Disjoint J ((A∪B)∪C) := by
    simp [J,A,B,C,f,mem_map,disjoint_left]
  have ringCheck : ∀ i : Fin 9,
      (i=0∨i=1∨i=2 ∨ (i=3∨i=4∨i=5) ∨ i=7∨i=8) ↔ i≠6 := by decide
  have support : J ∪ ((A∪B)∪C) = (univ : Finset (V⊕Fin 9)).erase (ear 6) := by
    ext v
    cases v with
    | inl u => by_cases e : u=x <;> simp [J,A,B,C,f,mem_map,e]
    | inr i => simpa [J,A,B,C,f,mem_map,or_assoc,or_left_comm,or_comm] using ringCheck i
  have inside := factor_disjUnion
    (factor_disjUnion (factor_single A0) (factor_single B0) dj1)
    (factor_single C0) dj2
  exact support ▸ factor_disjUnion (factor_map f target.exterior outside) inside dj3

#print axioms close_after_absorbing_edge
end
end KelmansCactus.AtomicBridge.EarTransfer
