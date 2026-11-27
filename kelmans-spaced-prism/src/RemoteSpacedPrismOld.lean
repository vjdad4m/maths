import RemoteSpacedPrismLayout
import RemoteVacancySeparation

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteSpacedPrismOld
open RemoteSpacedPrismLayout
open RemoteSpacedPrismHandle (Port)
open RemoteVacancyReach (Packing)
open RemoteVacancySeparation (holes)
open SquareCap (HasFactor IsTile)

abbrev Index (k : Nat) := Fin (2*gap k)×Bool

def rowVertex {k : Nat} (j : Index k) (r : Fin 3) : Core k :=
  (⟨3*j.1.val+r.val,by
    have a := j.1.isLt
    have b := r.isLt
    simp only [columns]
    omega⟩,j.2)

def owner {k : Nat} (v : Core k) : Index k :=
  (⟨v.1.val/3,(Nat.div_lt_iff_lt_mul (by decide)).mpr (by
    have a:=v.1.isLt
    simp only [columns] at a
    omega)⟩,v.2)

theorem owner_of_vertex {k : Nat} (j : Index k) (r : Fin 3) :
    owner (rowVertex j r)=j := by
  apply Prod.ext
  · apply Fin.ext
    change (3*j.1.val+r.val)/3=j.1.val
    have z := r.isLt
    omega
  · rfl

theorem vertex_of_owner {k : Nat} (v : Core k) :
    rowVertex (owner v) ⟨v.1.val%3,Nat.mod_lt _ (by decide)⟩=v := by
  apply Prod.ext
  · apply Fin.ext
    change 3*(v.1.val/3)+v.1.val%3=v.1.val
    exact Nat.div_add_mod _ _
  · rfl

def tile {k : Nat} (j : Index k) : Finset (Core k) :=
  {rowVertex j 0,rowVertex j 1,rowVertex j 2}

theorem tile_owner {k : Nat} {j : Index k} {v : Core k}
    (m : v∈tile j) : owner v=j := by
  simp only [tile,mem_insert,mem_singleton] at m
  rcases m with e|e|e <;> rw [e,owner_of_vertex]

def CoreSource (k : Nat) : SimpleGraph (Core k) :=
  (board k).comap Sum.inl

theorem core_source_adj (k : Nat) (v w : Core k) :
    (CoreSource k).Adj v w ↔ (core k).Adj v w ∧ ¬(marks k).Removed v w := Iff.rfl

private theorem three_path {W : Type*} [DecidableEq W] (G : SimpleGraph W)
    {a b c : W} (ab : G.Adj a b) (bc : G.Adj b c) (ac : a≠c) :
    IsTile G ({a,b,c}:Finset W) := by
  refine ⟨by simp [ab.ne,bc.ne,ac],b,by simp,?_⟩
  intro d r ne
  simp only [mem_insert,mem_singleton] at r
  rcases r with rfl|rfl|rfl
  · exact ab.symm
  · contradiction
  · exact bc

theorem tile_path {k : Nat} (j : Index k) : IsTile (CoreSource k) (tile j) := by
  apply three_path
  · exact row_adj k (by rfl) j.2
  · exact row_adj k (by rfl) j.2
  · intro e
    have h := congrArg (fun v : Core k=>v.1.val) e
    change 3*j.1.val + 0 = 3*j.1.val + 2 at h
    omega

def source (k : Nat) : Finset (Finset (Core k)) := univ.image tile

theorem source_packing (k : Nat) : Packing (CoreSource k) (source k) := by
  constructor
  · intro A am
    obtain ⟨j,_,rfl⟩ := mem_image.mp am
    exact tile_path j
  · intro A am B bm ab
    obtain ⟨i,_,rfl⟩ := mem_image.mp am
    obtain ⟨j,_,rfl⟩ := mem_image.mp bm
    apply disjoint_left.mpr
    intro z zi zj
    exact ab (congrArg (tile (k:=k)) ((tile_owner zi).symm.trans (tile_owner zj)))

theorem source_cover (k : Nat) : (source k).biUnion id=univ := by
  apply eq_univ_iff_forall.mpr
  intro x
  refine mem_biUnion.mpr ⟨tile (owner x),mem_image.mpr ⟨owner x,mem_univ _,rfl⟩,?_⟩
  have fy := vertex_of_owner x
  let r : Fin 3 := ⟨x.1.val%3,Nat.mod_lt _ (by decide)⟩
  have e : r=0 ∨ r=1 ∨ r=2 := by
    have h : ∀ s : Fin 3,s=0∨s=1∨s=2 := by decide
    exact h r
  change rowVertex (owner x) r=x at fy
  simp only [id_eq,tile,mem_insert,mem_singleton]
  rcases e with e|e|e <;> rw [e] at fy
  · exact Or.inl fy.symm
  · exact Or.inr (Or.inl fy.symm)
  · exact Or.inr (Or.inr fy.symm)

theorem source_factor (k : Nat) : HasFactor (CoreSource k) :=
  ⟨source k,(source_packing k).1,(source_packing k).2,source_cover k⟩

def oldEmb (k : Nat) : Core k↪Board k := ⟨Sum.inl,Sum.inl_injective⟩

def prior (k : Nat) : Finset (Finset (Board k)) :=
  (source k).image (Finset.map (oldEmb k))

theorem prior_packing (k : Nat) : Packing (board k) (prior k) := by
  constructor
  · intro T tm
    obtain ⟨S,sm,rfl⟩:=mem_image.mp tm
    obtain ⟨ct,c,cm,cent⟩ := (source_packing k).1 S sm
    refine ⟨(card_map _).trans ct,oldEmb k c,mem_map.mpr ⟨c,cm,rfl⟩,?_⟩
    intro z zm ne
    obtain ⟨w,wm,rfl⟩:=mem_map.mp zm
    exact cent w wm (fun e=>ne (congrArg (oldEmb k) e))
  · intro A am B bm ne
    obtain ⟨S,sm,rfl⟩:=mem_image.mp am
    obtain ⟨T,tm,rfl⟩:=mem_image.mp bm
    apply (disjoint_map _).mpr
    exact (source_packing k).2 S sm T tm (fun e=>ne (congrArg (Finset.map (oldEmb k)) e))

theorem old_covered (k : Nat) (v : Core k) : Sum.inl v ∈ (prior k).biUnion id := by
  have m : v∈(source k).biUnion id := source_cover k ▸ mem_univ _
  obtain ⟨T,tm,vm⟩ := mem_biUnion.mp m
  exact mem_biUnion.mpr ⟨T.map (oldEmb k),mem_image.mpr ⟨T,tm,rfl⟩,mem_map.mpr ⟨v,vm,rfl⟩⟩

theorem slot_free (k : Nat) (i : Port) : Sum.inr i∈holes (prior k) := by
  refine mem_sdiff.mpr ⟨mem_univ _,?_⟩
  intro h
  obtain ⟨T,tm,im⟩:=mem_biUnion.mp h
  obtain ⟨S,_,rfl⟩:=mem_image.mp tm
  obtain ⟨v,_,eq⟩:=mem_map.mp im
  cases eq

theorem vacancies (k : Nat) (v : Board k) :
    v∈holes (prior k) ↔ ∃ i : Port,v=Sum.inr i := by
  cases v with
  | inl a =>
    constructor
    · intro m
      exact ((mem_sdiff.mp m).2 (old_covered k a)).elim
    · rintro ⟨i,e⟩
      cases e
  | inr i =>
    exact ⟨fun _=>⟨i,rfl⟩,fun _=>slot_free k i⟩

#print axioms source_factor
#print axioms prior_packing
#print axioms vacancies
end KelmansCactus.AtomicBridge.RemoteSpacedPrismOld
