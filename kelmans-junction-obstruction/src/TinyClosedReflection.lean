import Substitute

open Finset
namespace KelmansCactus.AtomicBridge
open Substitute
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

theorem closed_three_iff_tile {S : Finset V} (size : S.card=3) :
    Closed G S ↔ KelmansStarter.IsTile G S := by
  constructor
  · rintro ⟨P,h⟩
    obtain ⟨v,vs⟩ := card_pos.mp (by omega : 0<S.card)
    obtain ⟨T,ht,_⟩ := mem_biUnion.mp (h.cover.symm ▸ vs)
    have til := h.tile T ht
    have st : S.card≤T.card := by rw [size,til.1]
    have eq := eq_of_subset_of_card_le (h.tile_sub G ht) st
    exact eq ▸ til
  · exact tile_closed

/-- At order six it suffices to check the single tile incident to an
arbitrary anchor. This avoids exhaustive enumeration of set partitions. -/
theorem closed_six_iff_anchor {S : Finset V} {a : V} (ha : a∈S) (size : S.card=6) :
    Closed G S ↔
      ∃ u∈S, ∃ v∈S, KelmansStarter.IsTile G {a,u,v} ∧
        KelmansStarter.IsTile G (S\{a,u,v}) := by
  constructor
  · rintro ⟨P,hP⟩
    obtain ⟨T,hT,aT⟩ := mem_biUnion.mp (hP.cover.symm ▸ ha)
    change a∈T at aT
    have tile := hP.tile T hT
    have ec : (T.erase a).card=2 := by rw [card_erase_of_mem aT,tile.1]
    obtain ⟨u,v,_,uv⟩ := card_eq_two.mp ec
    have ts := hP.tile_sub G hT
    have eql : T={a,u,v} := by rw [←insert_erase aT,uv]
    have rem : (S\T).card=3 := by rw [card_sdiff ts,size,tile.1]
    have fit : KelmansStarter.IsTile G (S\T) :=
      (closed_three_iff_tile rem).mp ⟨_,remove_tile hP hT⟩
    exact ⟨u,ts (by simp [eql]),v,ts (by simp [eql]),eql ▸ tile,eql ▸ fit⟩
  · rintro ⟨u,us,v,vs,t,rem⟩
    let T : Finset V := {a,u,v}
    have ts : T⊆S := insert_subset_iff.mpr ⟨ha,insert_subset_iff.mpr ⟨us,singleton_subset_iff.mpr vs⟩⟩
    have d : Disjoint (S\T) T := disjoint_left.mpr fun _ ht tt=>(mem_sdiff.mp ht).2 tt
    have eq := sdiff_union_of_subset ts
    exact eq ▸ add_closed (tile_closed rem) (tile_closed t) d

#print axioms closed_six_iff_anchor
end KelmansCactus.AtomicBridge
