import Substitute

open Finset
namespace KelmansCactus.AtomicBridge
open Substitute

variable {V X : Type*} [DecidableEq V] [DecidableEq X]
variable {G : SimpleGraph V} {H : SimpleGraph X}

theorem closed_pullback {S : Finset V} (emb : V↪X)
    (old : ∀ u∈S,∀ v∈S,H.Adj (emb u) (emb v)→G.Adj u v)
    (h : Closed H (S.map emb)) : Closed G S := by
  classical
  obtain ⟨P,hP⟩ := h
  let pre (t : Finset X) : Finset V := S.filter (fun u=>emb u∈t)
  have pre_m {t : Finset X} {u : V} : u∈pre t ↔ u∈S ∧ emb u∈t := by simp [pre]
  have map_pre {t : Finset X} (ht : t ∈ P) : (pre t).map emb=t := by
    ext x
    constructor
    · rintro hx
      obtain ⟨u,hu,rfl⟩ := mem_map.mp hx
      exact (pre_m.mp hu).2
    · intro hx
      obtain ⟨u,us,rfl⟩ := mem_map.mp (hP.tile_sub H ht hx)
      exact mem_map.mpr ⟨u,pre_m.mpr ⟨us,hx⟩,rfl⟩
  refine ⟨P.image pre,⟨?_,?_,?_⟩⟩
  · intro t tm
    obtain ⟨T,TP,rfl⟩ := mem_image.mp tm
    obtain ⟨n,c,cT,adj⟩ := hP.tile T TP
    obtain ⟨k,ks,rfl⟩ := mem_map.mp (hP.tile_sub H TP cT)
    have cN : (pre T).card=3 := by rw [←card_map emb,map_pre TP,n]
    refine ⟨cN,k,pre_m.mpr ⟨ks,cT⟩,?_⟩
    intro w ww ne
    obtain ⟨ws,wT⟩ := pre_m.mp ww
    exact old k ks w ws (adj (emb w) wT (fun eq=>ne (emb.injective eq)))
  · intro t ht w hw ne
    obtain ⟨T,TP,rfl⟩ := mem_image.mp ht
    obtain ⟨W,WP,rfl⟩ := mem_image.mp hw
    apply disjoint_left.mpr
    intro v e1 e2
    have hn : T≠W := fun h=>ne (congrArg pre h)
    exact disjoint_left.mp (hP.disj _ TP _ WP hn) (pre_m.mp e1).2 (pre_m.mp e2).2
  · ext v
    constructor
    · intro h
      obtain ⟨x,xp,xv⟩ := mem_biUnion.mp h
      obtain ⟨T,_,rfl⟩ := mem_image.mp xp
      exact (pre_m.mp xv).1
    · intro h
      have hm : emb v∈P.biUnion id := hP.cover.symm ▸ mem_map.mpr ⟨v,h,rfl⟩
      obtain ⟨T,TP,vT⟩ := mem_biUnion.mp hm
      exact mem_biUnion.mpr ⟨pre T,mem_image.mpr ⟨T,TP,rfl⟩,pre_m.mpr ⟨h,vT⟩⟩

#print axioms closed_pullback
end KelmansCactus.AtomicBridge
