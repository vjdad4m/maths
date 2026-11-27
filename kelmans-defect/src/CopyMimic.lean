import CubeBrick

open Finset
namespace KelmansCactus.CopyMimic
open ThreePort Substitute

variable {X Y : Type*} [DecidableEq X] [DecidableEq Y]
variable {G : SimpleGraph X} {H : SimpleGraph Y}

private theorem map_sat (e : X ↪ Y) {S R : Finset X} :
    (S \ R).map e = S.map e \ R.map e := by
  ext y
  constructor
  · intro hy
    obtain ⟨x,hx,rfl⟩ := mem_map.mp hy
    obtain ⟨xs,xr⟩ := mem_sdiff.mp hx
    exact mem_sdiff.mpr ⟨mem_map.mpr ⟨x,xs,rfl⟩,fun h => by
      obtain ⟨z,zr,ez⟩ := mem_map.mp h
      exact xr ((e.injective ez) ▸ zr)⟩
  · intro hy
    obtain ⟨ys,yr⟩ := mem_sdiff.mp hy
    obtain ⟨x,xs,rfl⟩ := mem_map.mp ys
    exact mem_map.mpr ⟨x,mem_sdiff.mpr ⟨xs,fun h => yr (mem_map.mpr ⟨x,h,rfl⟩)⟩,rfl⟩

private theorem map_biun {I : Type*} (e : X ↪ Y) (J : Finset I) (F : I → Finset X) :
    (J.biUnion F).map e = J.biUnion (fun i => (F i).map e) := by
  ext z
  constructor
  · intro zz
    obtain ⟨x,hx,hz⟩ := mem_map.mp zz
    obtain ⟨i,hi,xi⟩ := mem_biUnion.mp hx
    exact mem_biUnion.mpr ⟨i,hi,mem_map.mpr ⟨x,xi,hz⟩⟩
  · intro zz
    obtain ⟨i,hi,hz⟩ := mem_biUnion.mp zz
    obtain ⟨x,xi,ex⟩ := mem_map.mp hz
    exact mem_map.mpr ⟨x,mem_biUnion.mpr ⟨i,hi,xi⟩,ex⟩

theorem local_map {S : Finset X} {P : Finset (Finset X)} (e : X ↪ Y)
    (adj : ∀ u ∈ S, ∀ v ∈ S, G.Adj u v → H.Adj (e u) (e v)) (h : Assemble.LocalPart G P S) :
    Assemble.LocalPart H (P.map ⟨fun t => t.map e,map_injective e⟩) (S.map e) := by
  let setmap : Finset X ↪ Finset Y := ⟨fun t => t.map e,map_injective e⟩
  change Assemble.LocalPart H (P.map setmap) (S.map e)
  constructor
  · intro s hs
    obtain ⟨t,ht,rfl⟩ := mem_map.mp hs
    obtain ⟨hcard,c,hct,hstar⟩ := h.tile t ht
    refine ⟨by simpa [setmap] using hcard,e c,mem_map.mpr ⟨c,hct,rfl⟩,?_⟩
    intro v hv ne
    obtain ⟨u,ut,rfl⟩ := mem_map.mp hv
    exact adj c (h.tile_sub G ht hct) u (h.tile_sub G ht ut) (hstar u ut (fun he => ne (congrArg e he)))
  · intro s hs t ht ne
    obtain ⟨a,ha,rfl⟩ := mem_map.mp hs
    obtain ⟨b,hb,rfl⟩ := mem_map.mp ht
    exact (Finset.disjoint_map e).mpr (h.disj a ha b hb (fun he => ne (congrArg setmap he)))
  · rw [← h.cover,map_biun]
    ext v
    constructor
    · intro hv
      obtain ⟨t,ht,vt⟩ := mem_biUnion.mp hv
      obtain ⟨u,uu,rfl⟩ := mem_map.mp ht
      exact mem_biUnion.mpr ⟨u,uu,vt⟩
    · intro hv
      obtain ⟨t,ht,vt⟩ := mem_biUnion.mp hv
      exact mem_biUnion.mpr ⟨setmap t,mem_map.mpr ⟨t,ht,rfl⟩,vt⟩

theorem signature_map {S : Finset X} {p : Fin 3 → X} {w : Fin 3 → Nat} (e : X ↪ Y)
    (adj : ∀ u ∈ S, ∀ v ∈ S, G.Adj u v → H.Adj (e u) (e v)) (h : Signature (G:=G) S p w) :
    Signature (G:=H) (S.map e) (fun i => e (p i)) w := by
  obtain ⟨F,hF,dis,P,hP⟩ := h
  refine ⟨fun i => (F i).map e,?_,fun i j ne => (Finset.disjoint_map e).mpr (dis i j ne),?_⟩
  · intro i
    refine ⟨by simpa using (hF i).1,⟨?_,?_,?_⟩⟩
    · intro u hu
      obtain ⟨v,vf,rfl⟩ := mem_map.mp hu
      exact mem_map.mpr ⟨v,(hF i).2.inside vf,rfl⟩
    · rintro ⟨u,hu⟩
      obtain ⟨v,vf,rfl⟩ := mem_map.mp hu
      exact mem_map.mpr ⟨p i,(hF i).2.includes ⟨v,vf⟩,rfl⟩
    · intro v hv ne
      obtain ⟨u,uf,rfl⟩ := mem_map.mp hv
      exact adj (p i) ((hF i).2.inside ((hF i).2.includes ⟨u,uf⟩))
        u ((hF i).2.inside uf) ((hF i).2.star u uf (fun he => ne (congrArg e he)))
  · have tmp := local_map e (fun u hu v hv => adj u (mem_sdiff.mp hu).1 v (mem_sdiff.mp hv).1) hP
    rw [map_sat,map_biun] at tmp
    exact ⟨_,tmp⟩

theorem mimic_map {S : Finset X} {p : Fin 3 → X} (e : X ↪ Y)
    (adj : ∀ u ∈ S, ∀ v ∈ S, G.Adj u v → H.Adj (e u) (e v)) (h : Mimic G S p) :
    Mimic H (S.map e) (fun i => e (p i)) :=
  ⟨fun i => signature_map e adj (h.leaf i),fun i j ne => signature_map e adj (h.center i j ne)⟩

/-- Every embedded cube with one suppressed root has the needed
three-port states. Extra edges in the ambient graph are harmless. -/
theorem embedded_cube (e : Fin 8 ↪ Y)
    (adj : ∀ u ∈ CubeBrick.W, ∀ v ∈ CubeBrick.W, CubeBrick.cube.Adj u v → H.Adj (e u) (e v)) :
    Mimic H (CubeBrick.W.map e) (fun i => e (CubeBrick.ports i)) :=
  mimic_map e adj CubeBrick.cube_mimic

#print axioms embedded_cube
end KelmansCactus.CopyMimic
