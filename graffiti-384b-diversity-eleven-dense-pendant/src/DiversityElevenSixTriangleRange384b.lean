import SixUntouchedHost384b
import DiversityElevenPendantGeometry384b

namespace Graffiti384b.DiversityEleven
open Finset SimpleGraph ShorePairs
open private Graffiti384b.DiversityEleven.count_in_range from SixUntouchedHost384b
variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem triangle_range (U : Finset V) (a : Fin 6 ≃ U) (i : Fin 6)
    (closed : ∀ x y, G.Adj (a i).val x → G.Adj (a i).val y → G.Adj x y → x∈U ∧ y∈U) :
    let H := G.comap (fun i => (a i).val)
    letI : DecidableRel H.Adj := fun x y => inferInstanceAs (Decidable (G.Adj (a x).val (a y).val))
    trianglesAt H i=trianglesAt G (a i).val := by
  classical
  let H := G.comap (fun i => (a i).val)
  letI : DecidableRel H.Adj := fun x y => inferInstanceAs (Decidable (G.Adj (a x).val (a y).val))
  let em : Fin 6 ↪ V := a.toEmbedding.trans (Function.Embedding.subtype _)
  change (pairs H (H.neighborFinset i)).card = (pairs G (G.neighborFinset (a i).val)).card
  have eq : (pairs H (H.neighborFinset i)).image (fun s=>s.map em)=
      pairs G (G.neighborFinset (a i).val) := by
    ext p
    constructor
    · intro pm
      obtain ⟨q,qs,rfl⟩ := mem_image.mp pm
      obtain ⟨x,xm,y,ym,xy,rfl⟩ := (pair_mem H).mp qs
      have x1 : (a x).val∈G.neighborFinset (a i).val := (G.mem_neighborFinset ..).mpr
        ((H.mem_neighborFinset ..).mp xm)
      have y1 : (a y).val∈G.neighborFinset (a i).val := (G.mem_neighborFinset ..).mpr
        ((H.mem_neighborFinset ..).mp ym)
      exact (pair_mem G).mpr ⟨(a x).val,x1,(a y).val,y1,xy,by simp [em]⟩
    · intro pm
      obtain ⟨x,xm,y,ym,xy,rfl⟩ := (pair_mem G).mp pm
      obtain ⟨xu,yu⟩ := closed x y ((G.mem_neighborFinset ..).mp xm) ((G.mem_neighborFinset ..).mp ym) xy
      let xi : Fin 6 := a.symm ⟨x,xu⟩
      let yi : Fin 6 := a.symm ⟨y,yu⟩
      have xx : (a xi).val=x := by simp [xi]
      have yy : (a yi).val=y := by simp [yi]
      have jx : xi∈H.neighborFinset i := (H.mem_neighborFinset ..).mpr
        (by change G.Adj (a i).val (a xi).val; rw [xx]; exact (G.mem_neighborFinset ..).mp xm)
      have jy : yi∈H.neighborFinset i := (H.mem_neighborFinset ..).mpr
        (by change G.Adj (a i).val (a yi).val; rw [yy]; exact (G.mem_neighborFinset ..).mp ym)
      have e : H.Adj xi yi := by change G.Adj (a xi).val (a yi).val; rwa [xx,yy]
      exact mem_image.mpr ⟨{xi,yi},(pair_mem H).mpr ⟨xi,jx,yi,jy,e,rfl⟩,by
        simp [em,xi,yi]⟩
  rw [←eq,card_image_of_injective _ (Finset.map_injective em)]

/-- Six-selector lift allowing lost edges at zero-tagged vertices, provided
no triangle at such a vertex is lost. This is stronger than requiring its
ambient neighborhood to lie wholly within the six-vertex board. -/
theorem six_pair_of_triangle_closed (select : SixSelector)
    {U Z : Finset V} (sz : U.card=6)
    (deg : ∀ v∈Z, 3≤nbr G v U)
    (min : ∀ v∈Z, 2≤trianglesAt G v)
    (scores : Set.InjOn (trianglesAt G) (Z : Set V))
    (closed : ∀ v∈Z, ∀ x y, G.Adj v x → G.Adj v y → G.Adj x y → x∈U ∧ y∈U) :
    ∃ p∈U, ∃ q∈U, p≠q ∧
      ∀ v∈U, v≠p → v≠q →
        (v∈Z → G.Adj v p ∧ G.Adj v q) ∧
          (v∉Z → 2≤nbr G v U → G.Adj v p ∨ G.Adj v q) := by
  classical
  let a : Fin 6 ≃ U := (Fintype.equivFinOfCardEq
    (show Fintype.card U=6 by rwa [Fintype.card_coe])).symm
  let H := G.comap (fun i => (a i).val)
  let dec : DecidableRel H.Adj := fun i j => inferInstanceAs (Decidable (G.Adj (a i).val (a j).val))
  letI := dec
  let C := univ.filter (fun i : Fin 6 => (a i).val∈Z)
  have tag (i : Fin 6) : i∈C ↔ (a i).val∈Z := by simp [C]
  have hd (i : Fin 6) : H.degree i=nbr G (a i).val U := Graffiti384b.DiversityEleven.count_in_range G U a i
  have ht (i : Fin 6) (iz : i∈C) : trianglesAt H i=trianglesAt G (a i).val :=
    triangle_range G U a i (closed _ ((tag i).mp iz))
  have vmin : ∀ i∈C, 3≤H.degree i ∧ 2≤trianglesAt H i := by
    intro i ih
    rw [hd,ht i ih]
    exact ⟨deg _ ((tag i).mp ih),min _ ((tag i).mp ih)⟩
  have sc : Set.InjOn (trianglesAt H) (C : Set (Fin 6)) := by
    intro i ih j jh eq
    apply a.injective
    apply Subtype.ext
    exact scores ((tag i).mp ih) ((tag j).mp jh)
      ((ht i ih).symm.trans (eq.trans (ht j jh)))
  obtain ⟨p,q,pq,g⟩ := select H dec C vmin sc
  refine ⟨(a p).val,(a p).property,(a q).val,(a q).property,fun eq => pq (a.injective (Subtype.ext eq)),?_⟩
  intro v vu vp vq
  let i : Fin 6 := a.symm ⟨v,vu⟩
  have iv : (a i).val=v := by simp [i]
  have ip : i≠p := fun eq => vp (by rw [←iv,eq])
  have iq : i≠q := fun eq => vq (by rw [←iv,eq])
  obtain ⟨left,right⟩ := g i ip iq
  change (i∈C → G.Adj (a i).val (a p).val ∧ G.Adj (a i).val (a q).val) at left
  change (i∉C → 2≤H.degree i → G.Adj (a i).val (a p).val ∨ G.Adj (a i).val (a q).val) at right
  have z : i∈C ↔ v∈Z := (tag i).trans (by rw [iv])
  rw [hd,iv] at right
  rw [iv] at left
  exact ⟨fun hv => left (z.mpr hv),fun hv => right (fun c => hv (z.mp c))⟩

#print axioms six_pair_of_triangle_closed
end Graffiti384b.DiversityEleven
