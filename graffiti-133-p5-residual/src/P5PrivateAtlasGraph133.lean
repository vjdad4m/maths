import P5PrivateAtlasMap133
import P5CorePrivateLayers133

namespace Graffiti133P5PrivateAtlas
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133Camby Graffiti133P5CoreShape
  Graffiti133PrivateGeneric
open scoped Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem private_layers_config (H : Hole G 5)
    (h4 : FourCycleFree G) (h9 : NoPath G 9)
    (D : Finset V) (cy : ∀ i,H.c i∈D) (h7 : NoPath (G.induce (D : Set V)) 7)
    (w q : Fin 5→V) (wd : ∀ i,w i∈D) (wo : ∀ i,Outside H.c (w i))
    (wpriv : ∀ i j,G.Adj (w i) (H.c j)↔j=i)
    (qpriv : ∀ i,PrivateAt G D (w i) (q i)) :
    ∃ m : Fin 32,m.val∈goodMasks ∧
      (∀ i : Fin 5,m.val.testBit i.val=decide (G.Adj (w i) (w (i+2)))) ∧
      (m.val=31 ∨ ∀ i j,¬G.Adj (q i) (q j)) := by
  classical
  let b (i : Fin 5) := decide (G.Adj (w i) (w (i+2)))
  obtain ⟨m,ms⟩ := encode_five_bits b
  have wi : Function.Injective w := by
    intro i j e
    exact ((wpriv j i).mp (e ▸ (wpriv i i).mpr rfl))
  have qi : Function.Injective q := by
    intro i j e
    by_contra ne
    exact (qpriv j).2.2 (w i) (wd i) (fun he=>ne (wi he)) (e ▸ (qpriv i).2.1)
  let a := layerTen H w
  have ai : Function.Injective a := ten_layer_injective H w wo wi
  have ad (i : Fin 10) : a i∈D := by
    dsimp only [a]
    by_cases lo : i.val<5
    · rw [layerTen,dif_pos lo]
      exact cy _
    · rw [layerTen,dif_neg lo]
      exact wd _
  have aFit : ∀ i j : Fin 10,G.Adj (a i) (a j)↔firstEdge m.val i.val j.val=true :=
    ten_layer_fit H h4 w wo wpriv m ms
  let f (i : Fin 10) : (D : Set V) := ⟨a i,ad i⟩
  have fi : Function.Injective f := fun i j e=>ai (congrArg Subtype.val e)
  have valid := private_mask_necessary m f fi (fun i j=>aFit i j) h7
  refine ⟨m,valid,ms,?_⟩
  by_cases full : m.val=31
  · exact Or.inl full
  refine Or.inr (fun i j e=>?_ )
  have cannot (i j : Fin 5) (ij : i<j) (ed : G.Adj (q i) (q j)) : False := by
    have fresh (i : Fin 5) (j : Fin 10) : q i≠a j := fun e=>(qpriv i).1 (e.symm ▸ ad j)
    have only (i : Fin 5) (j : Fin 10) : G.Adj (a j) (q i)↔j.val=i.val+5 := by
      have qn : G.Adj (a j) (q i) ↔ a j=w i := by
        constructor
        · intro edge
          by_contra he
          exact (qpriv i).2.2 (a j) (ad j) he edge.symm
        · intro eq
          exact eq.symm ▸ (qpriv i).2.1.symm
      rw [qn]
      have wj : a ⟨i.val+5,by have := i.isLt; omega⟩=w i := by
        dsimp only [a]
        rw [layerTen,dif_neg (by omega : ¬i.val+5<5)]
        congr 1
      rw [←wj,ai.eq_iff,Fin.ext_iff]
    let bf := layerFifteen H w q
    have bfI : Function.Injective bf := fifteen_layer_injective H w q ai qi fresh
    have bfFit : Fit G bf (outerSpec m i j) := fifteen_layer_fit H w q m i j aFit only ed
    exact outer_row_impossible m i j valid full ij h4 h9 bf bfI bfFit
  rcases lt_trichotomy i j with less|eq|more
  · exact cannot i j less e
  · exact e.ne (congrArg q eq)
  · exact cannot j i more e.symm

#print axioms private_layers_config
end Graffiti133P5PrivateAtlas
