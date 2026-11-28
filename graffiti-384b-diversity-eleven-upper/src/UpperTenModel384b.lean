import UpperTenKernel384b
import Mathlib.Data.Fin.VecNotation

namespace Graffiti384b.DiversityEleven.CutTen
open Finset SimpleGraph

def fixedRows : Fin 4→Label→Nat := ![![1023,31,31,31,1023,241,241,241,273,529],![1023,127,31,31,1023,115,115,145,273,529],![1023,127,31,31,1023,115,115,145,273,529],![1023,63,63,31,1023,55,81,145,273,529]]
def trueRows : Fin 4→Label→Nat := ![![14,13,11,7,224,144,144,112,0,0],![14,93,11,7,98,80,50,0,0,0],![14,125,11,7,98,18,18,0,0,0],![14,29,59,7,38,20,0,0,0,0]]
def staticMotif (k : Fin 4) (i j : Label) : Option Bool :=
  if (fixedRows k i).testBit j.val then some ((trueRows k i).testBit j.val) else none

def cuts : Fin 4→Finset Nat :=
  ![{307,355,403,419},{181,213,229,403,419,451},{181,229,403,419},{121,211,213,227,229}]

private def pairs : Fin 45→Label×Label :=
  ![(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(3,4),(3,5),(3,6),(3,7),(3,8),(3,9),(4,5),(4,6),(4,7),(4,8),(4,9),(5,6),(5,7),(5,8),(5,9),(6,7),(6,8),(6,9),(7,8),(7,9),(8,9)]

private theorem slot_total : ∀ i j : Label, i<j→
    ∃ k : Fin 45,k.val=slot i.val j.val ∧ pairs k=(i,j) := by decide

theorem bits_of_model (G : SimpleGraph Label) [DecidableRel G.Adj]
    (M : Label→Label→Option Bool) (p : Label≃Label)
    (diag : ∀ i,M i i=some false)
    (hfix : ∀ i j b, M i j=some b → (G.Adj (p i) (p j) ↔ b=true)) :
    ∃ bits : Nat→Bool, ∀ i j,withBits M bits i j=true↔G.Adj (p i) (p j) := by
  let bits (k : Nat) := if h:k<45 then
    let t := pairs ⟨k,h⟩
    decide (G.Adj (p t.1) (p t.2))
    else false
  refine ⟨bits,?_⟩
  have ord (i j : Label) (ij : i<j) :
      bits (slot (min i.val j.val) (max i.val j.val))=true ↔ G.Adj (p i) (p j) := by
    have v : i.val<j.val := ij
    rw [min_eq_left v.le,max_eq_right v.le]
    obtain ⟨k,kval,xy⟩ := slot_total i j ij
    rw [←kval]
    simp only [bits,dif_pos k.isLt,xy,decide_eq_true_eq]
  intro i j
  unfold withBits
  cases e : M i j with
  | some z => exact (hfix i j z e).symm
  | none =>
    change bits (slot (min i.val j.val) (max i.val j.val))=true ↔ _
    rcases lt_trichotomy i j with ij|eq|ji
    · exact ord i j ij
    · subst j
      rw [diag] at e
      contradiction
    · rw [min_comm,max_comm,SimpleGraph.adj_comm]
      exact ord j i ji

#print axioms bits_of_model
end Graffiti384b.DiversityEleven.CutTen
