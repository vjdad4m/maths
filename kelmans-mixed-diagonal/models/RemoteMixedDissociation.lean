import SquareCapFactor
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace KelmansCactus.AtomicBridge.RemoteMixedDissociation
open SimpleGraph Finset
open scoped BigOperators
open SquareCap (IsTile HasFactor)
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- A dissociated support induces maximum degree at most one. -/
def Sparse (G : SimpleGraph V) (W : Finset V) : Prop :=
  ∀ c∈W,∀ x∈W,∀ y∈W,G.Adj c x → G.Adj c y → x=y

omit [Fintype V] in
theorem tile_bound {W T : Finset V} (thin : Sparse G W)
    (tile : IsTile G T) : (T∩W).card≤2 := by
  obtain ⟨ct,c,hc,center⟩ := tile
  by_contra! high
  have exact : T∩W=T := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
  have sub : T⊆W := by
    intro x xt
    exact (Finset.mem_inter.mp (exact.symm ▸ xt)).2
  have bound : (T.erase c).card≤1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    have hx' := Finset.mem_erase.mp hx
    have hy' := Finset.mem_erase.mp hy
    exact thin c (sub hc) x (sub hx'.2) y (sub hy'.2)
      (center x hx'.2 hx'.1) (center y hy'.2 hy'.1)
  rw [Finset.card_erase_of_mem hc,ct] at bound
  omega

/-- Packing into triples forces every dissociated support to have at most
two thirds of the vertices. This applies to mixed-rank subgraphs as well. -/
theorem no_factor_if_sparse_large {W : Finset V} (thin : Sparse G W)
    (tooLarge : 2*Fintype.card V < 3*W.card) : ¬HasFactor G := by
  classical
  rintro ⟨P,legal,apart,cover⟩
  have num : 3*P.card=Fintype.card V := by
    have hsum : (P.biUnion id).card=∑ T∈P,T.card := by
      apply Finset.card_biUnion
      intro A hA B hB ne
      exact apart A hA B hB ne
    rw [cover,Finset.card_univ] at hsum
    calc
      3*P.card = ∑ _T∈P,(3:ℕ) := by simp [Nat.mul_comm]
      _ = ∑ T∈P,T.card := Finset.sum_congr rfl (fun T ht=>(legal T ht).1.symm)
      _ = Fintype.card V := hsum.symm
  have shape : P.biUnion (fun T=>T∩W)=W := by
    change P.biUnion (fun T=>id T∩W)=W
    rw [←Finset.biUnion_inter P id W,cover]
    simp
  have sum : W.card = ∑ T∈P,(T∩W).card := by
    calc
      W.card = (P.biUnion (fun T=>T∩W)).card := congrArg Finset.card shape.symm
      _ = ∑ T∈P,(T∩W).card := by
        apply Finset.card_biUnion
        intro A hA B hB ne
        exact (apart A hA B hB ne).mono Finset.inter_subset_left Finset.inter_subset_left
  have bound : W.card ≤ 2*P.card := by
    rw [sum]
    calc
      (∑ T∈P,(T∩W).card) ≤ ∑ _T∈P,(2:ℕ) := Finset.sum_le_sum
        (fun T ht=>tile_bound thin (legal T ht))
      _ = 2*P.card := by simp [Nat.mul_comm]
  omega

end KelmansCactus.AtomicBridge.RemoteMixedDissociation

namespace KelmansCactus.AtomicBridge.DiagonalResidueLock
open SimpleGraph Finset
open RemoteMixedDissociation (Sparse no_factor_if_sparse_large)
open SquareCap (HasFactor)

abbrev V := Fin 21
def edges : List (V×V) :=
  [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),
   (9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(16,17),(17,0),
   (0,4),(3,17),(6,18),(18,12),(9,19),(19,20),(20,15)]

def Adj (x y : V) : Prop := (x,y)∈edges ∨ (y,x)∈edges
instance (x y : V) : Decidable (Adj x y) := by unfold Adj; infer_instance
def board : SimpleGraph V where
  Adj := Adj
  symm := by intro x y e; exact e.symm
  loopless := by
    have h : ∀ x : V, ¬Adj x x := by decide
    exact h
instance : DecidableRel board.Adj := fun _ _=>inferInstanceAs (Decidable (Adj _ _))

def sparse : Finset V := {1,2,4,5,7,8,10,11,13,14,16,17,18,19,20}
theorem sparse_card : sparse.card=15 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sparse_max_one : Sparse board sparse := by
  change ∀ c∈sparse, ∀ x∈sparse, ∀ y∈sparse, Adj c x → Adj c y → x=y
  decide

theorem no_factor : ¬HasFactor board :=
  no_factor_if_sparse_large sparse_max_one (by decide)

def firstDiagonal : List V := [0,1,2,3]
def secondDiagonal : List V := [4,5,6,7,8,9,10,11,12,13,14,15,16,17]

theorem diagonal_and_ears_geometry :
    firstDiagonal.Nodup ∧ secondDiagonal.Nodup ∧
    firstDiagonal.Chain' board.Adj ∧ secondDiagonal.Chain' board.Adj ∧
    Disjoint firstDiagonal.toFinset secondDiagonal.toFinset ∧
    board.Adj 0 4 ∧ board.Adj 4 3 ∧ board.Adj 3 17 ∧ board.Adj 17 0 ∧
    board.Adj 6 18 ∧ board.Adj 18 12 ∧
    board.Adj 9 19 ∧ board.Adj 19 20 ∧ board.Adj 20 15 := by decide

#print axioms KelmansCactus.AtomicBridge.RemoteMixedDissociation.no_factor_if_sparse_large
#print axioms no_factor
end KelmansCactus.AtomicBridge.DiagonalResidueLock
