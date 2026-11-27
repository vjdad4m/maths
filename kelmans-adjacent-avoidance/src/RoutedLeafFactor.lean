import RoutedLeafSupport
import RoutedFourRingSmallCuts
import RoutedLeafArithmetic
import HandleFactor

open Finset SimpleGraph
open scoped BigOperators
namespace KelmansCactus.AtomicBridge
open ThreePort Substitute PathSlides NearPerfectCells FourRingBudget FourRingReplica
open FourRingReplica.Layout FourRingCap ActiveCaps FourRingPropagation
open FourRingCutAux FourRingCyclicEquivalence HandleExtension
noncomputable section
universe u

/-- A factor of the mirrored six-cell ring missing two marked independent
rails forces a prescribed leaf on the original cap. -/
theorem cyclic4_factor_avoids_adjacent_layout
    (promise : CyclicUniversal.{u})
    {U : Type u} [Fintype U] [DecidableEq U] {A : SimpleGraph U} [DecidableRel A.Adj]
    (dom : CyclicDomain A) {r : Bool→U} (L : Layout A r) (blocked : Bool) :
    KelmansStarter.HasP3Factor (avoidAt A (r false) (r true) (L.port (false,blocked)).val) := by
  classical
  let ring : Circular sixNext := spin_circular (by decide : 2≤6)
  let H := L.routedGraph sixNext leafReverse ring.fixed
  have cub := L.routedCubic sixNext leafReverse ring.fixed dom.1.1
  have small := L.routedPreservesSmall sixNext leafReverse ring dom.1.1 dom.2
  have cardH : Fintype.card (Host (Fin 6) r)=6*(Fintype.card U-2) := by
    rw [L.host_card,Fintype.card_fin]
  have bigU := dom.1.2.1.1
  have rootR : Fintype.card U%3=0 := by
    obtain ⟨x,ex⟩ := dom.1.2.2
    omega
  have sh : 4≤Fintype.card (Host (Fin 6) r) := by omega
  have domH : CyclicDomain H := ⟨⟨cub,three_connected_of_small_trivial H cub sh small,
    ⟨Fintype.card U-2,cardH⟩⟩,small⟩
  let idx : Bool→Fin 6 := fun b=>if b then 2 else 0
  let E : Edges H := {
    a := fun b=>L.routedStart leafReverse (idx b,blocked)
    b := fun b=>L.routedEnd sixNext leafReverse (idx b,blocked)
    edge := fun b=>L.routedSeam_edge sixNext leafReverse _ _
    separated := by
      intro s t x hs ht
      have sMem : x.1=idx s ∨ x.1=sixNext (idx s) :=
        hs.imp (congrArg Prod.fst) (congrArg Prod.fst)
      have tMem : x.1=idx t ∨ x.1=sixNext (idx t) :=
        ht.imp (congrArg Prod.fst) (congrArg Prod.fst)
      have n01 : sixNext 0=1 := by decide
      have n23 : sixNext 2=3 := by decide
      cases s <;> cases t
      · rfl
      · change x.1=0 ∨ x.1=sixNext 0 at sMem
        change x.1=2 ∨ x.1=sixNext 2 at tMem
        rw [n01] at sMem
        rw [n23] at tMem
        have bad : ∀ i : Fin 6, (i=0 ∨ i=1) → (i=2 ∨ i=3) → False := by decide
        exact (bad _ sMem tMem).elim
      · change x.1=2 ∨ x.1=sixNext 2 at sMem
        change x.1=0 ∨ x.1=sixNext 0 at tMem
        rw [n23] at sMem
        rw [n01] at tMem
        have bad : ∀ i : Fin 6, (i=0 ∨ i=1) → (i=2 ∨ i=3) → False := by decide
        exact (bad _ tMem sMem).elim
      · rfl
  }
  obtain ⟨P,tiles,disj,cover⟩ := factor_avoids_two_disjoint promise domH E
  have mono {x y : Host (Fin 6) r} (h : E.deleteChosen.Adj x y) : H.Adj x y := h.1
  have pack : PackIn H univ P := ⟨⟨fun t ht=>by
    obtain ⟨card,c,mc,star⟩ := tiles t ht
    exact ⟨card,c,mc,fun y my ne=>mono (star y my ne)⟩,disj,rfl⟩,subset_univ _⟩
  let seam (i : Fin 6) := L.routedCellSeam sixNext leafReverse ring.fixed i
  let phys (i : Fin 6) (s : Slot) := width P (cell i) (L.p i s) (L.routedQ sixNext leafReverse i s)
  let log (i : Fin 6) (s : Slot) := phys i (swapSlot (leafReverse i) s)
  have sig (i : Fin 6) : Signature (G:=H) (cell i) (L.p i) (phys i) :=
    signature_of_covered_cell pack (cover.symm ▸ subset_univ _) (seam i)
  have bd (i : Fin 6) (s : Slot) : log i s≤2 :=
    width_le_two pack ((seam i).right _)
  have localResidue (i : Fin 6) : (∑ s : Slot,log i s)%3=1 := by
    have physR := width_congruence (sig i)
    have card := L.cell_card (J:=Fin 6) i
    rw [card] at physR
    have ss : (∑ s : Slot,log i s)=(∑ s : Slot,phys i s) := by
      rw [profile_sum,profile_sum]
      exact left_right_swap (phys i) (leafReverse i)
    rw [ss,physR]
    omega
  have flips (i : Fin 6) (k : Bool) :
      L.p (sixNext i) (swapSlot (leafReverse (sixNext i)) (false,k)) =
        L.routedQ sixNext leafReverse i (swapSlot (leafReverse i) (true,k)) ∧
      L.routedQ sixNext leafReverse (sixNext i) (swapSlot (leafReverse (sixNext i)) (false,k)) =
        L.p i (swapSlot (leafReverse i) (true,k)) := by
    refine ⟨(L.routedQ_start sixNext leafReverse i k).symm,?_⟩
    simp [routedQ,routedMate,swapAt,mate]
  have compatible (i : Fin 6) (k : Bool) : Opposite (log i (true,k)) (log (sixNext i) (false,k)) :=
    opposite_at_shared_seam pack (seam i) (seam (sixNext i))
      (cellDisjoint (r:=r) (mem_univ i) (mem_univ (sixNext i)) (ring.fixed i).symm)
      _ _ (flips i k).1 (flips i k).2
  have marked (b : Bool) : log (idx b) (true,blocked)=0 := by
    have omitE : ¬E.deleteChosen.Adj (E.a b) (E.b b) :=
      fun h=>h.2 ⟨b,Or.inl ⟨rfl,rfl⟩⟩
    let i := idx b
    let k := swapSlot (leafReverse i) (true,blocked)
    let k' := swapSlot (leafReverse (sixNext i)) (false,blocked)
    have forbidden : ¬E.deleteChosen.Adj (L.p i k) (L.routedQ sixNext leafReverse i k) := by
      rw [show L.routedQ sixNext leafReverse i k=L.routedEnd sixNext leafReverse (i,blocked)
        from L.routedQ_start sixNext leafReverse i blocked]
      exact omitE
    have nonuse := no_tile_at_omitted_seam (seam i) (seam (sixNext i))
      (cellDisjoint (r:=r) (mem_univ i) (mem_univ (sixNext i)) (ring.fixed i).symm)
      k k' (flips i blocked).1 (flips i blocked).2 mono forbidden tiles
    change width P (cell i) (L.p i k) (L.routedQ sixNext leafReverse i k)=0
    simp [width,tileAt_of_no_use nonuse]
  obtain ⟨i,ll,rr,off⟩ := forced_balanced_leaf log blocked bd localResidue compatible (marked false) (marked true)
  have no : phys i (false,blocked)=0 := by
    change phys i (swapSlot (leafReverse i) (swapSlot (leafReverse i) (false,blocked)))=0 at off
    simpa only [swapSlot_twice] using off
  have balances : left (phys i)=2 ∧ right (phys i)=2 := by
    change left (fun s=>phys i (swapSlot (leafReverse i) s))=2 at ll
    change right (fun s=>phys i (swapSlot (leafReverse i) s))=2 at rr
    cases h : leafReverse i
    · exact ⟨by simpa only [h] using ll,by simpa only [h] using rr⟩
    · exact ⟨by simpa only [h] using rr,by simpa only [h] using ll⟩
  exact cap_balanced_with_missing_slot L blocked sixNext leafReverse ring.fixed (sig i)
    balances.1 balances.2 no

/-- Plain cyclic-four Kelmans implies avoidance of any two specified
incident edges, in the same cyclic-four cubic order-zero class. -/
theorem cyclic4_factor_avoids_adjacent
    (promise : CyclicUniversal.{u})
    {U : Type u} [Fintype U] [DecidableEq U] {A : SimpleGraph U} [DecidableRel A.Adj]
    (dom : CyclicDomain A) {a b c : U} (ab : A.Adj a b) (ac : A.Adj a c) (bc : b≠c) :
    KelmansStarter.HasP3Factor (avoidAt A a b c) := by
  let r : Bool→U := fun k=>if k then b else a
  have order : 4<Fintype.card U := by
    have low := dom.1.2.1.1
    obtain ⟨k,ek⟩ := dom.1.2.2
    omega
  have triangle := triangle_free_of_small_trivial A dom.1.1 order dom.2
  have free (x : U) (aX : A.Adj (r false) x) (bX : A.Adj (r true) x) : False :=
    triangle a b x ab bX aX.symm
  let lay := from_triangle_free_edge A r dom.1.1 ab free
  let v : Piece r := ⟨c,ac.ne.symm,bc.symm⟩
  obtain ⟨blocked,eq⟩ := lay.exactPort false v ac
  have fac := cyclic4_factor_avoids_adjacent_layout promise dom lay blocked
  have edgeEq : (lay.port (false,blocked)).val=c := congrArg Subtype.val eq
  simpa only [edgeEq] using fac

#print axioms cyclic4_factor_avoids_adjacent_layout
#print axioms cyclic4_factor_avoids_adjacent

end
end KelmansCactus.AtomicBridge
