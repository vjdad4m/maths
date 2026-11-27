import RoutedFourRing
import RoutedActiveCaps
import RoutedNoCoTile

open Finset SimpleGraph
open scoped BigOperators
namespace KelmansCactus.AtomicBridge
open ThreePort Substitute PathSlides NearPerfectCells FourRingBudget FourRingReplica
open FourRingReplica.Layout FourRingCap ActiveCaps FourRingPropagation
open FourRingCutAux FourRingCyclicEquivalence
noncomputable section
universe u

/-- Delete the two designated incident edges, preserving all other edges. -/
def avoidAt {V : Type*} (G : SimpleGraph V) (a b c : V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ ¬((x=a ∧ (y=b ∨ y=c)) ∨ (y=a ∧ (x=b ∨ x=c)))
  symm := by
    intro x y h
    exact ⟨h.1.symm,fun a=>h.2 (a.elim Or.inr Or.inl)⟩
  loopless := fun x h=>G.loopless _ h.1

theorem left_right_swap (w : Slot→ℕ) (b : Bool) :
    left (fun s=>w (swapSlot b s))+right (fun s=>w (swapSlot b s))=left w+right w := by
  cases b
  · rfl
  · unfold left right
    change w (true,false)+w (true,true)+(w (false,false)+w (false,true))=_
    omega

/-- A balanced signature in the physical ports with one false-root
slot unused caps to a factor avoiding both unwanted edges at that root. -/
theorem cap_balanced_with_missing_slot
    {U : Type u} [Fintype U] [DecidableEq U] {A : SimpleGraph U} {r : Bool→U}
    (L : Layout A r) (blocked : Bool)
    {J : Type*} [Fintype J] [DecidableEq J] (next : Equiv.Perm J)
    (rev : J→Bool) (fixed : ∀i,next i≠i)
    {i : J} {w : Slot→ℕ}
    (sig : Signature (G:=L.routedGraph next rev fixed) (cell i) (L.p i) w)
    (bs0 : left w=2) (bs1 : right w=2) (no : w (false,blocked)=0) :
    KelmansStarter.HasP3Factor (avoidAt A (r false) (r true) (L.port (false,blocked)).val) := by
  classical
  let e := L.embedCap i (next i) (fixed i)
  let B := avoidAt A (r false) (r true) (L.port (false,blocked)).val
  let K : SimpleGraph (Host J r) := B.map e
  let root : Bool→Host J r := fun b=>e (r b)
  have cap : ActiveCap (G:=L.routedGraph next rev fixed) K (cell i) (L.p i) root w := by
    refine ⟨?_,fun h=>L.rootEdge.ne (e.injective h),?_,?_⟩
    · intro b m
      have eq := mem_cell.mp m
      cases b
      · exact fixed i (congrArg Prod.fst (L.embedCap_rootF (i:=i) (j:=next i) (ji:=fixed i)).symm |>.trans eq)
      · exact fixed i (congrArg Prod.fst (L.embedCap_rootT (i:=i) (j:=next i) (ji:=fixed i)).symm |>.trans eq)
    · rintro ⟨b,k⟩ pos
      have im : e (L.port (b,k)).val=L.p i (b,k) := L.embedCap_nonroot (L.port (b,k))
      change K.Adj (e (r b)) (L.p i (b,k))
      rw [←im]
      apply SimpleGraph.map_adj_apply.mpr
      refine ⟨L.conn (b,k),?_⟩
      rintro (⟨rr,h⟩|⟨portEq,_⟩)
      · cases b
        · rcases h with p|p
          · exact (L.port (false,k)).property.2 p
          · have same := L.port.injective (Subtype.ext p)
            have kb : k=blocked := congrArg Prod.snd same
            subst k
            omega
        · exact L.rootEdge.ne rr.symm
      · exact (L.port (b,k)).property.1 portEq
    · intro x xm y ym a
      have xx := mem_cell.mp xm
      have yy := mem_cell.mp ym
      have xIm : e x.2.val=x := (L.embedCap_nonroot x.2).trans (Prod.ext xx.symm rfl)
      have yIm : e y.2.val=y := (L.embedCap_nonroot y.2).trans (Prod.ext yy.symm rfl)
      have ed := (L.routedInternal next rev (xx.trans yy.symm)).mp a
      exact ⟨x.2.val,y.2.val,⟨ed,fun h=>h.elim (fun h=>x.2.property.1 h.1)
        (fun h=>y.2.property.1 h.1)⟩,xIm,yIm⟩
  have ready := export_balanced_active_caps cap sig bs0 bs1
  have image : insert (root false) (insert (root true) (cell i)) =
      (univ : Finset U).map e := by
    rw [L.cap_image i (next i) (fixed i)]
    change insert (e (r false)) (insert (e (r true))
      (((univ.erase (r false)).erase (r true)).map e))=_
    rw [←map_insert,←map_insert,insert_erase,insert_erase (mem_univ (r false))]
    exact mem_erase.mpr ⟨L.rootEdge.ne.symm,mem_univ _⟩
  rw [image] at ready
  exact FourReplace.full_factor_of_closed_image e
    (fun _ _ a=>SimpleGraph.map_adj_apply.mp a) ready



end
end KelmansCactus.AtomicBridge
