import OddUncross
import FourRingCyclicGeometry

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.OddUncross
open FourRingCutAux
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] [DecidableRel G.Adj] in
private theorem acyclic_two_vertices (c : V→Bool) (h : Fintype.card (Shore c)≤2) :
    (shoreGraph G c).IsAcyclic := by
  intro a w cyc
  have atLeast := cyc.three_le_length
  let f : Fin w.length→Shore c := fun i=>w.getVert i.val
  have inj : Function.Injective f := by
    intro i j same
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    exact cyc.getVert_injOn' (show i.val≤w.length-1 by omega)
      (show j.val≤w.length-1 by omega) same
  have b := Fintype.card_le_of_injective f inj
  rw [Fintype.card_fin] at b
  omega

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem colour_constant_walk {D : Finset V} (c : V→Bool)
    (same : ∀ {x y},x∉D→y∉D→G.Adj x y → c x=c y)
    {u v : {v : V // v∉D}} (w : (G.induce {x | x∉D}).Walk u v) :
    c u.val=c v.val := by
  induction w with
  | nil=>rfl
  | @cons a b z e rest ih => exact (same a.property b.property e).trans ih

/-- A cubic, 3-vertex-connected simple graph has global minimum
proper boundary at least three. Delete the true endpoints of a
hypothetical ≤2 cut; a whole small shore is handled by cubicity. -/
theorem min_boundary_three_of_three_connected (cub : ∀x,G.degree x=3)
    (conn : KelmansStarter.ThreeConnected G) : MinBoundaryThree G := by
  classical
  intro c ⟨x,xt⟩ ⟨y,yf⟩
  refine Classical.byContradiction ?_
  intro no
  have low : (boundary G c).card≤2 := by omega
  let D := (boundary G c).image Prod.fst
  have ds : D.card≤2 := (card_image_le : D.card≤(boundary G c).card).trans low
  have on (v : V) (vd : v∈D) : c v=true := by
    obtain ⟨p,mp,eq⟩ := mem_image.mp vd
    exact eq ▸ (mem_boundary.mp mp).1
  have yn : y∉D := fun h=>Bool.false_ne_true (yf.symm.trans (on _ h))
  have hconst {v w : V} (vn : v∉D) (wn : w∉D) (e : G.Adj v w) : c v=c w := by
    cases vc : c v <;> cases wc : c w
    · rfl
    · exact (wn (mem_image.mpr ⟨(w,v),mem_boundary.mpr ⟨wc,vc,e.symm⟩,rfl⟩)).elim
    · exact (vn (mem_image.mpr ⟨(v,w),mem_boundary.mpr ⟨vc,wc,e⟩,rfl⟩)).elim
    · rfl
  have sub (v : V) (vt : c v=true) : v∈D := by
    by_contra vn
    obtain ⟨w⟩ := (conn.2 D ds).preconnected (⟨v,vn⟩ : {z : V // z∉D}) ⟨y,yn⟩
    have r : c v=c y := colour_constant_walk G c hconst w
    exact Bool.false_ne_true (yf.symm.trans (r.symm.trans vt))
  by_cases single : ∀v,c v=true →v=x
  · have eq := singleton_boundary G c x xt single
    rw [cub] at eq
    omega
  · push_neg at single
    obtain ⟨z,zt,neq⟩ := single
    let f : Shore c→↥D := fun v=>⟨v.val,sub v.val v.property⟩
    have inj : Function.Injective f := fun a b e=>Subtype.ext (congrArg (fun v : ↥D=>v.val) e)
    have card := Fintype.card_le_of_injective f inj
    rw [Fintype.card_coe] at card
    have ac := acyclic_two_vertices G c (card.trans ds)
    have impossible := acyclic_shore_large_cut G c cub ac zt xt neq
    omega

#print axioms min_boundary_three_of_three_connected
end
end KelmansCactus.AtomicBridge.OddUncross
