import Z5JunctionGap
import FourRingThreeConnected
import Mathlib.Tactic.FinCases

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.Z5JunctionGap
open KelmansCactus.FourRingCutAux
abbrev X := Fin 10

private def petEdges : Finset (X × X) := rawEdges.toFinset

private theorem reflected_adj :
    ∀ u v : X, H.Adj u v ↔ (u,v)∈petEdges ∨ (v,u)∈petEdges := by decide

private def cbound (c : X → Bool) : Finset (X × X) :=
  (petEdges.filter (fun e=>c e.1≠c e.2)).image (fun e=>orientation c e.1 e.2)

private theorem observe_bound (c : X → Bool) : boundary H c = cbound c := by
  ext z
  obtain ⟨u,v⟩ := z
  constructor
  · intro h
    obtain ⟨bu,bv,ed⟩ := mem_boundary.mp h
    rcases (reflected_adj u v).mp ed with lo|hi
    · exact mem_image.mpr ⟨(u,v),mem_filter.mpr ⟨lo,by simp [bu,bv]⟩,by simp [orientation,bu]⟩
    · exact mem_image.mpr ⟨(v,u),mem_filter.mpr ⟨hi,by simp [bu,bv]⟩,by simp [orientation,bv]⟩
  · intro h
    obtain ⟨⟨x,y⟩,hp,eq⟩ := mem_image.mp h
    obtain ⟨xy,ne⟩ := mem_filter.mp hp
    have ed : H.Adj x y := (reflected_adj x y).mpr (Or.inl xy)
    exact eq ▸ active_edge ne ed

private def colour (c : X → Bool) (b : Bool) : Finset X :=
  univ.filter (fun x=> c x = b)

private def crosses (c : X → Bool) (e : X×X) : Bool := c e.1 != c e.2

private theorem boundary_count (c : X → Bool) :
    (cbound c).card = (rawEdges.filter (crosses c)).length := by
  classical
  have ordered : ∀ e ∈ petEdges,e.1 < e.2 := by decide
  have inj : Set.InjOn (fun e : X×X=>orientation c e.1 e.2)
      (↑(petEdges.filter (fun e=>c e.1≠c e.2)) : Set (X×X)) := by
    intro p hp q hq he
    change orientation c p.1 p.2 = orientation c q.1 q.2 at he
    have pl := ordered p (mem_filter.mp hp).1
    have ql := ordered q (mem_filter.mp hq).1
    have swapn (hh : p = q.swap) : False := by
      rw [hh] at pl
      exact (not_lt_of_ge (le_of_lt ql)) pl
    rcases orientation_cases (c:=c) (x:=p.1) (y:=p.2) with h1|h1 <;>
      rcases orientation_cases (c:=c) (x:=q.1) (y:=q.2) with h2|h2 <;>
      rw [h1,h2] at he
    · exact he
    · exact (swapn he).elim
    · exact (swapn (by simpa only [Prod.swap_swap] using congrArg Prod.swap he)).elim
    · simpa only [Prod.swap_swap] using congrArg Prod.swap he
  rw [cbound,card_image_of_injOn inj]
  have eq : petEdges.filter (fun e=>c e.1≠c e.2) = (rawEdges.filter (crosses c)).toFinset := by
    ext x
    simp [petEdges,crosses,and_comm]
  rw [eq]
  exact List.toFinset_card_of_nodup ((by decide : rawEdges.Nodup).filter _)

private theorem colour_count (c : X → Bool) (b : Bool) :
    (colour c b).card = ((List.finRange 10).filter (fun v=>c v == b)).length := by
  have eq : colour c b = ((List.finRange 10).filter (fun v=>c v == b)).toFinset := by
    ext x
    simp [colour]
  rw [eq]
  exact List.toFinset_card_of_nodup ((by decide : (List.finRange 10).Nodup).filter _)

private def boundTest (c : X → Bool) : Prop :=
  (rawEdges.filter (crosses c)).length ≤ 3 →
    ((List.finRange 10).filter (fun v=>c v == true)).length ≤ 1 ∨
    ((List.finRange 10).filter (fun v=>c v == false)).length ≤ 1

private instance (c : X → Bool) : Decidable (boundTest c) := by
  unfold boundTest
  infer_instance

private abbrev Back := Bool × Bool × Bool × Bool × Bool

private def paint (a b c d e : Bool) (r : Back) (x : X) : Bool :=
  if x=0 then a else if x=1 then b else if x=2 then c else if x=3 then d
  else if x=4 then e else if x=5 then r.1 else if x=6 then r.2.1
  else if x=7 then r.2.2.1 else if x=8 then r.2.2.2.1 else r.2.2.2.2

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 1250 in
private theorem cut_tests (a b c d e : Bool) :
    ∀ r : Back, boundTest (paint a b c d e r) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide

private theorem all_cut_tests (c : X → Bool) : boundTest c := by
  let r : Back := (c 5,c 6,c 7,c 8,c 9)
  have h : paint (c 0) (c 1) (c 2) (c 3) (c 4) r = c := by
    funext v
    fin_cases v <;> rfl
  rw [← h]
  exact cut_tests _ _ _ _ _ r

theorem no_small_nontrivial : SmallTrivial H := by
  intro c hc
  rw [observe_bound] at hc
  have small (b : Bool) (h : (colour c b).card ≤ 1) :
      ∀ x y, c x = b → c y = b → x=y := by
    intro x y hx hy
    exact (card_le_one.mp h x (by simp [colour,hx]) y (by simp [colour,hy]))
  rw [boundary_count] at hc
  have h := all_cut_tests c hc
  rw [← colour_count, ← colour_count] at h
  exact h.imp (small true) (small false)

theorem three_connected : KelmansStarter.ThreeConnected H :=
  three_connected_of_small_trivial H cubic (by decide) no_small_nontrivial

#print axioms no_small_nontrivial
#print axioms three_connected
end KelmansCactus.AtomicBridge.Z5JunctionGap
