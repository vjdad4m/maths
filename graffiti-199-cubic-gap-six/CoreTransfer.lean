import FiniteLayout
import WideFlankPropagation

open private pred_mem succ_mem from CompactOmission
open private three_names_exhaust_neighbors from DepletedFootprint

namespace Graffiti199Depleted.WiderOmission

open SimpleGraph
open CompactOmission (six_tree_absurd chain_from_chart trace_of_middle_replacement)

def CoreRoute {n : ℕ} (e : Fin (n+1) → Fin (n+1) → Bool) (P : List (Fin (n+1))) : Prop :=
  P.Perm (List.finRange (n+1)) ∧ P.head? = some 0 ∧ P.getLast? = some (rightEnd n) ∧
    P.Chain' (fun i j => e i j = true)

instance {n : ℕ} (e : Fin (n+1) → Fin (n+1) → Bool) (P : List (Fin (n+1))) :
    Decidable (CoreRoute e P) := by unfold CoreRoute; infer_instance

variable {V : Type*} {G : SimpleGraph V} [DecidableEq V] [DecidableRel G.Adj] [Fintype V]

omit [DecidableRel G.Adj] [Fintype V] in
theorem traceable_of_core_route {n : ℕ} (pos : 0 < n)
    {f : Fin (n+1) ↪ V} {e : Fin (n+1) → Fin (n+1) → Bool}
    (p : PathOn G {v | v ≠ f (Fin.last n)}) {L R : List V} (split : p.vertices = L ++ block f ++ R)
    (chart : ∀ i j, G.Adj (f i) (f j) ↔ e i j = true)
    {P : List (Fin (n+1))} (route : CoreRoute e P) : Catalogue.Traceable G := by
  obtain ⟨perm,ph,pt,ch⟩ := route
  have head := block_head f pos
  have tail := block_last f pos
  have ne : block f ≠ [] := by
    intro nil
    rw [nil] at head
    cases head
  have neP : P.map f ≠ [] := by
    intro nil
    cases P <;> simp_all
  have sameHead : (P.map f).head? = (block f).head? := by rw [List.head?_map,ph,head]; rfl
  have sameTail : (P.map f).getLast? = (block f).getLast? := by rw [List.getLast?_map,pt,tail]; rfl
  exact trace_of_middle_replacement p split ne neP sameHead sameTail (block_perm f perm)
    (chain_from_chart chart ch)

omit [DecidableEq V] in
private theorem exterior_off_of_three {n : ℕ} {f : Fin (n+1) ↪ V} {v : V}
    (outside : ∀ i, v ≠ f i) {u a b c : Fin (n+1)}
    (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c)
    (degree : G.degree (f u) = 3)
    (ha : G.Adj (f u) (f a)) (hb : G.Adj (f u) (f b)) (hc : G.Adj (f u) (f c)) :
    ¬ G.Adj v (f u) := by
  intro e
  obtain ⟨i,_,eq⟩ := three_names_exhaust_neighbors f ab ac bc degree ha hb hc v e.symm
  exact outside _ eq.symm

/-- Complete lifting from the finite core and attachment certificates. -/
theorem traceable_of_layout_classified {n : ℕ} (b : Layout n) (m : Fin 3)
    {f : Fin (n+1) ↪ V} (d : Family n) (fixed : Consistent b m d)
    (tags : List ℕ)
    (coverage : ∀ row, (∃ T, CompactOmission.SixTree (d.pattern.edge row) T) ∨
      ∃ tag ∈ tags, ∀ i j, d.pattern.edge row i j = d.pattern.edge tag i j)
    (finish : ∀ k ∈ tags, (∃ P, CoreRoute (d.pattern.edge k) P) ∨
      Nonempty (FlankRules n (d.pattern.edge k) (b.port m)))
    (left : b.prev 0 = 0) (right : b.next 2 = rightEnd n)
    (budget : Catalogue.treeNumber G ≤ 5)
    (p : PathOn G {v | v ≠ f (Fin.last n)}) {L R : List V} (split : p.vertices = L ++ block f ++ R)
    (za : ∀ i, G.Adj (f (Fin.last n)) (f (b.port i)))
    (ind : ∀ i j, ¬ G.Adj (f (b.port i)) (f (b.port j)))
    (dz : G.degree (f (Fin.last n)) = 3) (dm : G.degree (f (b.port m)) = 3) :
    Catalogue.Traceable G := by
  classical
  by_contra noTrace
  have live := placement b m p split noTrace za ind dz dm
  obtain ⟨row,hrow⟩ := actual_row live fixed
  rcases coverage row with ⟨T,tree⟩|⟨tag,tagOk,eq⟩
  · exact six_tree_absurd budget hrow tree
  · have htag (i j) : G.Adj (f i) (f j) ↔ d.pattern.edge tag i j = true :=
      (hrow i j).trans (by rw [eq i j])
    have pos : 0 < n := by have h := b.interior 0; omega
    rcases finish tag tagOk with hRoute|hRules
    · obtain ⟨P,hP⟩ := hRoute
      exact noTrace (traceable_of_core_route pos p split htag hP)
    · obtain ⟨rules⟩ := hRules
      have step (i : Fin 3) : (b.prev i).val + 1 = (b.port i).val := by
        have it := (b.interior i).1
        change (b.port i).val - 1 + 1 = _
        omega
      have lt (i : Fin 3) : (b.port i).val < n := by have h := b.interior i; omega
      have preP : f 0 ∈ p.predecessors := by
        rw [← left]
        exact pred_mem (split_block_edge p split (step 0) (lt 0)) (za 0)
      have sucQ : f (rightEnd n) ∈ p.rev.predecessors := by
        rw [← right]
        exact succ_mem (split_block_edge p split rfl (b.interior 2).2) (za 2)
      have exterior (v : V) (out : ∀ i, v ≠ f i) :
          ¬ G.Adj v (f (Fin.last n)) ∧ ¬ G.Adj v (f (b.port m)) := by
        constructor
        · exact exterior_off_of_three out (b.port.injective.ne (by decide : (0 : Fin 3) ≠ 1))
            (b.port.injective.ne (by decide : (0 : Fin 3) ≠ 2))
            (b.port.injective.ne (by decide : (1 : Fin 3) ≠ 2)) dz (za 0) (za 1) (za 2)
        · have hi := b.interior m
          have ql : Fin.last n ≠ b.prev m := by
            intro e
            have el := congrArg Fin.val e
            change n = (b.port m).val - 1 at el
            omega
          have qr : Fin.last n ≠ b.next m := by
            intro e
            have er := congrArg Fin.val e
            change n = (b.port m).val + 1 at er
            omega
          have lr : b.prev m ≠ b.next m := by
            intro e
            have elr := congrArg Fin.val e
            change (b.port m).val - 1 = (b.port m).val + 1 at elr
            omega
          exact exterior_off_of_three out ql qr lr dm (za m).symm
            (live.consecutive _ _ (step m) (lt m)).symm
            (live.consecutive _ _ rfl (b.interior m).2)
      exact noTrace (traceable_of_flank_rules pos budget rules p htag exterior preP sucQ L R split)

theorem traceable_of_layout {n : ℕ} (b : Layout n) (m : Fin 3)
    {f : Fin (n+1) ↪ V} (d : Family n) (fixed : Consistent b m d)
    (tags : List ℕ) (C : Cover (n+1)) (coverage : C.Valid d.pattern (FullyKnown d tags) 0 0)
    (finish : ∀ k ∈ tags, (∃ P, CoreRoute (d.pattern.edge k) P) ∨
      Nonempty (FlankRules n (d.pattern.edge k) (b.port m)))
    (left : b.prev 0 = 0) (right : b.next 2 = rightEnd n)
    (budget : Catalogue.treeNumber G ≤ 5)
    (p : PathOn G {v | v ≠ f (Fin.last n)}) {L R : List V} (split : p.vertices = L ++ block f ++ R)
    (za : ∀ i, G.Adj (f (Fin.last n)) (f (b.port i)))
    (ind : ∀ i j, ¬ G.Adj (f (b.port i)) (f (b.port j)))
    (dz : G.degree (f (Fin.last n)) = 3) (dm : G.degree (f (b.port m)) = 3) :
    Catalogue.Traceable G :=
  traceable_of_layout_classified b m d fixed tags (classified coverage) finish left right
    budget p split za ind dz dm

#print axioms traceable_of_layout_classified
#print axioms traceable_of_layout

end Graffiti199Depleted.WiderOmission
