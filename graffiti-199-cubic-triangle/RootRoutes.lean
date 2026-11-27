import TrianglePlacement
import FullMaskCover

open private all_known from FullMaskCover

namespace Graffiti199Depleted.WiderOmission

open SimpleGraph
open CompactOmission (SixTree six_tree_absurd)

def RootRouteCheck {n k : ℕ} (D : Seams n k) (d : Family n)
    (routes : List (List (SegmentToken n k))) (exceptional : List ℕ)
    (dom value tag : ℕ) : Prop :=
  if h : tag < routes.length then
    let p := routes.get ⟨tag,h⟩
    SegmentRoute D (d.pattern.edge value) p ∧
      p.Chain' (fun u v => d.pattern.known dom (u.finish D) (v.start D) = true)
  else tag - routes.length ∈ exceptional ∧ value = tag - routes.length ∧
    dom = 2 ^ d.choices.length - 1

instance rootRouteCheckDecidable {n k : ℕ} (D : Seams n k) (d : Family n)
    (routes : List (List (SegmentToken n k))) (exceptional : List ℕ) (dom value tag : ℕ) :
    Decidable (RootRouteCheck D d routes exceptional dom value tag) := by
  if h : tag < routes.length then
    let p := routes.get ⟨tag,h⟩
    exact decidable_of_iff
      (SegmentRoute D (d.pattern.edge value) p ∧
        p.Chain' (fun u v => d.pattern.known dom (u.finish D) (v.start D) = true))
      (by simp only [RootRouteCheck,dif_pos h,p])
  else
    exact decidable_of_iff
      (tag - routes.length ∈ exceptional ∧ value = tag - routes.length ∧
        dom = 2 ^ d.choices.length - 1)
      (by simp only [RootRouteCheck,dif_neg h])

private theorem transfer_chain {n k : ℕ} (D : Seams n k) (d : Family n)
    {row dom value : ℕ} (agree : Agree row dom value) (P : List (SegmentToken n k))
    (edges : P.Chain' (fun u v => d.pattern.edge value (u.finish D) (v.start D) = true))
    (known : P.Chain' (fun u v => d.pattern.known dom (u.finish D) (v.start D) = true)) :
    P.Chain' (fun u v => d.pattern.edge row (u.finish D) (v.start D) = true) := by
  induction P with
  | nil => simp
  | cons a tail ih =>
    cases tail with
    | nil => simp
    | cons b rest =>
      exact List.chain'_cons.mpr ⟨(edge_agree d.pattern agree known.rel_head).trans edges.rel_head,
        ih edges.tail known.tail⟩

theorem classified_by_root_routes {n k : ℕ} {D : Seams n k} {d : Family n}
    {routes : List (List (SegmentToken n k))} {exceptional : List ℕ} {C : Cover (n+1)}
    (valid : C.Valid d.pattern (RootRouteCheck D d routes exceptional) 0 0) (row : ℕ) :
    (∃ T, SixTree (d.pattern.edge row) T) ∨
      (∃ P, SegmentRoute D (d.pattern.edge row) P) ∨
      ∃ tag ∈ exceptional, ∀ i j, d.pattern.edge row i j = d.pattern.edge tag i j := by
  rcases Cover.start valid row with tree|⟨dom,value,tag,agree,checked⟩
  · exact Or.inl tree
  · by_cases range : tag < routes.length
    · simp only [RootRouteCheck,dif_pos range] at checked
      obtain ⟨⟨labels,seams,first,last,edges⟩,known⟩ := checked
      exact Or.inr (Or.inl ⟨_,labels,seams,first,last,transfer_chain D d agree _ edges known⟩)
    · simp only [RootRouteCheck,dif_neg range] at checked
      obtain ⟨mem,eq,hd⟩ := checked
      subst dom
      exact Or.inr (Or.inr ⟨_,mem,fun i j => (edge_agree d.pattern agree (all_known d i j)).trans
        (congrArg (fun v => d.pattern.edge v i j) eq)⟩)

variable {V : Type*} {G : SimpleGraph V} [DecidableEq V] [DecidableRel G.Adj] [Fintype V]

theorem resolve_triangle_routed {n k : ℕ} {D : Seams n k} (b : Layout n) (m : Fin 3) {skipped : List ℕ}
    (d : Family n) (fixed : TriangleConsistent b skipped m d) (good : List ℕ)
    (classify : ∀ row, (∃ T, SixTree (d.pattern.edge row) T) ∨
      (∃ P, SegmentRoute D (d.pattern.edge row) P) ∨
      ∃ tag ∈ good, ∀ i j, d.pattern.edge row i j = d.pattern.edge tag i j)
    (budget : Catalogue.treeNumber G ≤ 5) {f : Fin (n+1) ↪ V}
    (p : PathOn G {v | v ≠ f (Fin.last n)})
    (real : ∀ i j : Fin (n+1), i.val+1=j.val → j.val<n → i.val∉skipped → G.Adj (f i) (f j))
    (around : ∀ i, ∃ L R : List V, p.vertices = L ++ f (b.prev i) :: f (b.port i) :: f (b.next i) :: R)
    (za : ∀ i, G.Adj (f (Fin.last n)) (f (b.port i)))
    (triangle : ∀ i j, i ≠ j → i ≠ m → j ≠ m → G.Adj (f (b.port i)) (f (b.port j)))
    (dz : G.degree (f (Fin.last n)) = 3) (dm : G.degree (f (b.port m)) = 3)
    (splice : ∀ row P, (∀ i j, G.Adj (f i) (f j) ↔ d.pattern.edge row i j = true) →
      SegmentRoute D (d.pattern.edge row) P → Catalogue.Traceable G)
    (close : ∀ tag ∈ good, (∀ i j, G.Adj (f i) (f j) ↔ d.pattern.edge tag i j = true) →
      Catalogue.Traceable G) : Catalogue.Traceable G := by
  classical
  by_contra noTrace
  have must (i j) (h : TriangleMust b m skipped i j) : G.Adj (f i) (f j) := by
    rcases h with (⟨step,lt,off⟩|⟨rfl,jp⟩)|⟨s,t,st,sm,tm,rfl,rfl⟩
    · exact real _ _ step lt off
    · obtain ⟨k,rfl⟩ := List.mem_ofFn.mp jp
      exact za k
    · exact triangle s t st sm tm
  obtain ⟨row,hrow⟩ := triangle_row fixed must (triangle_off b m p noTrace around za dz dm)
  rcases classify row with ⟨T,hT⟩|⟨P,hP⟩|⟨tag,ok,eq⟩
  · exact six_tree_absurd budget hrow hT
  · exact noTrace (splice row P hrow hP)
  · exact noTrace (close tag ok (fun i j => (hrow i j).trans (by rw [eq i j])))

end Graffiti199Depleted.WiderOmission
