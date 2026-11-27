import SegmentSplice
import WideGraphLift

namespace Graffiti199Depleted.WiderOmission

open SimpleGraph
open CompactOmission (SixTree six_tree_absurd)

structure FragmentRoute (n k : ℕ) where
  first : Fin (n+1)
  last : Fin (n+1)
  tokens : List (SegmentToken n k)

def FragmentRoute.Valid {n k : ℕ} (D : Seams n k) (e : Fin (n+1) → Fin (n+1) → Bool)
    (r : FragmentRoute n k) : Prop :=
  (r.tokens.flatMap (SegmentToken.labels D)).Perm (List.finRange (n+1)) ∧
  (r.tokens.filterMap SegmentToken.seam).Perm (List.finRange k) ∧
  r.tokens.head?.map (SegmentToken.start D) = some r.first ∧
  r.tokens.getLast?.map (SegmentToken.finish D) = some r.last ∧
  r.tokens.Chain' (fun u v => e (u.finish D) (v.start D) = true)

instance fragmentRouteDecidable {n k : ℕ} (D : Seams n k) (e : Fin (n+1) → Fin (n+1) → Bool)
    (r : FragmentRoute n k) : Decidable (r.Valid D e) := by
  unfold FragmentRoute.Valid
  infer_instance

variable {V : Type*} {G : SimpleGraph V}

structure RealizedRoute (G : SimpleGraph V) (s t z : V) (B : List V) where
  vertices : List V
  chain : vertices.Chain' G.Adj
  first : vertices.head? = some s
  last : vertices.getLast? = some t
  perm : vertices.Perm (z :: B)

theorem realize_fragments {n k : ℕ} {D : Seams n k} {I : Fin k → List V}
    {f : Fin (n+1) ↪ V} {e : Fin (n+1) → Fin (n+1) → Bool} {B : List V}
    (core : B.Perm (block f ++ (List.finRange k).flatMap I))
    (chart : ∀ i j, G.Adj (f i) (f j) ↔ e i j = true)
    (inside : ∀ i, (f (D i).1 :: I i ++ [f (D i).2]).Chain' G.Adj)
    {r : FragmentRoute n k} (h : r.Valid D e) :
    Nonempty (RealizedRoute G (f r.first) (f r.last) (f (Fin.last n)) B) := by
  obtain ⟨perm,used,ph,pt,ch⟩ := h
  let C := r.tokens.flatMap (SegmentToken.expand D I f)
  have hd : C.head? = some (f r.first) := by
    change (r.tokens.flatMap (SegmentToken.expand D I f)).head? = _
    rw [head_expand_route,ph]
    rfl
  have tl : C.getLast? = some (f r.last) := by
    change (r.tokens.flatMap (SegmentToken.expand D I f)).getLast? = _
    rw [last_expand_route,pt]
    rfl
  have per := expand_route_perm D I f r.tokens perm used
  have coreMap : (List.finRange (n+1)).map f = block f ++ [f (Fin.last n)] := by
    rw [List.finRange_succ_last]
    simp [block,Function.comp_def]
  have move : ((block f ++ [f (Fin.last n)]) ++ (List.finRange k).flatMap I).Perm
      (f (Fin.last n) :: (block f ++ (List.finRange k).flatMap I)) := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using
      (List.perm_middle (a := f (Fin.last n)) (l₁ := block f) (l₂ := (List.finRange k).flatMap I))
  rw [coreMap] at per
  exact ⟨⟨C,expand_route_chain chart inside ch,hd,tl,per.trans (move.trans (core.symm.cons _))⟩⟩

def SingleChecks {n : ℕ} (e : Fin (n+1) → Fin (n+1) → Bool) (mate : Fin (n+1))
    (P : List ℕ) : Prop :=
  ∀ row, touch row (Fin.last n) = false → touch row mate = false →
    (∃ T, SixTree (singleEdge e row) T) ∨ ∃ m ∈ P, ∀ i : Fin (n+1), touch row i = touch m i

theorem external_from_check [DecidableEq V] [DecidableRel G.Adj] [Fintype V] {n : ℕ}
    (budget : Catalogue.treeNumber G ≤ 5) {f : Fin (n+1) ↪ V} {mate : Fin (n+1)}
    {e : Fin (n+1) → Fin (n+1) → Bool} {P : List ℕ} (checks : SingleChecks e mate P) {v : V}
    (core : ∀ i j, G.Adj (f i) (f j) ↔ e i j = true) (outside : ∀ i, v ≠ f i)
    (offZ : ¬ G.Adj v (f (Fin.last n))) (offMate : ¬ G.Adj v (f mate)) :
    ∃ m ∈ P, ProfileAt G f v m := by
  let flags := fun i : Fin (n+1) => decide (G.Adj v (f i))
  let row := encode flags
  have atRow : ProfileAt G f v row := fun i => by
    unfold touch row
    rw [encode_bit flags i]
    simp [flags]
  have offz : touch row (Fin.last n) = false :=
    Bool.eq_false_iff.mpr (fun e => offZ ((atRow _).mpr e))
  have offm : touch row mate = false :=
    Bool.eq_false_iff.mpr (fun e => offMate ((atRow _).mpr e))
  rcases checks row offz offm with ⟨T,tree⟩|⟨m,ok,agree⟩
  · let x : Fin 1 ↪ V := ⟨fun _ => v,fun _ _ _ => Subsingleton.elim _ _⟩
    let g := extend f x (fun i _ => outside i)
    have chart : ∀ i j, G.Adj (g i) (g j) ↔ singleEdge e row i j = true :=
      extension_chart core (fun _ => atRow) (fun _ _ => by simp [x,singleLinks])
    exact (six_tree_absurd budget chart tree).elim
  · exact ⟨m,ok,fun i => (atRow i).trans (by rw [agree i])⟩

/-- Labels 0 and 1 are the old left and right vertices. Label 2 is
the next vertex to the left. The 0-2 edge belongs to the original path. -/
def fragmentStepLinks (old new : Bool) : Fin 3 → Fin 3 → Bool :=
  fun i j => (i != j) && (if i == 2 || j == 2 then
    (if i == 0 || j == 0 then true else new) else old)

def fragmentStepEdge {n : ℕ} (e : Fin (n+1) → Fin (n+1) → Bool)
    (left right m : ℕ) (old new : Bool) : Fin ((n+1)+3) → Fin ((n+1)+3) → Bool :=
  extension e (![left,right,m] : Fin 3 → ℕ) (fragmentStepLinks old new)

end Graffiti199Depleted.WiderOmission
