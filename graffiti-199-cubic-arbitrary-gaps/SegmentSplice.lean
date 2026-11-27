import CoreTransfer

namespace Graffiti199Depleted.WiderOmission

open SimpleGraph
open CompactOmission (trace_of_middle_replacement)

inductive SegmentToken (n k : ℕ)
  | vertex (i : Fin (n+1))
  | across (i : Fin k) (backward : Bool)

abbrev Seams (n k : ℕ) := Fin k → Fin (n+1) × Fin (n+1)

def SegmentToken.start {n k} (D : Seams n k) : SegmentToken n k → Fin (n+1)
  | .vertex i => i
  | .across i r => if r then (D i).2 else (D i).1

def SegmentToken.finish {n k} (D : Seams n k) : SegmentToken n k → Fin (n+1)
  | .vertex i => i
  | .across i r => if r then (D i).1 else (D i).2

def SegmentToken.labels {n k} (D : Seams n k) : SegmentToken n k → List (Fin (n+1))
  | .vertex i => [i]
  | .across i r => if r then [(D i).2,(D i).1] else [(D i).1,(D i).2]

def SegmentToken.seam {n k} : SegmentToken n k → Option (Fin k)
  | .vertex _ => none
  | .across i _ => some i

def SegmentRoute {n k} (D : Seams n k) (e : Fin (n+1) → Fin (n+1) → Bool)
    (P : List (SegmentToken n k)) : Prop :=
  (P.flatMap (SegmentToken.labels D)).Perm (List.finRange (n+1)) ∧
  (P.filterMap SegmentToken.seam).Perm (List.finRange k) ∧
  P.head?.map (SegmentToken.start D) = some 0 ∧
  P.getLast?.map (SegmentToken.finish D) = some (rightEnd n) ∧
  P.Chain' (fun u v => e (u.finish D) (v.start D) = true)

instance segmentRouteDecidable {n k} (D : Seams n k) (e : Fin (n+1) → Fin (n+1) → Bool)
    (P : List (SegmentToken n k)) : Decidable (SegmentRoute D e P) := by
  unfold SegmentRoute
  infer_instance

variable {V : Type*} {G : SimpleGraph V}

def SegmentToken.extra {n k} (I : Fin k → List V) : SegmentToken n k → List V
  | .vertex _ => []
  | .across i r => if r then (I i).reverse else I i

def SegmentToken.expand {n k} (D : Seams n k) (I : Fin k → List V)
    (f : Fin (n+1) ↪ V) : SegmentToken n k → List V
  | .vertex i => [f i]
  | .across i r =>
    if r then f (D i).2 :: (I i).reverse ++ [f (D i).1]
    else f (D i).1 :: I i ++ [f (D i).2]

theorem SegmentToken.expand_ne {n k} (D : Seams n k) (I : Fin k → List V)
    (f : Fin (n+1) ↪ V) (t : SegmentToken n k) : t.expand D I f ≠ [] := by
  cases t with
  | vertex => simp [SegmentToken.expand]
  | across i r => cases r <;> simp [SegmentToken.expand]

theorem SegmentToken.head_expand {n k} (D : Seams n k) (I : Fin k → List V)
    (f : Fin (n+1) ↪ V) (t : SegmentToken n k) :
    (t.expand D I f).head? = some (f (t.start D)) := by
  cases t with
  | vertex => rfl
  | across i r => cases r <;> rfl

theorem SegmentToken.last_expand {n k} (D : Seams n k) (I : Fin k → List V)
    (f : Fin (n+1) ↪ V) (t : SegmentToken n k) :
    (t.expand D I f).getLast? = some (f (t.finish D)) := by
  cases t with
  | vertex => rfl
  | across i r =>
    cases r <;> simp only [SegmentToken.expand,SegmentToken.finish,Bool.false_eq_true,
      if_false,if_true,← List.cons_append,List.getLast?_append,List.getLast?_singleton,Option.some_or]

theorem SegmentToken.expand_chain {n k} {D : Seams n k} {I : Fin k → List V}
    {f : Fin (n+1) ↪ V} (t : SegmentToken n k)
    (inside : ∀ i, (f (D i).1 :: I i ++ [f (D i).2]).Chain' G.Adj) :
    (t.expand D I f).Chain' G.Adj := by
  cases t with
  | vertex => simp [SegmentToken.expand]
  | across i r =>
    cases r
    · exact inside i
    · have rev := List.chain'_reverse.mpr
        ((inside i).imp (R := G.Adj) (S := flip G.Adj) (fun _ _ e => e.symm))
      simpa [SegmentToken.expand,List.reverse_append,List.reverse_cons,List.append_assoc] using rev

theorem SegmentToken.expand_perm {n k} (D : Seams n k) (I : Fin k → List V)
    (f : Fin (n+1) ↪ V) (t : SegmentToken n k) :
    (t.expand D I f).Perm ((t.labels D).map f ++ t.extra I) := by
  cases t with
  | vertex => simp [SegmentToken.expand,SegmentToken.labels,SegmentToken.extra]
  | across i r =>
    cases r
    · simpa only [SegmentToken.expand,SegmentToken.labels,SegmentToken.extra,Bool.false_eq_true,
        if_false,List.map_cons,List.map_nil,List.cons_append,List.nil_append,List.append_nil] using
        (List.perm_middle (a := f (D i).2) (l₁ := I i) (l₂ := [])).cons (f (D i).1)
    · simpa only [SegmentToken.expand,SegmentToken.labels,SegmentToken.extra,if_true,
        List.map_cons,List.map_nil,List.cons_append,List.nil_append,List.append_nil] using
        (List.perm_middle (a := f (D i).1) (l₁ := (I i).reverse) (l₂ := [])).cons (f (D i).2)

theorem head_expand_route {n k} (D : Seams n k) (I : Fin k → List V)
    (f : Fin (n+1) ↪ V) (P : List (SegmentToken n k)) :
    (P.flatMap (SegmentToken.expand D I f)).head? = (P.head?.map (SegmentToken.start D)).map f := by
  cases P with
  | nil => rfl
  | cons t R =>
    rw [List.flatMap_cons,List.head?_append_of_ne_nil _ (t.expand_ne D I f),t.head_expand D I f]
    rfl

theorem last_expand_route {n k} (D : Seams n k) (I : Fin k → List V)
    (f : Fin (n+1) ↪ V) (P : List (SegmentToken n k)) :
    (P.flatMap (SegmentToken.expand D I f)).getLast? = (P.getLast?.map (SegmentToken.finish D)).map f := by
  induction P using List.reverseRecOn with
  | nil => rfl
  | append_singleton P t ih =>
    rw [List.flatMap_append,List.flatMap_singleton,List.getLast?_append_of_ne_nil _ (t.expand_ne D I f),
      t.last_expand D I f,List.getLast?_append_of_ne_nil _ (by simp)]
    rfl

private theorem extras_perm {n k} (I : Fin k → List V) (P : List (SegmentToken n k)) :
    (P.flatMap (SegmentToken.extra I)).Perm ((P.filterMap SegmentToken.seam).flatMap I) := by
  induction P with
  | nil => rfl
  | cons t P ih =>
    cases t with
    | vertex => simpa [SegmentToken.extra,SegmentToken.seam] using ih
    | across i r =>
      cases r
      · simpa [SegmentToken.extra,SegmentToken.seam] using ih.append_left (I i)
      · simpa [SegmentToken.extra,SegmentToken.seam] using (List.reverse_perm _).append ih

theorem expand_route_perm {n k} (D : Seams n k) (I : Fin k → List V)
    (f : Fin (n+1) ↪ V) (P : List (SegmentToken n k))
    {A : List (Fin (n+1))} (perm : (P.flatMap (SegmentToken.labels D)).Perm A)
    (all : (P.filterMap SegmentToken.seam).Perm (List.finRange k)) :
    (P.flatMap (SegmentToken.expand D I f)).Perm (A.map f ++ (List.finRange k).flatMap I) := by
  have split : (P.flatMap (SegmentToken.expand D I f)).Perm
      ((P.flatMap (SegmentToken.labels D)).map f ++ P.flatMap (SegmentToken.extra I)) := by
    clear perm all A
    induction P with
    | nil => rfl
    | cons t P ih =>
      let a := (t.labels D).map f
      let b := t.extra I
      let c := (P.flatMap (SegmentToken.labels D)).map f
      let d := P.flatMap (SegmentToken.extra I)
      have move : (a ++ b ++ (c ++ d)).Perm ((a ++ c) ++ (b ++ d)) := by
        simpa only [List.append_assoc] using
          (((List.perm_append_comm (l₁ := b) (l₂ := c)).append_left a).append_right d)
      simpa only [List.flatMap_cons,List.map_append] using ((t.expand_perm D I f).append ih).trans move
  exact split.trans ((perm.map f).append ((extras_perm I P).trans (all.flatMap_right I)))

theorem expand_route_chain {n k} {D : Seams n k} {I : Fin k → List V} {f : Fin (n+1) ↪ V}
    {e : Fin (n+1) → Fin (n+1) → Bool}
    (chart : ∀ i j, G.Adj (f i) (f j) ↔ e i j = true)
    (inside : ∀ i, (f (D i).1 :: I i ++ [f (D i).2]).Chain' G.Adj)
    {P : List (SegmentToken n k)} (hc : P.Chain' (fun u v => e (u.finish D) (v.start D) = true)) :
    (P.flatMap (SegmentToken.expand D I f)).Chain' G.Adj := by
  change (P.map (SegmentToken.expand D I f)).flatten.Chain' G.Adj
  apply (List.chain'_flatten (by
    intro mem
    obtain ⟨t,_,eq⟩ := List.mem_map.mp mem
    exact t.expand_ne D I f eq)).mpr
  constructor
  · intro A mem
    obtain ⟨t,_,rfl⟩ := List.mem_map.mp mem
    exact t.expand_chain inside
  · rw [List.chain'_map]
    apply hc.imp
    intro u v uv x hx y hy
    rw [u.last_expand D I f] at hx
    rw [v.head_expand D I f] at hy
    have xx : f (u.finish D) = x := by simpa using hx
    have yy : f (v.start D) = y := by simpa using hy
    exact xx ▸ yy ▸ (chart _ _).mpr uv

/-- Replace a segment of a one-omission path by a certified route which
may traverse each designated subpath in either direction. -/
theorem traceable_of_segment_route [DecidableEq V] {n k} {D : Seams n k} {I : Fin k → List V}
    {f : Fin (n+1) ↪ V} {e : Fin (n+1) → Fin (n+1) → Bool}
    (p : PathOn G {x | x ≠ f (Fin.last n)}) {L B R : List V}
    (split : p.vertices = L ++ B ++ R)
    (corePerm : B.Perm (block f ++ (List.finRange k).flatMap I))
    (first : B.head? = some (f 0)) (last : B.getLast? = some (f (rightEnd n)))
    (chart : ∀ i j, G.Adj (f i) (f j) ↔ e i j = true)
    (inside : ∀ i, (f (D i).1 :: I i ++ [f (D i).2]).Chain' G.Adj)
    {P : List (SegmentToken n k)} (cert : SegmentRoute D e P) : Catalogue.Traceable G := by
  obtain ⟨perm,used,ph,pt,ch⟩ := cert
  let C := P.flatMap (SegmentToken.expand D I f)
  have headC : C.head? = B.head? := by
    change (P.flatMap (SegmentToken.expand D I f)).head? = _
    rw [head_expand_route,ph,first]
    rfl
  have tailC : C.getLast? = B.getLast? := by
    change (P.flatMap (SegmentToken.expand D I f)).getLast? = _
    rw [last_expand_route,pt,last]
    rfl
  have nonempty : B ≠ [] := by intro h; rw [h] at first; cases first
  have cn : C ≠ [] := by intro h; rw [h,first] at headC; cases headC
  have per := expand_route_perm D I f P perm used
  have core : (List.finRange (n+1)).map f = block f ++ [f (Fin.last n)] := by
    rw [List.finRange_succ_last]
    simp [block,Function.comp_def]
  have move : ((block f ++ [f (Fin.last n)]) ++ (List.finRange k).flatMap I).Perm
      (f (Fin.last n) :: (block f ++ (List.finRange k).flatMap I)) := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using
      (List.perm_middle (a := f (Fin.last n)) (l₁ := block f) (l₂ := (List.finRange k).flatMap I))
  rw [core] at per
  exact trace_of_middle_replacement p split nonempty cn headC tailC
    (per.trans (move.trans (corePerm.symm.cons _))) (expand_route_chain chart inside ch)

#print axioms traceable_of_segment_route

end Graffiti199Depleted.WiderOmission
