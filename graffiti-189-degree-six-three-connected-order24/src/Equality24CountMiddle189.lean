import Equality24CNFMiddle189

open Finset SimpleGraph Graffiti189LongestPath
open Graffiti189LongestPath.Equality24Profile Graffiti189LongestPath.Equality24CNF Graffiti189LongestPath.Layer24Numbering
open private Graffiti189LongestPath.Equality24CNF.valuation Graffiti189LongestPath.Equality24CNF.val_pack
  Graffiti189LongestPath.Equality24CNF.val_edge Graffiti189LongestPath.Equality24CNF.val_near
  Graffiti189LongestPath.Equality24CNF.val_high
  Graffiti189LongestPath.Equality24CNF.posSat Graffiti189LongestPath.Equality24CNF.negSat from Equality24CNFMiddle189
set_option linter.unusedSectionVars false
set_option maxRecDepth 30000
set_option maxHeartbeats 30000000
namespace Graffiti189LongestPath.Equality24Count

def back (p : Vert) : Vert := ⟨p.val-1,by have := p.isLt; omega⟩
def metric (d : Bool) (i j : Vert) := if d then near i j else edge i j

private theorem cv {G : SimpleGraph Vert} [DecidableRel G.Adj] (d : Bool) (i p k : Vert) :
    Graffiti189LongestPath.Equality24CNF.valuation G (countCode d i p k) ↔
      k.val≤(vertexSlice G d i p).card := by
  unfold countCode
  rw [Graffiti189LongestPath.Equality24CNF.val_pack]
  cases d <;> rfl

private theorem mv {G : SimpleGraph Vert} [DecidableRel G.Adj] (d : Bool) (i j : Vert) :
    Graffiti189LongestPath.Equality24CNF.valuation G (metric d i j) ↔ sample G d i j := by
  cases d
  · exact Graffiti189LongestPath.Equality24CNF.val_edge i j
  · exact Graffiti189LongestPath.Equality24CNF.val_near i j

private theorem prefix_zero (G : SimpleGraph Vert) [DecidableRel G.Adj] (d : Bool) (i : Vert) :
    (vertexSlice G d i 0).card=if sample G d i 0 then 1 else 0 := by
  by_cases h : sample G d i 0
  · have e : vertexSlice G d i 0={0} := by
      ext j
      simp only [vertexSlice,mem_filter,mem_univ,true_and,mem_singleton]
      constructor
      · intro q
        have q := q.1
        exact Fin.ext (by change j.val≤0 at q; omega)
      · rintro rfl
        exact ⟨le_rfl,h⟩
    rw [e,card_singleton,if_pos h]
  · have e : vertexSlice G d i 0=∅ := by
      apply eq_empty_iff_forall_not_mem.mpr
      intro j jj
      obtain ⟨jo,sj⟩ := (mem_filter.mp jj).2
      have hj : j=0 := Fin.ext (by change j.val≤0 at jo; omega)
      exact h (hj ▸ sj)
    rw [e,card_empty,if_neg h]

private theorem prefix_step (G : SimpleGraph Vert) [DecidableRel G.Adj] (d : Bool) (i p k : Vert)
    (hp : p≠0) (hk : k≠0) :
    k.val≤(vertexSlice G d i p).card ↔
      k.val≤(vertexSlice G d i (back p)).card ∨
      ((back k).val≤(vertexSlice G d i (back p)).card ∧ sample G d i p) := by
  have ppos : 0<p.val := by
    by_contra! h
    exact hp (Fin.ext (by change p.val=0; omega))
  have kpos : 0<k.val := by
    by_contra! h
    exact hk (Fin.ext (by change k.val=0; omega))
  have prev (j : Vert) : j.val≤p.val ↔ j=p ∨ j.val≤(back p).val := by
    change j.val≤p.val ↔ j=p ∨ j.val≤p.val-1
    constructor
    · intro q
      by_cases e : j.val=p.val
      · exact Or.inl (Fin.ext e)
      · exact Or.inr (by omega)
    · rintro (rfl|r) <;> omega
  by_cases h : sample G d i p
  · have eq : vertexSlice G d i p=insert p (vertexSlice G d i (back p)) := by
      ext j
      simp only [vertexSlice,mem_filter,mem_univ,true_and,mem_insert]
      rw [prev j]
      constructor
      · rintro ⟨rfl|l,q⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨l,q⟩
      · rintro (rfl|⟨l,q⟩)
        · exact ⟨Or.inl rfl,h⟩
        · exact ⟨Or.inr l,q⟩
    have no : p∉vertexSlice G d i (back p) := by
      intro e
      have q := (mem_filter.mp e).2.1
      change p.val≤p.val-1 at q
      omega
    rw [eq,card_insert_of_not_mem no]
    simp only [h,and_true,back]
    omega
  · have eq : vertexSlice G d i p=vertexSlice G d i (back p) := by
      ext j
      simp only [vertexSlice,mem_filter,mem_univ,true_and]
      rw [prev j]
      constructor
      · rintro ⟨rfl|l,q⟩
        · exact (h q).elim
        · exact ⟨l,q⟩
      · exact fun ⟨l,q⟩ => ⟨Or.inr l,q⟩
    simp [eq,h]

def StepClause (d : Bool) (i p k : Vert) (j : Fin 4) : List Sat.Literal :=
  let current := countCode d i p k
  let same := countCode d i (back p) k
  let less := countCode d i (back p) (back k)
  let m := metric d i p
  if j=0 then [.neg same,.pos current]
  else if j=1 then [.neg less,.neg m,.pos current]
  else if j=2 then [.neg current,.pos same,.pos less]
  else [.neg current,.pos same,.pos m]

inductive Rule where
  | ordinary (rule : Equality24CNF.Rule)
  | zero (d : Bool) (i p : Vert)
  | base (d : Bool) (i : Vert) (direction : Bool)
  | impossibleBase (d : Bool) (i k : Vert)
  | step (d : Bool) (i p k : Vert) (kind : Fin 4)
  | capFinal (i : Vert)
  | fromHigh (i : Vert)

def Rule.clause : Rule→List Sat.Literal
  | .ordinary r => r.clause
  | .zero d i p => [.pos (countCode d i p 0)]
  | .base d i flag =>
    if flag then [.neg (countCode d i 0 1),.pos (metric d i 0)]
    else [.neg (metric d i 0),.pos (countCode d i 0 1)]
  | .impossibleBase d i k => [.neg (countCode d i 0 k)]
  | .step d i p k j => StepClause d i p k j
  | .capFinal i => [.neg (countCode true i 23 7)]
  | .fromHigh i => [.neg (high i),.pos (countCode false i 23 6)]

def Rule.WF (m : Kind) (t b : ℕ) : Rule→Prop
  | .ordinary r => r.WF m t b
  | .impossibleBase _ _ k => 2≤k.val
  | .step _ _ p k _ => p≠0 ∧ k≠0
  | .capFinal _ => True
  | _ => True

instance (m : Kind) (t b : ℕ) (r : Rule) : Decidable (r.WF m t b) := by
  cases r <;> simp only [Rule.WF] <;> infer_instance

private theorem final_shadow (G : SimpleGraph Vert) [DecidableRel G.Adj] (i : Vert) :
    vertexSlice G true i 23=Shadow G i := by
  ext j
  have le : j.val≤(23:Vert).val := by change j.val≤23; have := j.isLt; omega
  constructor
  · intro h
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp h).2.2⟩
  · intro h
    exact mem_filter.mpr ⟨mem_univ _,le,(mem_filter.mp h).2⟩

private theorem final_neigh (G : SimpleGraph Vert) [DecidableRel G.Adj] (i : Vert) :
    vertexSlice G false i 23=G.neighborFinset i := by
  ext j
  have le : j.val≤(23:Vert).val := by change j.val≤23; have := j.isLt; omega
  constructor
  · intro h
    exact (G.mem_neighborFinset _ _).mpr (mem_filter.mp h).2.2
  · intro h
    exact mem_filter.mpr ⟨mem_univ _,le,(G.mem_neighborFinset _ _).mp h⟩

private theorem step_satisfies (v : Sat.Valuation) (a b c d : Nat) (i : Fin 4)
    (rel : v a ↔ v b ∨ (v c ∧ v d)) :
    v.satisfies (if i=0 then [.neg b,.pos a]
      else if i=1 then [.neg c,.neg d,.pos a]
      else if i=2 then [.neg a,.pos b,.pos c]
      else [.neg a,.pos b,.pos d]) := by
  by_cases i0 : i=0
  · rw [if_pos i0]
    intro hb na
    exact na (rel.mpr (Or.inl hb))
  rw [if_neg i0]
  by_cases i1 : i=1
  · rw [if_pos i1]
    intro hc hd na
    exact na (rel.mpr (Or.inr ⟨hc,hd⟩))
  rw [if_neg i1]
  by_cases i2 : i=2
  · rw [if_pos i2]
    intro ha nb nc
    exact (rel.mp ha).elim nb (fun q => nc q.1)
  · rw [if_neg i2]
    intro ha nb nd
    exact (rel.mp ha).elim nb (fun q => nd q.2)

theorem satisfies_rule {G : SimpleGraph Vert} [DecidableRel G.Adj] {m : Kind} {t b : ℕ}
    (M : Model G m t b) (r : Rule) (wr : r.WF m t b) :
    (Graffiti189LongestPath.Equality24CNF.valuation G).satisfies r.clause := by
  classical
  let v := Graffiti189LongestPath.Equality24CNF.valuation G
  change v.satisfies r.clause
  cases r with
  | ordinary r => exact Equality24CNF.satisfies_rule M r wr
  | zero d i p =>
    intro notZero
    exact notZero ((cv d i p 0).mpr (Nat.zero_le _))
  | base d i dir =>
    cases dir
    · intro hit noCount
      have hs := (mv d i 0).mp hit
      apply noCount
      refine (cv d i 0 1).mpr ?_
      rw [prefix_zero,if_pos hs]
      exact le_rfl
    · intro count noHit
      have q := (cv d i 0 1).mp count
      apply noHit
      refine (mv d i 0).mpr ?_
      by_contra h
      rw [prefix_zero,if_neg h] at q
      exact (show ¬(1:Vert).val≤0 by decide) q
  | impossibleBase d i k =>
    intro e
    have q := (cv d i 0 k).mp e
    rw [prefix_zero] at q
    change 2≤k.val at wr
    split at q <;> omega
  | capFinal i =>
    intro e
    have q := (cv true i 23 7).mp e
    rw [final_shadow] at q
    have ub := M.cap i
    change (7:ℕ)≤(Shadow G i).card at q
    omega
  | fromHigh i =>
    intro hi noCount
    have e := (Graffiti189LongestPath.Equality24CNF.val_high i).mp hi
    apply noCount
    apply (cv false i 23 6).mpr
    rwa [final_neigh,G.card_neighborFinset_eq_degree]
  | step d i p k branch =>
    have step := prefix_step G d i p k wr.1 wr.2
    have relation : v (countCode d i p k) ↔
        v (countCode d i (back p) k) ∨
        (v (countCode d i (back p) (back k)) ∧ v (metric d i p)) := by
      refine (cv d i p k).trans (step.trans ?_)
      constructor
      · intro e
        exact e.imp ((cv d i (back p) k).mpr)
          (fun e => ⟨(cv d i (back p) (back k)).mpr e.1,(mv d i p).mpr e.2⟩)
      · intro e
        exact e.imp ((cv d i (back p) k).mp)
          (fun e => ⟨(cv d i (back p) (back k)).mp e.1,(mv d i p).mp e.2⟩)
    exact step_satisfies v _ _ _ _ branch relation

theorem contradiction_of_proof {G : SimpleGraph Vert} [DecidableRel G.Adj] {m : Kind} {t b : ℕ}
    (M : Model G m t b) (rules : List Rule) (wf : ∀ r∈rules,r.WF m t b)
    (certificate : Sat.Fmla.proof (rules.map Rule.clause) []) : False := by
  apply certificate (Graffiti189LongestPath.Equality24CNF.valuation G)
  constructor
  intro C hC
  obtain ⟨r,rm,rfl⟩ := List.mem_map.mp hC
  exact satisfies_rule M r (wf _ rm)

#print axioms contradiction_of_proof
end Graffiti189LongestPath.Equality24Count
