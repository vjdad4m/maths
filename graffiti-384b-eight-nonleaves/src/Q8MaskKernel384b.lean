import Proof384b
import Mathlib.Data.Fin.VecNotation

namespace Graffiti384b.Q8
open Finset
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

structure Shape where
  edge01 : Bool
  d0 : ℕ
  d1 : ℕ
  common : ℕ

def forms : Fin 8 → Shape :=
  ![⟨false,5,5,4⟩,⟨true,5,5,2⟩,⟨true,5,5,3⟩,⟨true,5,5,4⟩,
    ⟨true,6,5,3⟩,⟨true,6,5,4⟩,⟨true,6,6,4⟩,⟨true,7,5,4⟩]

def slot (i j : Nat) : Nat := ((i-2)*(13-i))/2 + (j-i-1)

def anchorZero (s : Shape) (r : Nat) : Bool :=
  decide (r<s.d0-(if s.edge01 then 1 else 0))

def anchorOne (s : Shape) (r : Nat) : Bool :=
  let a := s.d0-(if s.edge01 then 1 else 0)
  let b := s.d1-(if s.edge01 then 1 else 0)
  decide (r<s.common ∨ (a≤r ∧ r<a+b-s.common))

def adj (s : Shape) (b : Nat→Bool) (u v : Fin 8) : Bool :=
  let i := min u.val v.val
  let j := max u.val v.val
  if i=j then false else
  if i=0 then if j=1 then s.edge01 else anchorZero s (j-2)
  else if i=1 then anchorOne s (j-2)
  else b (slot i j)

theorem adj_mono {s : Shape} {a b : Nat→Bool}
    (h : ∀ j,a j=true→b j=true) (i j : Fin 8) :
    adj s a i j=true→adj s b i j=true := by
  dsimp [adj]
  split <;> (try exact id)
  split <;> (try exact id)
  split
  · exact id
  · exact h _

abbrev Label := Fin 8
abbrev Rel := Label→Label→Bool

def orderedPairs : List (Label × Label) :=
  (List.ofFn (fun i : Label=>i)).flatMap fun i =>
    ((List.ofFn (fun j : Label=>j)).filter (fun j=>decide (i<j))).map fun j=>(i,j)

def score (E : Rel) (v : Label) : Nat :=
  (orderedPairs.filter fun ij=>E v ij.1 && E v ij.2 && E ij.1 ij.2).length

private theorem length_filter_mono {α : Type} (a b : α→Bool) (l : List α)
    (inc : ∀ x,a x=true→b x=true) : (l.filter a).length≤(l.filter b).length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    by_cases h : a x=true
    · simp [List.filter_cons,h,inc _ h,ih]
    · have z : a x=false := Bool.eq_false_iff.mpr h
      cases e : b x <;> simp [List.filter_cons,z,e] <;> omega

theorem score_mono {E F : Rel} (h : ∀ i j,E i j=true→F i j=true) (v : Label) :
    score E v≤score F v := by
  unfold score
  apply length_filter_mono
  intro z hz
  simp only [Bool.and_eq_true] at hz ⊢
  exact ⟨⟨h _ _ hz.1.1,h _ _ hz.1.2⟩,h _ _ hz.2⟩

def Dominates3 (E : Rel) (a b c : Label) : Prop :=
  a≠b ∧ a≠c ∧ b≠c ∧ ∀ v : Label,v≠a→v≠b→v≠c→
    (E v a=true ∧ E v b=true) ∨ (E v a=true ∧ E v c=true) ∨ (E v b=true ∧ E v c=true)

instance (E : Rel) (a b c : Label) : Decidable (Dominates3 E a b c) := by
  unfold Dominates3
  infer_instance

theorem dominates_mono {E F : Rel} (h : ∀ i j,E i j=true→F i j=true) {a b c : Label}
    (d : Dominates3 E a b c) : Dominates3 F a b c := by
  refine ⟨d.1,d.2.1,d.2.2.1,?_⟩
  intro v va vb vc
  rcases d.2.2.2 v va vb vc with xy|xy|xy
  · exact Or.inl ⟨h _ _ xy.1,h _ _ xy.2⟩
  · exact Or.inr (Or.inl ⟨h _ _ xy.1,h _ _ xy.2⟩)
  · exact Or.inr (Or.inr ⟨h _ _ xy.1,h _ _ xy.2⟩)

def anchor (r : Fin 2) : Label := ⟨r.val,by have := r.isLt; omega⟩

structure Ranked (E : Rel) : Prop where
  pos : ∀ v, 0<score E v
  distinct : Function.Injective (score E)
  large : ∀ r : Fin 2, 7≤score E (anchor r)
  top : ∀ (v : Label),2≤v.val→∀ (r : Fin 2),score E v<score E (anchor r)

inductive Reason
  | small (r : Fin 2)
  | unordered (v : Label) (r : Fin 2)
  | zero (v : Label)
  | equal (u v : Label)
  | cover (a b c : Label)

def validReason (lo hi : Rel) : Reason→Prop
  | .small r => score hi (anchor r)<7
  | .unordered v r => 2≤v.val ∧ score hi (anchor r)≤score lo v
  | .zero v => score hi v=0
  | .equal u v => u≠v ∧ score lo u=score hi u ∧ score lo v=score hi v ∧ score lo u=score lo v
  | .cover a b c => Dominates3 lo a b c

instance (lo hi : Rel) (r : Reason) : Decidable (validReason lo hi r) := by
  cases r <;> unfold validReason <;> infer_instance

theorem reason_sound {lo E hi : Rel} (H : Ranked E)
    (L : ∀ i j,lo i j=true→E i j=true) (U : ∀ i j,E i j=true→hi i j=true)
    (r : Reason) (valid : validReason lo hi r) : ∃ a b c, Dominates3 E a b c := by
  cases r with
  | small j =>
    have x := H.large j
    have y := score_mono U (anchor j)
    unfold validReason at valid
    omega
  | unordered v j =>
    obtain ⟨vn,ord⟩ := valid
    have x := H.top v vn j
    have y := score_mono U (anchor j)
    have z := score_mono L v
    omega
  | zero v =>
    have x := H.pos v
    have y := score_mono U v
    unfold validReason at valid
    omega
  | equal u v =>
    obtain ⟨ne,ue,ve,eq⟩ := valid
    have u0 := score_mono L u
    have u1 := score_mono U u
    have v0 := score_mono L v
    have v1 := score_mono U v
    exact (ne (H.distinct (by omega))).elim
  | cover a b c => exact ⟨a,b,c,dominates_mono L valid⟩

inductive Tree
  | tip (r : Reason)
  | split (i : Nat) (no yes : Tree)

def lo (s : Shape) (on : Nat) : Rel := adj s (fun j=>on.testBit j)
def hi (s : Shape) (off : Nat) : Rel := adj s (fun j=>!off.testBit j)

def treeOK (s : Shape) (on off : Nat) : Tree→Bool
  | .tip r => decide (validReason (lo s on) (hi s off) r)
  | .split i no yes => treeOK s on (off ||| 2^i) no && treeOK s (on ||| 2^i) off yes

theorem tree_sound (s : Shape) (b : Nat→Bool) (H : Ranked (adj s b))
    (T : Tree) (on off : Nat)
    (O : ∀ j,on.testBit j=true→b j=true)
    (Z : ∀ j,off.testBit j=true→b j=false)
    (valid : treeOK s on off T=true) : ∃ a c d,Dominates3 (adj s b) a c d := by
  induction T generalizing on off with
  | tip r =>
    apply reason_sound H (adj_mono O) (adj_mono ?_) r (of_decide_eq_true valid)
    intro i bi
    change (!off.testBit i)=true
    cases e : off.testBit i
    · rfl
    · exact Bool.noConfusion (bi.symm.trans (Z i e))
  | split i no yes ihN ihY =>
    change (treeOK s on (off|||2^i) no && treeOK s (on|||2^i) off yes)=true at valid
    have both : treeOK s on (off|||2^i) no=true ∧ treeOK s (on|||2^i) off yes=true := by
      simpa only [Bool.and_eq_true] using valid
    obtain ⟨hn,hy⟩ := both
    cases v : b i
    · apply ihN on (off|||2^i) O ?_ hn
      intro j h
      rw [Nat.testBit_or,Bool.or_eq_true,Nat.testBit_two_pow,decide_eq_true_eq] at h
      rcases h with h|rfl
      · exact Z j h
      · exact v
    · apply ihY (on|||2^i) off ?_ Z hy
      intro j h
      rw [Nat.testBit_or,Bool.or_eq_true,Nat.testBit_two_pow,decide_eq_true_eq] at h
      rcases h with h|rfl
      · exact O j h
      · exact v

theorem checked_tree (s : Shape) (b : Nat→Bool) (H : Ranked (adj s b)) (T : Tree)
    (valid : treeOK s 0 0 T=true) : ∃ a c d,Dominates3 (adj s b) a c d :=
  tree_sound s b H T 0 0 (by simp) (by simp) valid

#print axioms checked_tree
end Graffiti384b.Q8
