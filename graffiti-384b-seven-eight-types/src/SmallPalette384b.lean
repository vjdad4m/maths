import Proof384b
import Mathlib.Data.Fin.VecNotation

namespace Graffiti384b.SmallPalette
open Finset
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

structure Shape where
  edge01 : Bool
  d0 : ℕ
  d1 : ℕ
  common : ℕ

def slot (n i j : Nat) : Nat := ((i-2)*(2*n-3-i))/2 + (j-i-1)
def anchorZero (s : Shape) (r : Nat) : Bool :=
  decide (r<s.d0-(if s.edge01 then 1 else 0))
def anchorOne (s : Shape) (r : Nat) : Bool :=
  let a := s.d0-(if s.edge01 then 1 else 0)
  let b := s.d1-(if s.edge01 then 1 else 0)
  decide (r<s.common ∨ (a≤r ∧ r<a+b-s.common))
abbrev Rel (n : Nat) := Fin n → Fin n → Bool

def adj {n : Nat} (s : Shape) (b : Nat→Bool) : Rel n := fun u v =>
  let i := min u.val v.val
  let j := max u.val v.val
  if i=j then false else
  if i=0 then if j=1 then s.edge01 else anchorZero s (j-2)
  else if i=1 then anchorOne s (j-2)
  else b (slot n i j)

theorem adj_mono {n : Nat} {s : Shape} {a b : Nat→Bool}
    (h : ∀ j,a j=true→b j=true) (i j : Fin n) :
    adj s a i j=true→adj s b i j=true := by
  dsimp [adj]
  split <;> (try exact id)
  split <;> (try exact id)
  split
  · exact id
  · exact h _

def orderedPairs (n : Nat) : List (Fin n × Fin n) :=
  (List.ofFn (fun i : Fin n=>i)).flatMap fun i =>
    ((List.ofFn (fun j : Fin n=>j)).filter (fun j=>decide (i<j))).map fun j=>(i,j)

def score {n : Nat} (E : Rel n) (v : Fin n) : Nat :=
  ((orderedPairs n).filter fun ij=>E v ij.1 && E v ij.2 && E ij.1 ij.2).length

private theorem length_filter_mono {α : Type} (a b : α→Bool) (l : List α)
    (inc : ∀ x,a x=true→b x=true) : (l.filter a).length≤(l.filter b).length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    by_cases h : a x=true
    · simp [List.filter_cons,h,inc _ h,ih]
    · have z : a x=false := Bool.eq_false_iff.mpr h
      cases e : b x <;> simp [List.filter_cons,z,e] <;> omega

theorem score_mono {n : Nat} {E F : Rel n} (h : ∀ i j,E i j=true→F i j=true) (v : Fin n) :
    score E v≤score F v := by
  unfold score
  apply length_filter_mono
  intro z hz
  simp only [Bool.and_eq_true] at hz ⊢
  exact ⟨⟨h _ _ hz.1.1,h _ _ hz.1.2⟩,h _ _ hz.2⟩

def palette {n : Nat} (E : Rel n) : Finset Nat :=
  (univ.filter fun i=>0<score E i).image (score E)

def skipped (n mask : Nat) : Finset (Fin n) :=
  univ.filter fun v=>mask.testBit v.val=true

def ranges {n : Nat} (lo hi : Rel n) (mask : Nat) : Finset Nat :=
  ((univ : Finset (Fin n)) \ skipped n mask).biUnion fun v =>
    Icc (max 1 (score lo v)) (score hi v)

theorem palette_le_cover {n : Nat} {lo E hi : Rel n}
    (L : ∀ i j,lo i j=true→E i j=true)
    (U : ∀ i j,E i j=true→hi i j=true) (mask : Nat) :
    (palette E).card ≤ (skipped n mask).card + (ranges lo hi mask).card := by
  have sub : palette E ⊆ (skipped n mask).image (score E) ∪ ranges lo hi mask := by
    intro k hk
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hk
    by_cases hs : v ∈ skipped n mask
    · exact mem_union_left _ (mem_image.mpr ⟨v,hs,rfl⟩)
    · apply mem_union_right
      apply mem_biUnion.mpr
      refine ⟨v, by simp [hs], ?_⟩
      apply mem_Icc.mpr
      exact ⟨max_le (mem_filter.mp hv).2 (score_mono L v), score_mono U v⟩
  exact (card_le_card sub).trans ((card_union_le _ _).trans (Nat.add_le_add_right card_image_le _))

def O4 {n : Nat} (a b c d : Fin n) : Finset (Fin n) := {a,b,c,d}
def Effective {n : Nat} (lo hi : Rel n) (a b c d : Fin n) : Prop :=
  (O4 a b c d).card=4 ∧ ∀ v : Fin n, v ∈ O4 a b c d →
    (∃ x y : Fin n, x ∉ O4 a b c d ∧ y ∉ O4 a b c d ∧ x≠y ∧
      lo v x=true ∧ lo v y=true) ∨
    (∀ w : Fin n, w ∈ O4 a b c d → hi v w=false)

instance {n} (lo hi : Rel n) (a b c d : Fin n) : Decidable (Effective lo hi a b c d) := by
  unfold Effective
  infer_instance

structure Ranked {n : Nat} (E : Rel n) : Prop where
  palette_large : 6≤(palette E).card
  large : ∀ v : Fin n, v.val<2→5≤score E v

inductive Reason (n : Nat)
  | small (r : Fin n)
  | cover (a b c d : Fin n)
  | rank (skip : Nat)

def validReason {n} (lo hi : Rel n) : Reason n→Prop
  | .small r => r.val<2 ∧ score hi r<5
  | .cover a b c d => Effective lo hi a b c d
  | .rank mask => (skipped n mask).card + (ranges lo hi mask).card < 6

instance {n} (lo hi : Rel n) (r : Reason n) : Decidable (validReason lo hi r) := by
  cases r <;> unfold validReason <;> infer_instance

theorem reason_sound {n} {lo E hi : Rel n} (H : Ranked E)
    (L : ∀ i j,lo i j=true→E i j=true) (U : ∀ i j,E i j=true→hi i j=true)
    (r : Reason n) (valid : validReason lo hi r) : ∃ a b c d, Effective E E a b c d := by
  cases r with
  | small j =>
    obtain ⟨lt,up⟩ := valid
    have x := H.large j lt
    have y := score_mono U j
    omega
  | cover a b c d =>
    refine ⟨a,b,c,d,valid.1,?_⟩
    intro v hv
    rcases valid.2 v hv with ⟨x,y,hx,hy,hn,ex,ey⟩ | off
    · exact Or.inl ⟨x,y,hx,hy,hn,L _ _ ex,L _ _ ey⟩
    · exact Or.inr (fun w hw=>Bool.eq_false_iff.mpr (fun et=>by
        have et' := U _ _ et
        simp [off w hw] at et'))
  | rank mask =>
    have h := palette_le_cover L U mask
    have pos := H.palette_large
    change (skipped n mask).card + (ranges lo hi mask).card < 6 at valid
    omega

inductive Tree (n : Nat)
  | tip (r : Reason n)
  | split (i : Nat) (no yes : Tree n)

def lo (n : Nat) (s : Shape) (on : Nat) : Rel n := adj s (fun j=>on.testBit j)
def hi (n : Nat) (s : Shape) (off : Nat) : Rel n := adj s (fun j=>!off.testBit j)

def treeOK {n : Nat} (s : Shape) (on off : Nat) : Tree n→Bool
  | .tip r => decide (validReason (lo n s on) (hi n s off) r)
  | .split i no yes => treeOK s on (off ||| 2^i) no && treeOK s (on ||| 2^i) off yes

theorem tree_sound {n} (s : Shape) (b : Nat→Bool) (H : Ranked (n:=n) (adj s b))
    (T : Tree n) (on off : Nat)
    (O : ∀ j,on.testBit j=true→b j=true)
    (Z : ∀ j,off.testBit j=true→b j=false)
    (valid : treeOK s on off T=true) : ∃ a c d e : Fin n, Effective (adj s b) (adj s b) a c d e := by
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

theorem checked_tree {n} (s : Shape) (b : Nat→Bool) (H : Ranked (n:=n) (adj s b)) (T : Tree n)
    (valid : treeOK s 0 0 T=true) : ∃ a c d e : Fin n, Effective (adj s b) (adj s b) a c d e :=
  tree_sound s b H T 0 0 (by simp) (by simp) valid

#print axioms checked_tree
end Graffiti384b.SmallPalette
