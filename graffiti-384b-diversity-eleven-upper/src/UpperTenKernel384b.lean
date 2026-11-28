import Q10MaskKernel384b

namespace Graffiti384b.DiversityEleven.CutTen
open Finset
abbrev Label := Fin 10
abbrev Rel := Label→Label→Bool
abbrev score := Graffiti384b.Q10.score

def degree (E : Rel) (v : Label) : Nat := (univ.filter fun w=>E v w=true).card

def across (m : Nat) (v w : Label) : Bool := m.testBit v.val != m.testBit w.val
def cross (E : Rel) (m : Nat) (v : Label) : Nat := degree (fun x y=>E x y && across m x y) v
def inside (E : Rel) (m : Nat) (v : Label) : Nat := degree (fun x y=>E x y && !across m x y) v

def adjacentAcross (E : Rel) (m : Nat) (v w : Label) : Bool := E v w && across m v w

def Ordinary (v : Label) : Prop := v≠0 ∧ v≠4
instance (v : Label) : Decidable (Ordinary v) := by unfold Ordinary; infer_instance

structure Admissible (E : Rel) (m : Nat) : Prop where
  minDegree : ∀ v, Ordinary v → 4≤degree E v
  minScore : ∀ v, Ordinary v → 4≤score E v
  minCross : ∀ v, Ordinary v → 3≤cross E m v
  active : ∀ v, 2≤inside E m v → adjacentAcross E m v 0=true ∨ adjacentAcross E m v 4=true

def Cover (E : Rel) (D : Finset Label) : Prop :=
  D.card≤4 ∧ ∀ v : Label, v∉D → 2≤(D.filter fun w=>E v w=true).card
instance (E : Rel) (D : Finset Label) : Decidable (Cover E D) := by unfold Cover; infer_instance

theorem card_mono {E F : Rel} (h : ∀ i j,E i j=true→F i j=true) (D : Finset Label) (v : Label) :
    (D.filter fun w=>E v w=true).card≤(D.filter fun w=>F v w=true).card :=
  card_le_card (fun _w hw=>mem_filter.mpr ⟨(mem_filter.mp hw).1,h _ _ (mem_filter.mp hw).2⟩)

private theorem split_mono {E F : Rel} (h : ∀ i j,E i j=true→F i j=true)
    (r : Rel) (i j : Label) : (E i j && r i j)=true→(F i j && r i j)=true := by
  simp only [Bool.and_eq_true]
  exact fun z=>⟨h _ _ z.1,z.2⟩

inductive Reason
  | degreeSmall (v : Label)
  | scoreSmall (v : Label)
  | crossSmall (v : Label)
  | noActive (v : Label)
  | cover (D : Finset Label)

def validReason (lo hi : Rel) (m : Nat) : Reason→Prop
  | .degreeSmall v => Ordinary v ∧ degree hi v<4
  | .scoreSmall v => Ordinary v ∧ score hi v<4
  | .crossSmall v => Ordinary v ∧ cross hi m v<3
  | .noActive v => 2≤inside lo m v ∧ adjacentAcross hi m v 0=false ∧ adjacentAcross hi m v 4=false
  | .cover D => Cover lo D
instance (lo hi : Rel) (m : Nat) (r : Reason) : Decidable (validReason lo hi m r) := by
  cases r <;> unfold validReason <;> infer_instance

theorem reason_sound {lo hi E : Rel} {m : Nat} (ad : Admissible E m)
    (L : ∀ i j,lo i j=true→E i j=true) (U : ∀ i j,E i j=true→hi i j=true)
    (r : Reason) (ok : validReason lo hi m r) : ∃ D,Cover E D := by
  cases r with
  | degreeSmall v =>
    obtain ⟨normal,cap⟩ := ok
    have q := ad.minDegree v normal
    have r : degree E v≤degree hi v := card_mono U univ v
    omega
  | scoreSmall v =>
    obtain ⟨normal,cap⟩ := ok
    have q := ad.minScore v normal
    have r : score E v≤score hi v := Graffiti384b.Q10.score_mono U v
    omega
  | crossSmall v =>
    obtain ⟨normal,cap⟩ := ok
    have q := ad.minCross v normal
    have r : cross E m v≤cross hi m v := card_mono (split_mono U (across m)) univ v
    omega
  | noActive v =>
    obtain ⟨low,off0,off4⟩ := ok
    have r : inside lo m v≤inside E m v := card_mono (split_mono L (fun x y=> !across m x y)) univ v
    rcases ad.active v (low.trans r) with act|act
    · have x : adjacentAcross hi m v 0=true := split_mono U (across m) _ _ act
      rw [off0] at x
      contradiction
    · have x : adjacentAcross hi m v 4=true := split_mono U (across m) _ _ act
      rw [off4] at x
      contradiction
  | cover D =>
    exact ⟨D,ok.1,fun v hv=>(ok.2 v hv).trans (card_mono L D v)⟩

def slot (i j : Nat) : Nat := (i*(19-i))/2 + (j-i-1)

def withBits (M : Label→Label→Option Bool) (b : Nat→Bool) (u v : Label) : Bool :=
  (M u v).getD (b (slot (min u.val v.val) (max u.val v.val)))

theorem withBits_mono {M : Label→Label→Option Bool} {a b : Nat→Bool}
    (h : ∀ j,a j=true→b j=true) (i j : Label) :
    withBits M a i j=true→withBits M b i j=true := by
  unfold withBits
  cases M i j
  · exact h _
  · exact id

inductive Tree
  | tip (r : Reason)
  | split (i : Nat) (no yes : Tree)

def treeOK (M : Label→Label→Option Bool) (m on off : Nat) : Tree→Bool
  | .tip r => decide (validReason (withBits M (fun j=>on.testBit j))
    (withBits M (fun j=>!off.testBit j)) m r)
  | .split i no yes =>
    treeOK M m on (off ||| 2^i) no && treeOK M m (on ||| 2^i) off yes

theorem tree_sound (M : Label→Label→Option Bool) (m : Nat) (b : Nat→Bool)
    (H : Admissible (withBits M b) m) (T : Tree) (on off : Nat)
    (O : ∀ j,on.testBit j=true→b j=true)
    (Z : ∀ j,off.testBit j=true→b j=false)
    (valid : treeOK M m on off T=true) : ∃ D,Cover (withBits M b) D := by
  induction T generalizing on off with
  | tip r =>
    apply reason_sound H (withBits_mono O) (withBits_mono ?_) r (of_decide_eq_true valid)
    intro i bi
    change (!off.testBit i)=true
    cases e : off.testBit i
    · rfl
    · exact Bool.noConfusion (bi.symm.trans (Z i e))
  | split i no yes ihN ihY =>
    simp only [treeOK,Bool.and_eq_true] at valid
    obtain ⟨hn,hy⟩ := valid
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

theorem checked_tree (M : Label→Label→Option Bool) (m : Nat) (b : Nat→Bool)
    (H : Admissible (withBits M b) m) (T : Tree)
    (valid : treeOK M m 0 0 T=true) : ∃ D,Cover (withBits M b) D :=
  tree_sound M m b H T 0 0 (by simp) (by simp) valid

theorem join (M : Label→Label→Option Bool) (m bit on off off' on' : Nat) (l r : Tree)
    (ht : (off|||2^bit)=off') (hf : (on|||2^bit)=on')
    (no : treeOK M m on off' l=true) (yes : treeOK M m on' off r=true) :
    treeOK M m on off (.split bit l r)=true := by
  simp only [treeOK,ht,hf,Bool.and_eq_true]
  exact ⟨no,yes⟩

#print axioms checked_tree
#print axioms join
end Graffiti384b.DiversityEleven.CutTen
