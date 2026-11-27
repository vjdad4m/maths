import FirstBandFour133

namespace Graffiti133Bicycle
open SimpleGraph Graffiti133 Graffiti133NoFive Finset
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

def bit (rows : List Nat) (i j : Nat) : Bool := (rows.getD i 0).testBit j
def cycle (i j : Nat) : Bool :=
  decide (i+1=j ∨ j+1=i ∨ (i=0 ∧ j+1=7) ∨ (j=0 ∧ i+1=7))

def adj (rows : List Nat) (site : Nat → Nat) (i j : Nat) : Bool :=
  if i<7 then
    if j<7 then cycle i j else i == site (j-7)
  else if j<7 then j == site (i-7)
  else bit rows (i-7) (j-7)

def pslot (code i : Nat) : Nat := code / (32^i) % 32

def pathCheck (rows seq : List Nat) (code : Nat) : Bool :=
  let p := pslot code
  (List.range 9).all (fun i =>
    decide (p i < 7+seq.length) &&
      (List.range 9).all (fun j =>
        if i<j then (p i != p j) &&
          (adj rows (fun k => seq.getD k 7) (p i) (p j) == (i+1==j)) else true))

def stepLegal (rows d2 seq : List Nat) (c : Nat) : Bool :=
  (List.range seq.length).all (fun i =>
    (!(bit rows seq.length i) || !(cycle c (seq.getD i 7))) &&
    (!(bit d2 seq.length i) || (c != seq.getD i 7)))

structure Legal (rows d2 : List Nat) (n : Nat) (s : Nat → Nat) : Prop where
  range : ∀ i < n,s i<7
  adjacent : ∀ i < n, ∀ j < i, bit rows i j = true → cycle (s i) (s j) = false
  apart : ∀ i < n, ∀ j < i, bit d2 i j = true → s i≠s j

def PathExists (rows : List Nat) (n : Nat) (s : Nat → Nat) : Prop :=
  ∃ p : Fin 9 → Nat, Function.Injective p ∧ (∀ i, p i<7+n) ∧
    ∀ i j, i<j → (adj rows s (p i) (p j)=true ↔ i.val+1=j.val)

def Agrees (s : Nat → Nat) (seq : List Nat) : Prop :=
  ∀ i < seq.length,seq.getD i 7=s i

private theorem extAgrees {s : Nat → Nat} {seq : List Nat} (h : Agrees s seq) :
    Agrees s (seq ++ [s seq.length]) := by
  intro i hi
  by_cases k : i<seq.length
  · rw [List.getD_eq_getElem?_getD,List.getElem?_append_left k,←List.getD_eq_getElem?_getD]
    exact h i k
  · have ie : i=seq.length := by simp at hi; omega
    subst i
    simp

private theorem adjAgree (rows seq : List Nat) (s : Nat → Nat) (h : Agrees s seq)
    {i j : Nat} (hi : i<7+seq.length) (hj : j<7+seq.length) :
    adj rows (fun k => seq.getD k 7) i j = adj rows s i j := by
  unfold adj
  split
  · split
    · rfl
    · exact congrArg (fun t => i == t) (h (j-7) (by omega))
  · split
    · exact congrArg (fun t => j == t) (h (i-7) (by omega))
    · rfl

theorem pathCheck_sound {rows seq : List Nat} {code n : Nat} {s : Nat → Nat}
    (h : Agrees s seq) (size : seq.length≤n) (ok : pathCheck rows seq code=true) :
    PathExists rows n s := by
  let p (i : Fin 9) := pslot code i.val
  have row (i : Fin 9) := (Iff.of_eq (Bool.and_eq_true _ _)).mp
    (List.all_eq_true.mp ok i.val (List.mem_range.mpr i.isLt))
  have pos (i : Fin 9) : p i<7+seq.length := of_decide_eq_true (row i).1
  have all (i j : Fin 9) (lt : i<j) : p i≠p j ∧
      ((adj rows s (p i) (p j)=true) ↔ i.val+1=j.val) := by
    have atj := List.all_eq_true.mp (row i).2 j.val (List.mem_range.mpr j.isLt)
    have lt' : i.val<j.val := lt
    rw [if_pos lt'] at atj
    have q := (Iff.of_eq (Bool.and_eq_true _ _)).mp atj
    refine ⟨bne_iff_ne.mp q.1,?_⟩
    rw [←adjAgree rows seq s h (pos i) (pos j),beq_iff_eq.mp q.2]
    simp
  refine ⟨p,?_,fun i => (pos i).trans_le (Nat.add_le_add_left size _),fun i j g => (all i j g).2⟩
  intro i j eq
  rcases lt_trichotomy i j with l|e|g
  · exact ((all i j l).1 eq).elim
  · exact e
  · exact ((all j i g).1 eq.symm).elim

def verify (rows d2 : List Nat) (data : List (List Nat)) :
    (fuel node : Nat) → (seq : List Nat) → Bool
  | 0, _, _ => false
  | f+1, node, seq =>
    (List.range 7).all fun c =>
      if stepLegal rows d2 seq c then
        let w := (data.getD node []).getD c 0
        if w<1024 then verify rows d2 data f w (seq ++ [c])
        else pathCheck rows (seq ++ [c]) (w-1024)
      else true

theorem verify_sound {rows d2 : List Nat} {data : List (List Nat)}
    {n : Nat} {s : Nat → Nat} (legal : Legal rows d2 n s)
    (fuel node : Nat) (seq : List Nat) (size : seq.length+fuel=n)
    (same : Agrees s seq) (ok : verify rows d2 data fuel node seq=true) :
    PathExists rows n s := by
  induction fuel generalizing node seq with
  | zero => simp [verify] at ok
  | succ f ih =>
    let c := s seq.length
    have lt : seq.length<n := by omega
    have hC : c<7 := legal.range _ lt
    have fine : stepLegal rows d2 seq c = true := by
      apply List.all_eq_true.mpr
      intro i hi
      have il := List.mem_range.mp hi
      rw [same i il]
      by_cases hr : bit rows seq.length i = true
      · by_cases hd : bit d2 seq.length i = true
        · have cyc := legal.adjacent _ lt _ il hr
          have ne := legal.apart _ lt _ il hd
          simp [hr,hd,c,cyc,ne]
        · have cyc := legal.adjacent _ lt _ il hr
          simp [hr,hd,c,cyc]
      · by_cases hd : bit d2 seq.length i = true
        · have ne := legal.apart _ lt _ il hd
          simp [hr,hd,c,ne]
        · simp [hr,hd]
    have b := List.all_eq_true.mp (show ((List.range 7).all _) = true from ok) c (List.mem_range.mpr hC)
    change (if stepLegal rows d2 seq c then _ else true) = true at b
    rw [if_pos (show stepLegal rows d2 seq c = true from fine)] at b
    let w := (data.getD node []).getD c 0
    change (if w<1024 then verify rows d2 data f w (seq ++ [c]) else pathCheck rows (seq ++ [c]) (w-1024))=true at b
    by_cases h : w<1024
    · rw [if_pos h] at b
      exact ih w (seq++[c]) (by simp; omega) (extAgrees same) b
    · rw [if_neg h] at b
      exact pathCheck_sound (extAgrees same) (by simp; omega) b

theorem numbered_site_zero_has_path {rows d2 : List Nat} {data : List (List Nat)}
    {n : Nat} {s : Nat → Nat} (hn : 1≤n) (legal : Legal rows d2 n s) (zero : s 0=0)
    (ok : verify rows d2 data (n-1) 0 [0]=true) : PathExists rows n s := by
  apply verify_sound legal (n-1) 0 [0] (by simp; omega) ?_ ok
  intro i hi
  have e : i=0 := by simp at hi; omega
  subst i
  simpa using zero.symm

#print axioms numbered_site_zero_has_path
end Graffiti133Bicycle
namespace Graffiti133Bicycle
open SimpleGraph Graffiti133
set_option linter.unusedSectionVars false
variable {V : Type*} {G : SimpleGraph V}

structure Numbered (G : SimpleGraph V) (rows d2 : List Nat) (n : Nat) (s : Nat → Nat) where
  f : Nat → V
  inj : ∀ i < 7+n, ∀ j < 7+n, f i=f j → i=j
  siteRange : ∀ i < n, s i<7
  cycleAdj : ∀ i < 7, ∀ j < 7, G.Adj (f i) (f j) ↔ cycle i j=true
  exteriorAdj : ∀ i < n, ∀ j < n, G.Adj (f (7+i)) (f (7+j)) ↔ bit rows i j=true
  joinAdj : ∀ i < n, ∀ j < 7, G.Adj (f (7+i)) (f j) ↔ s i=j
  distanceTwo : ∀ i < n, ∀ j < n, bit d2 i j=true →
    ∃ k < n, bit rows i k=true ∧ bit rows j k=true

theorem Numbered.legal {rows d2 : List Nat} {n : Nat} {s : Nat → Nat}
    (M : Numbered G rows d2 n s) (h4 : FourCycleFree G) : Legal rows d2 n s := by
  refine ⟨M.siteRange,?_,?_⟩
  · intro i hi j hj r
    have hj' := hj.trans hi
    have si := M.siteRange i hi
    have sj := M.siteRange j hj'
    by_contra h
    have cc : cycle (s i) (s j)=true := Bool.eq_true_of_not_eq_false h
    have er := (M.exteriorAdj i hi j hj').mpr r
    have ea := (M.joinAdj i hi (s i) si).mpr rfl
    have eb := (M.joinAdj j hj' (s j) sj).mpr rfl
    have ec := (M.cycleAdj (s i) si (s j) sj).mpr cc
    have ne : M.f (7+i)≠M.f (s j) := fun f => by
      have e := M.inj (7+i) (by omega) (s j) (by omega) f
      omega
    have eq := M.inj (7+j) (by omega) (s i) (by omega) (h4 _ _ _ _ ne er eb.symm ea ec.symm)
    omega
  · intro i hi j hj r eq
    have hj' := hj.trans hi
    have si := M.siteRange i hi
    obtain ⟨k,hk,ik,jk⟩ := M.distanceTwo i hi j hj' r
    have eik := (M.exteriorAdj i hi k hk).mpr ik
    have ejk := (M.exteriorAdj j hj' k hk).mpr jk
    have ea := (M.joinAdj i hi (s i) si).mpr rfl
    have eb := (M.joinAdj j hj' (s i) si).mpr eq.symm
    have ne : M.f (7+i)≠M.f (7+j) := fun e => by
      have g := M.inj _ (by omega) _ (by omega) e
      omega
    have gap := M.inj (7+k) (by omega) (s i) (by omega) (h4 _ _ _ _ ne eik ejk ea eb)
    omega

theorem Numbered.adj_iff {rows d2 : List Nat} {n : Nat} {s : Nat → Nat}
    (M : Numbered G rows d2 n s) {i j : Nat} (hi : i<7+n) (hj : j<7+n) :
    G.Adj (M.f i) (M.f j) ↔ adj rows s i j=true := by
  unfold adj
  by_cases ei : i<7
  · rw [if_pos ei]
    by_cases ej : j<7
    · rw [if_pos ej]
      exact M.cycleAdj i ei j ej
    · rw [if_neg ej,beq_iff_eq,G.adj_comm]
      have e := M.joinAdj (j-7) (by omega) i ei
      have jEq : 7+(j-7)=j := by omega
      rw [jEq] at e
      exact e.trans eq_comm
  · rw [if_neg ei]
    by_cases ej : j<7
    · rw [if_pos ej,beq_iff_eq]
      have e := M.joinAdj (i-7) (by omega) j ej
      have iEq : 7+(i-7)=i := by omega
      rw [iEq] at e
      exact e.trans eq_comm
    · rw [if_neg ej]
      have e := M.exteriorAdj (i-7) (by omega) (j-7) (by omega)
      have iEq : 7+(i-7)=i := by omega
      have jEq : 7+(j-7)=j := by omega
      rwa [iEq,jEq] at e

theorem Numbered.lift {rows d2 : List Nat} {n : Nat} {s : Nat → Nat}
    (M : Numbered G rows d2 n s) (h : PathExists rows n s) :
    ∃ p : Fin 9 → V, InducedPath G p := by
  obtain ⟨p,inj,bound,edge⟩ := h
  exact ⟨M.f∘p,fun i j e => inj (M.inj _ (bound i) _ (bound j) e),fun i j g =>
    (M.adj_iff (bound i) (bound j)).trans (edge i j g)⟩

#print axioms Numbered.legal
#print axioms Numbered.lift
end Graffiti133Bicycle
