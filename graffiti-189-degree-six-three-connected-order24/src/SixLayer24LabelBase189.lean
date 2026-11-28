import SixLayer24Normalization189
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.EquivFin

namespace Graffiti189LongestPath
open SimpleGraph Finset
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1100000
variable {V : Type*} {G : SimpleGraph V}
  [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

private noncomputable def indexSet (S : Finset V) (m : ℕ) (h : S.card = m) :
    Fin m ≃ (↑S : Set V) :=
  (Fintype.equivFinOfCardEq ((Fintype.card_coe S).trans h)).symm

/-- Abstract layer numbering with prescribed orders on the selectors and children. -/
theorem exists_layer_twenty_four_label_from_orders
    (hc : G.Connected) (x : V) (n : Fintype.card V=24) (L : Layer24Cover G x)
    (aE : Fin L.T.card ≃ (↑L.T : Set V))
    (cE : Fin (Shell G x 3).card ≃ (↑(Shell G x 3) : Set V)) :
    let b := (Shell G x 2).card
    let c := (Shell G x 3).card
    ∃ e : Fin 24 ≃ V, e 0=x ∧
      (∀ i, G.dist x (e i) = if i.val=0 then 0 else if i.val<7 then 1 else
        if i.val<7+b then 2 else if i.val<7+b+c then 3 else 4) ∧
      (∀ i, e i∈L.T ↔ 1≤i.val ∧ i.val≤L.T.card) ∧
      (∀ (i : Fin 24) (lo : 1≤i.val) (hi : i.val≤L.T.card),
        e i = (aE ⟨i.val-1,by have _a := lo; have _b := hi; omega⟩).val) ∧
      (∀ i j : Fin 24, 1≤i.val → i.val≤L.T.card → j.val=6+i.val → e j=L.rep (e i)) ∧
      (∀ (j : Fin 24) (jl : 7+b≤j.val) (jh : j.val<7+b+c),
        e j=(cE ⟨j.val-(7+b),by change _<c; have _a := jl; have _h := jh; omega⟩).val) := by
  classical
  let A := Shell G x 1
  let B := Shell G x 2
  let C := Shell G x 3
  let D := Shell G x 4
  let t := L.T.card
  let b := B.card
  let c := C.card
  have tc : t=3 ∨ t=4 := L.tSize
  have b4 : 4≤b := L.secondMin
  have e6 := L.evenMax
  have b6 : b≤6 := by change b+D.card≤6 at e6; omega
  have t4 : t≤4 := by omega
  have tot : b+c+D.card=17 := L.shellTotal
  have cc := L.thirdSize
  change c=11 ∨ c=12 at cc
  have dZ : D.card=17-b-c := by omega
  have ac : (A \ L.T).card = 6-t := by
    have s := card_sdiff_add_card_eq_card L.selected
    have h := L.firstSize
    change (A \ L.T).card + L.T.card = A.card at s
    change A.card = 6 at h
    dsimp [t]
    omega
  let aO := indexSet (A \ L.T) (6-t) ac
  let used := L.T.image L.rep
  have um : used ⊆ B := by
    intro v vm
    obtain ⟨a,at',rfl⟩ := mem_image.mp vm
    exact mem_shell.mpr (L.repDepth a at')
  have ui : ∀ a∈L.T, ∀ a'∈L.T, L.rep a = L.rep a' → a=a' := by
    intro a am a' am' eq
    apply Classical.byContradiction
    intro ne
    have h := L.repAdj a am
    rw [eq] at h
    exact L.repPrivate a' am' a am ne h
  have uc : used.card = t := card_image_of_injOn ui
  have bc : (B \ used).card = b-t := by
    have h := card_sdiff_add_card_eq_card um
    dsimp [b]
    omega
  let bO := indexSet (B \ used) (b-t) bc
  let dE := indexSet D (17-b-c) dZ
  let a (j : Fin t) := (aE j).val
  have am (j : Fin t) : a j ∈ L.T := (aE j).property
  let f (i : Fin 24) : V :=
    if h0 : i.val = 0 then x else
    if h1 : i.val < 1+t then a ⟨i.val-1,by omega⟩ else
    if h2 : i.val < 7 then (aO ⟨i.val-(1+t),by omega⟩).val else
    if h3 : i.val < 7+t then L.rep (a ⟨i.val-7,by omega⟩) else
    if h4 : i.val < 7+b then (bO ⟨i.val-(7+t),by omega⟩).val else
    if h5 : i.val < 7+b+c then (cE ⟨i.val-(7+b),by change _<c; omega⟩).val
    else (dE ⟨i.val-(7+b+c),by omega⟩).val
  have atZero : f 0 = x := by simp [f]
  have atA (j : Fin t) : f ⟨1+j.val,by omega⟩ = a j := by
    have k : (⟨1+j.val-1,by omega⟩ : Fin t) = j := by apply Fin.ext; simp only [Fin.val_mk]; omega
    simp only [f,Fin.val_mk,dif_neg (show 1+j.val≠0 by omega),
      dif_pos (show 1+j.val<1+t by omega),k]
  have atAO (j : Fin (6-t)) : f ⟨1+t+j.val,by omega⟩ = (aO j).val := by
    have h := j.isLt
    have k : (⟨1+t+j.val-(1+t),by omega⟩ : Fin (6-t)) = j := by apply Fin.ext; simp only [Fin.val_mk]; omega
    simp only [f,Fin.val_mk,dif_neg (show 1+t+j.val≠0 by omega),
      dif_neg (show ¬ 1+t+j.val<1+t by omega),dif_pos (show 1+t+j.val<7 by omega),k]
  have atB (j : Fin t) : f ⟨7+j.val,by omega⟩ = L.rep (a j) := by
    have h := j.isLt
    have k : (⟨7+j.val-7,by omega⟩ : Fin t) = j := by apply Fin.ext; simp only [Fin.val_mk]; omega
    simp only [f,Fin.val_mk,dif_neg (show 7+j.val≠0 by omega),
      dif_neg (show ¬ 7+j.val<1+t by omega),dif_neg (show ¬ 7+j.val<7 by omega),
      dif_pos (show 7+j.val<7+t by omega),k]
  have atBO (j : Fin (b-t)) : f ⟨7+t+j.val,by omega⟩ = (bO j).val := by
    have h := j.isLt
    have k : (⟨7+t+j.val-(7+t),by omega⟩ : Fin (b-t)) = j := by apply Fin.ext; simp only [Fin.val_mk]; omega
    simp only [f,Fin.val_mk,dif_neg (show 7+t+j.val≠0 by omega),
      dif_neg (show ¬ 7+t+j.val<1+t by omega),dif_neg (show ¬ 7+t+j.val<7 by omega),
      dif_neg (show ¬ 7+t+j.val<7+t by omega),dif_pos (show 7+t+j.val<7+b by omega),k]
  have atC (j : Fin c) : f ⟨7+b+j.val,by have := j.isLt; omega⟩ = (cE j).val := by
    have jj := j.isLt
    have k : (⟨7+b+j.val-(7+b),by omega⟩ : Fin c)=j := by
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
    simp only [f,Fin.val_mk,dif_neg (show 7+b+j.val≠0 by omega),
      dif_neg (show ¬7+b+j.val<1+t by omega),dif_neg (show ¬7+b+j.val<7 by omega),
      dif_neg (show ¬7+b+j.val<7+t by omega),dif_neg (show ¬7+b+j.val<7+b by omega),
      dif_pos (show 7+b+j.val<7+b+c by omega),k]
  have atD (j : Fin (17-b-c)) :
      f ⟨7+b+c+j.val,by have := j.isLt; omega⟩=(dE j).val := by
    have jj := j.isLt
    have k : (⟨7+b+c+j.val-(7+b+c),by omega⟩ : Fin (17-b-c))=j := by
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
    simp only [f,Fin.val_mk,dif_neg (show 7+b+c+j.val≠0 by omega),
      dif_neg (show ¬7+b+c+j.val<1+t by omega),dif_neg (show ¬7+b+c+j.val<7 by omega),
      dif_neg (show ¬7+b+c+j.val<7+t by omega),dif_neg (show ¬7+b+c+j.val<7+b by omega),
      dif_neg (show ¬7+b+c+j.val<7+b+c by omega),k]
  have sur : Function.Surjective f := by
    intro y
    have r := L.radius y
    have eq : G.dist x y=0 ∨ G.dist x y=1 ∨ G.dist x y=2 ∨
      G.dist x y=3 ∨ G.dist x y=4 := by omega
    rcases eq with h|h|h|h|h
    · have e : x=y := (dist_eq_zero_iff_eq_or_not_reachable.mp h).resolve_right
        (not_not.mpr (hc x y))
      exact ⟨0,atZero.trans e⟩
    · have ym : y ∈ A := mem_shell.mpr h
      by_cases yt : y ∈ L.T
      · obtain ⟨j,hj⟩ := aE.surjective ⟨y,yt⟩
        refine ⟨⟨1+j.val,by omega⟩, (atA j).trans ?_⟩
        exact congrArg Subtype.val hj
      have yy : y ∈ A \ L.T := mem_sdiff.mpr ⟨ym,yt⟩
      obtain ⟨j,hj⟩ := aO.surjective ⟨y,yy⟩
      exact ⟨⟨1+t+j.val,by have := j.isLt; omega⟩, (atAO j).trans (congrArg Subtype.val hj)⟩
    · have ym : y ∈ B := mem_shell.mpr h
      by_cases yu : y ∈ used
      · obtain ⟨z,zt,zy⟩ := mem_image.mp yu
        obtain ⟨j,hj⟩ := aE.surjective ⟨z,zt⟩
        have e : a j = z := congrArg Subtype.val hj
        exact ⟨⟨7+j.val,by omega⟩, (atB j).trans (e.symm ▸ zy)⟩
      have yy : y ∈ B \ used := mem_sdiff.mpr ⟨ym,yu⟩
      obtain ⟨j,hj⟩ := bO.surjective ⟨y,yy⟩
      exact ⟨⟨7+t+j.val,by have := j.isLt; omega⟩, (atBO j).trans (congrArg Subtype.val hj)⟩
    · have ym : y ∈ C := mem_shell.mpr h
      obtain ⟨j,hj⟩ := cE.surjective ⟨y,ym⟩
      exact ⟨⟨7+b+j.val,by have hj := j.isLt; change j.val<c at hj; omega⟩,(atC j).trans (congrArg Subtype.val hj)⟩
    have ym : y ∈ D := mem_shell.mpr h
    obtain ⟨j,hj⟩ := dE.surjective ⟨y,ym⟩
    exact ⟨⟨7+b+c+j.val,by have := j.isLt; omega⟩,(atD j).trans (congrArg Subtype.val hj)⟩
  let e : Fin 24 ≃ V := Equiv.ofBijective f
    ((Fintype.bijective_iff_surjective_and_card f).mpr ⟨sur,by simp [n]⟩)
  have depth (i : Fin 24) : G.dist x (e i) =
      if i.val=0 then 0 else if i.val<7 then 1 else if i.val<7+b then 2 else
      if i.val<7+b+c then 3 else 4 := by
    change G.dist x (f i) = _
    by_cases hi : i.val=0
    · have z : i=0 := Fin.ext hi
      subst i
      simp [atZero,dist_self]
    by_cases h1 : i.val<1+t
    · simp only [f,dif_neg hi,dif_pos h1,if_neg hi,if_pos (show i.val<7 by omega)]
      exact mem_shell.mp (L.selected (am _))
    by_cases h2 : i.val<7
    · simp only [f,dif_neg hi,dif_neg h1,dif_pos h2,if_neg hi,if_pos h2]
      exact mem_shell.mp (mem_sdiff.mp ((aO _).property)).1
    by_cases h3 : i.val<7+t
    · simp only [f,dif_neg hi,dif_neg h1,dif_neg h2,dif_pos h3,if_neg hi,if_neg h2,
        if_pos (show i.val<7+b by omega)]
      exact L.repDepth _ (am _)
    by_cases h4 : i.val<7+b
    · simp only [f,dif_neg hi,dif_neg h1,dif_neg h2,dif_neg h3,dif_pos h4,if_neg hi,if_neg h2,if_pos h4]
      exact mem_shell.mp (mem_sdiff.mp ((bO _).property)).1
    by_cases h5 : i.val<7+b+c
    · simp only [f,dif_neg hi,dif_neg h1,dif_neg h2,dif_neg h3,dif_neg h4,dif_pos h5,
        if_neg hi,if_neg h2,if_neg h4,if_pos h5]
      exact mem_shell.mp (cE _).property
    simp only [f,dif_neg hi,dif_neg h1,dif_neg h2,dif_neg h3,dif_neg h4,dif_neg h5,
      if_neg hi,if_neg h2,if_neg h4,if_neg h5]
    exact mem_shell.mp (dE _).property
  have chooseA (i : Fin 24) (p : 1≤i.val) (q : i.val≤t) :
      e i = a ⟨i.val-1,by omega⟩ := by
    change f i = _
    simp only [f,dif_neg (show i.val≠0 by omega),dif_pos (show i.val<1+t by omega)]
  have chooseB (i j : Fin 24) (p : 1≤i.val) (q : i.val≤t) (r : j.val=6+i.val) :
      e j = L.rep (e i) := by
    rw [chooseA i p q]
    change f j = _
    have hi : (⟨j.val-7,by omega⟩ : Fin t) = ⟨i.val-1,by omega⟩ := by apply Fin.ext; simp only [Fin.val_mk]; omega
    simp only [f,dif_neg (show j.val≠0 by omega),dif_neg (show ¬j.val<1+t by omega),
      dif_neg (show ¬j.val<7 by omega),dif_pos (show j.val<7+t by omega)]
    exact congrArg (L.rep ∘ a) hi
  have cAt (j : Fin 24) (p : 7+b≤j.val) (q : j.val<7+b+c) :
      e j = (cE ⟨j.val-(7+b),by change _<c; omega⟩).val := by
    change f j = _
    simp only [f,dif_neg (show j.val≠0 by omega),dif_neg (show ¬j.val<1+t by omega),
      dif_neg (show ¬j.val<7 by omega),dif_neg (show ¬j.val<7+t by omega),
      dif_neg (show ¬j.val<7+b by omega),dif_pos q]
  refine ⟨e,atZero,depth,?_,chooseA,chooseB,cAt⟩
  · intro i
    constructor
    · intro hi
      have h := mem_shell.mp (L.selected hi)
      have dep := depth i
      have range : 1≤i.val ∧ i.val<7 := by
        split at dep
        · omega
        split at dep
        · omega
        split at dep
        · omega
        split at dep <;> omega
      apply Classical.byContradiction
      intro no
      change ¬ (1≤i.val ∧ i.val≤t) at no
      have hz : ¬i.val=0 := by omega
      have hl : ¬i.val<1+t := by omega
      change f i ∈ L.T at hi
      simp only [f,dif_neg hz,dif_neg hl,dif_pos range.2] at hi
      exact (mem_sdiff.mp (aO _).property).2 hi
    · rintro ⟨p,q⟩
      rw [chooseA i p q]
      exact am _

#print axioms exists_layer_twenty_four_label_from_orders
end Graffiti189LongestPath
