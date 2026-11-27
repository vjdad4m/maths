import CyclicT2
import HandleExtension

open SimpleGraph Finset
namespace KelmansCactus.AtomicBridge.DominoGadget
open HandleExtension FourRingCutAux FourRingReplica.Layout FourRingCyclicEquivalence
noncomputable section
variable {U : Type*} {G : SimpleGraph U} {x : U}

structure Seed (G : SimpleGraph U) (x : U) where
  a : U
  b : U
  d : U
  w : U
  xa : G.Adj x a
  xd : G.Adj x d
  ab : G.Adj a b
  aw : G.Adj a w
  dx : d≠x
  da : d≠a
  dw : d≠w
  wx : w≠x
  bx : b≠x
  bw : b≠w
  exactA : ∀ u,G.Adj a u → u=x ∨ u=b ∨ u=w

variable (S : Seed G x)

abbrev Steps U := (U⊕Bool)⊕Bool
abbrev Rest (x : U) := {v : U // v≠x}

def first : Edges G where
  a s := if s then S.a else x
  b s := if s then S.w else S.d
  edge := by
    intro s
    cases s
    · exact S.xd
    · exact S.aw
  separated := by
    intro s t v hs ht
    cases s <;> cases t
    · rfl
    · rcases hs with h|h <;> rcases ht with k|k
      · exact (S.xa.ne (h.symm.trans k)).elim
      · exact (S.wx (k.symm.trans h)).elim
      · exact (S.da (h.symm.trans k)).elim
      · exact (S.dw (h.symm.trans k)).elim
    · rcases hs with h|h <;> rcases ht with k|k
      · exact (S.xa.ne (k.symm.trans h)).elim
      · exact (S.da (k.symm.trans h)).elim
      · exact (S.wx (h.symm.trans k)).elim
      · exact (S.dw (k.symm.trans h)).elim
    · rfl

private theorem removed_xa_false : ¬(first S).Removed x S.a := by
  rintro ⟨k,h⟩
  cases k
  · rcases h with ⟨_,b⟩|⟨a,_⟩
    · exact S.da b.symm
    · exact S.dx a.symm
  · rcases h with ⟨a,_⟩|⟨a,_⟩
    · exact S.xa.ne a
    · exact S.wx a.symm

def second : Edges (first S).host where
  a s := if s then Sum.inr false else Sum.inl x
  b s := if s then Sum.inr true else Sum.inl S.a
  edge := by
    intro s
    cases s
    · exact ⟨S.xa,removed_xa_false S⟩
    · exact Bool.false_ne_true
  separated := by
    intro s t v hs ht
    cases s <;> cases t
    · rfl
    · rcases hs with h|h <;> rcases ht with k|k <;>
        have e := h.symm.trans k <;> cases e
    · rcases hs with h|h <;> rcases ht with k|k <;>
        have e := h.symm.trans k <;> cases e
    · rfl

def X : Steps U := Sum.inl (Sum.inl x)
def Y : Steps U := Sum.inl (Sum.inr false)
def pp : Steps U := Sum.inl (Sum.inl S.a)
def qq : Steps U := Sum.inr false
def rr : Steps U := Sum.inr true
def root (x : U) (b : Bool) : Steps U :=
  if b then Y (U:=U) else X (x:=x)

theorem roots_adjacent : (second S).host.Adj (root x false) (root x true) := by
  refine ⟨?_,?_⟩
  · exact Or.inl rfl
  · rintro ⟨j,e⟩
    cases j <;> rcases e with h|h <;> rcases h with ⟨v,w⟩
    · cases w
    · cases w
    · cases v
    · cases v

variable [DecidableEq U]

def original (u : Rest x) : Steps U :=
  if u.val=S.a then Sum.inl (Sum.inr true) else Sum.inl (Sum.inl u.val)

def extra (i : Fin 3) : Steps U :=
  if i=0 then pp S else if i=1 then qq else rr

def combined : Rest x ⊕ Fin 3 → Steps U
  | .inl u => original S u
  | .inr i => extra S i

omit [DecidableEq U] in
theorem old_a_relabel : (show Rest x from ⟨S.a,S.xa.ne.symm⟩).val=S.a := rfl

private theorem combined_survives (v : Rest x⊕Fin 3) :
    combined S v≠root x false ∧ combined S v≠root x true := by
  cases v with
  | inl u => by_cases ua : u.val=S.a <;> simp [combined,original,ua,root,X,Y,u.property]
  | inr i => fin_cases i <;> simp [combined,extra,pp,qq,rr,root,X,Y,S.xa.ne.symm]

private theorem combined_injective : Function.Injective (combined S) := by
  rintro (u|i) (v|j) e
  · apply congrArg Sum.inl
    apply Subtype.ext
    by_cases hu : u.val=S.a <;> by_cases hv : v.val=S.a
    · exact hu.trans hv.symm
    · simp [combined,original,hu,hv] at e
    · simp [combined,original,hu,hv] at e
    · simpa [combined,original,hu,hv] using e
  · by_cases hu : u.val=S.a <;> fin_cases j <;> simp [combined,original,extra,hu,pp,qq,rr] at e
  · by_cases hv : v.val=S.a <;> fin_cases i <;> simp [combined,original,extra,hv,pp,qq,rr] at e
    exact (hv e.symm).elim
  · fin_cases i <;> fin_cases j <;> simp_all [combined,extra,pp,qq,rr]

def embed : Rest x⊕Fin 3 ≃ FourRingReplica.Piece (root x) :=
  Equiv.ofBijective (fun v=>⟨combined S v,combined_survives S v⟩) (by
    constructor
    · exact fun _ _ e=>combined_injective S (congrArg Subtype.val e)
    · rintro ⟨((u|j)|s),notX,notY⟩
      · by_cases ua : u=S.a
        · exact ⟨Sum.inr 0,Subtype.ext (by simp [combined,extra,pp,ua])⟩
        · have ux : u≠x := fun h=>notX (by simp [root,X,h])
          exact ⟨Sum.inl ⟨u,ux⟩,Subtype.ext (by simp [combined,original,ua])⟩
      · cases j
        · exact (notY rfl).elim
        · exact ⟨Sum.inl ⟨S.a,S.xa.ne.symm⟩,Subtype.ext (by simp [combined,original])⟩
      · cases s
        · exact ⟨Sum.inr 1,Subtype.ext (by simp [combined,extra,qq])⟩
        · exact ⟨Sum.inr 2,Subtype.ext (by simp [combined,extra,rr])⟩)

def reduced : SimpleGraph (Rest x⊕Fin 3) :=
  (minor (second S).host (root x)).comap (embed S)

abbrev oldGraph (G : SimpleGraph U) (x : U) : SimpleGraph (Rest x) := G.comap Subtype.val

private theorem old_to_old (u v : Rest x) :
    (reduced S).Adj (Sum.inl u) (Sum.inl v) → (oldGraph G x).Adj u v := by
  intro e
  change (second S).host.Adj (original S u) (original S v) at e
  by_cases hu : u.val=S.a <;> by_cases hv : v.val=S.a
  · have h : u=v := Subtype.ext (hu.trans hv.symm)
    subst v
    exact ((second S).host.loopless _ e).elim
  · change G.Adj u.val v.val
    rw [hu]
    have f : (first S).host.Adj (Sum.inr true) (Sum.inl v.val) := by
      simp only [original,hu,hv,if_true,if_false] at e
      exact e.1
    rcases f with a|w
    · exact (hv a).elim
    · rw [w]
      exact S.aw
  · change G.Adj u.val v.val
    rw [hv]
    have f : (first S).host.Adj (Sum.inl u.val) (Sum.inr true) := by
      simp only [original,hu,hv,if_true,if_false] at e
      exact e.1
    rcases f with a|w
    · exact (hu a).elim
    · rw [w]
      exact S.aw.symm
  · simp only [original,hu,hv,if_true,if_false] at e
    exact e.1.1

private theorem p_contact (v : Rest x) :
    (reduced S).Adj (Sum.inr 0) (Sum.inl v) ↔ v.val=S.a ∨ v.val=S.b := by
  change (second S).host.Adj (pp S) (original S v) ↔ _
  by_cases vA : v.val=S.a
  · constructor
    · exact fun _=>Or.inl vA
    · intro _
      rw [original,if_pos vA]
      refine ⟨Or.inl rfl,?_⟩
      rintro ⟨k,h⟩
      cases k
      · rcases h with ⟨u,z⟩|⟨u,z⟩ <;> cases z
      · rcases h with ⟨u,_⟩|⟨u,_⟩ <;> cases u
  · rw [original,if_neg vA]
    constructor
    · intro h
      have ed : G.Adj S.a v.val := h.1.1
      have gone : ¬(first S).Removed S.a v.val := h.1.2
      rcases S.exactA _ ed with xV|bV|wV
      · exact (v.property xV).elim
      · exact Or.inr bV
      · exact (gone ⟨true,Or.inl ⟨rfl,wV⟩⟩).elim
    · rintro (h|bV)
      · exact (vA h).elim
      rw [bV]
      refine ⟨⟨S.ab,?_⟩,?_⟩
      · rintro ⟨j,h⟩
        cases j
        · rcases h with ⟨u,_⟩|⟨u,_⟩
          · exact S.xa.ne u.symm
          · exact S.da u.symm
        · rcases h with ⟨_,z⟩|⟨u,_⟩
          · exact S.bw z
          · exact S.aw.ne u
      · rintro ⟨j,h⟩
        cases j
        · rcases h with ⟨u,_⟩|⟨_,z⟩
          · exact S.xa.ne (Sum.inl.inj u).symm
          · exact S.bx (Sum.inl.inj z)
        · rcases h with ⟨u,_⟩|⟨u,_⟩ <;> cases u

private theorem q_contact (v : Rest x) :
    ¬(reduced S).Adj (Sum.inr 1) (Sum.inl v) := by
  change ¬(second S).host.Adj qq (original S v)
  unfold original
  split <;> intro h
  · rcases h with a|a <;> cases a
  · rcases h with a|a
    · exact v.property (Sum.inl.inj a)
    · rename_i n; exact n (Sum.inl.inj a)

private theorem r_contact (v : Rest x) :
    (reduced S).Adj (Sum.inr 2) (Sum.inl v) ↔ v.val=S.a := by
  change (second S).host.Adj rr (original S v) ↔ _
  by_cases a : v.val=S.a
  · simp only [original,a,if_true]
    exact ⟨fun _=>trivial,fun _=>Or.inr rfl⟩
  · simp only [original,a,if_false,iff_false]
    rintro (a|a) <;> cases a

theorem residual_shape :
    (∀u v,(reduced S).Adj (.inl u) (.inl v) → (oldGraph G x).Adj u v) ∧
    (∀v,(reduced S).Adj (.inr 0) (.inl v) ↔ v=⟨S.a,S.xa.ne.symm⟩ ∨ v=⟨S.b,S.bx⟩) ∧
    (∀v,¬(reduced S).Adj (.inr 1) (.inl v)) ∧
    (∀v,(reduced S).Adj (.inr 2) (.inl v) ↔ v=⟨S.a,S.xa.ne.symm⟩) ∧
    (reduced S).Adj (.inr 0) (.inr 1) ∧
    (reduced S).Adj (.inr 1) (.inr 2) ∧
    ¬(reduced S).Adj (.inr 0) (.inr 2) := by
  refine ⟨old_to_old S,?_,q_contact S,?_,?_,?_,?_⟩
  · intro v
    rw [p_contact]
    simp only [Subtype.ext_iff]
  · intro v
    rw [r_contact]
    simp only [Subtype.ext_iff]
  · exact Or.inr rfl
  · exact Bool.false_ne_true
  · intro h
    rcases h with a|a <;> cases a

#print axioms roots_adjacent
#print axioms residual_shape
end
end KelmansCactus.AtomicBridge.DominoGadget
