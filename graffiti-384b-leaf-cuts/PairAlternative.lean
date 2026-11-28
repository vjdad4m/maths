import ZeroLeaf384b
import IsolateBasic384b
namespace Graffiti384b.OddStars.PairAlternative
open Finset SimpleGraph PositivePalette IsolateBasic
open private TrianglePrune.triangle_iff from TrianglePrune384b
open private Repair.nbr_mono from Repair384b
open private IsolateBasic.minimum from IsolateBasic384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def attach (a b : V) : SimpleGraph (V⊕Unit) where
  Adj
    | .inl x,.inl y => G.Adj x y
    | .inl x,.inr _ => x=a ∨ x=b
    | .inr _,.inl x => x=a ∨ x=b
    | .inr _,.inr _ => False
  symm := by intro x y; cases x <;> cases y <;> first | exact G.adj_symm | exact id
  loopless := by intro x; cases x <;> first | exact G.loopless _ | exact id

instance (a b : V) : DecidableRel (attach G a b).Adj := fun x y => by
  cases x <;> cases y <;> first | exact inferInstanceAs (Decidable (G.Adj _ _)) | exact inferInstanceAs (Decidable (_=_ ∨ _=_)) | exact isFalse (fun h => h)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem unsupported {a b x y : V} (ab : ¬G.Adj a b) (edge : G.Adj x y)
    (px : x=a ∨ x=b) (py : y=a ∨ y=b) : False := by
  rcases px with rfl|rfl <;> rcases py with rfl|rfl <;> first | exact edge.ne rfl | exact ab edge | exact ab edge.symm

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem patch_eq {a b : V} (ab : ¬G.Adj a b) :
    patch (attach G a b) ∅=extend (patch G ∅) := by
  ext x y
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      change (G.Adj x y ∧ _) ↔ G.Adj x y ∧ _
      simp only [Finset.not_mem_empty,or_false,false_or]
      constructor
      · rintro ⟨e,w,u,v⟩
        cases w with
        | inl w => exact ⟨e,w,u,v⟩
        | inr w => exact (unsupported G ab e u v).elim
      · rintro ⟨e,w,u,v⟩; exact ⟨e,Sum.inl w,u,v⟩
    | inr y =>
      simp only [patch,attach,extend,Finset.not_mem_empty,or_false,false_or,iff_false]
      rintro ⟨px,w,u,v⟩; cases w with
      | inl w => exact unsupported G ab u px v
      | inr w => exact v
  | inr x =>
    cases y with
    | inl y =>
      simp only [patch,attach,extend,Finset.not_mem_empty,or_false,false_or,iff_false]
      rintro ⟨py,w,u,v⟩; cases w with
      | inl w => exact unsupported G ab v py u
      | inr w => exact u
    | inr y => simp [patch,attach,extend]

private theorem patch_types (J : SimpleGraph V) [DecidableRel J.Adj] : types (patch J ∅)=types J := by
  unfold types; exact image_congr (fun _ _ => patch_scores ..)

private theorem palette {a b : V} (ab : ¬G.Adj a b) :
    types (attach G a b)=insert 0 (types G) := by
  calc
    _ = types (patch (attach G a b) ∅) := (patch_types _).symm
    _ = types (extend (patch G ∅)) := by congr 1; exact patch_eq G ab
    _ = insert 0 (types (patch G ∅)) := IsolateBasic.palette _
    _ = _ := by rw [patch_types G]

private theorem attached_info {a b : V} (ne : a≠b) (ab : ¬G.Adj a b) :
    (attach G a b).degree (.inr ())=2 ∧ trianglesAt (attach G a b) (.inr ())=0 := by
  have N : (attach G a b).neighborFinset (.inr ())=({a,b}:Finset V).map .inl := by
    ext i; cases i <;> simp [attach]
  constructor
  · rw [←card_neighborFinset_eq_degree,N,card_map,card_pair ne]
  · apply Nat.eq_zero_of_not_pos
    intro pos
    obtain ⟨i,j,zi,zj,ij⟩ := (TrianglePrune.triangle_iff _ _).mp pos
    cases i with
    | inr i => exact zi
    | inl i =>
      cases j with
      | inr j => exact zj
      | inl j => exact unsupported G ab ij zi zj

omit [Fintype V] in
private theorem credits {a b : V} (D : Finset (V⊕Unit)) (v : V) :
    nbr (attach G a b) (.inl v) D=nbr G v D.toLeft +
    (if (.inr () : V⊕Unit)∈D ∧ (v=a ∨ v=b) then 1 else 0) := by
  let F := D.filter ((attach G a b).Adj (.inl v))
  have l : F.toLeft=D.toLeft.filter (G.Adj v) := by ext; simp [F,attach]
  have r : F.toRight=(if (.inr () : V⊕Unit)∈D ∧ (v=a ∨ v=b) then {()} else ∅) := by
    ext y; cases y; by_cases h : (.inr () : V⊕Unit)∈D ∧ (v=a ∨ v=b) <;> simp [F,attach,h]
  have c := card_toLeft_add_card_toRight (u:=F)
  rw [l,r] at c
  change F.card=(D.toLeft.filter (G.Adj v)).card+_
  split <;> rename_i h <;> simpa [h] using c.symm

/-- A nonedge in any catalogue failure is either jointly retained by a minimum
set or admits a one-short set that can be deficient only at its two endpoints. -/
theorem pair_alternative (bad : bound G<gamma G) {a b : V} (ne : a≠b) (ab : ¬G.Adj a b) :
    (∃D,TwoDominates G D ∧ D.card=gamma G ∧ a∈D ∧ b∈D) ∨
    ∃S : Finset V, S.card+1=gamma G ∧ a∉S ∧ b∉S ∧
      (∀v∉S,v≠a → v≠b → 2≤nbr G v S) ∧ 1≤nbr G a S ∧ 1≤nbr G b S ∧
      (nbr G a S=1 ∨ nbr G b S=1) := by
  classical
  let E := attach G a b
  have ⟨de,zz⟩ := attached_info G ne ab
  have boundE := exact_of_zero_nonleaf E zz de.ge
  have zero := (failure_requires_odd_zero G bad).2
  have pal : types E=types G := (palette G ab).trans (insert_eq_of_mem zero)
  have limited : gamma E≤gamma G := by
    unfold bound at bad boundE
    rw [pal,Fintype.card_sum,Fintype.card_unit] at boundE
    have cap : (types G).card≤Fintype.card V := card_image_le.trans_eq card_univ
    omega
  obtain ⟨D,dom,size⟩ := IsolateBasic.minimum E
  let S := D.toLeft
  have credit (x : V) (xo : x∉S) := dom (.inl x) (fun hx => xo (mem_toLeft.mpr hx))
  have cost : S.card+D.toRight.card=D.card := card_toLeft_add_card_toRight
  by_cases z : (.inr () : V⊕Unit)∈D
  · have dr : D.toRight={()} := by ext u; cases u; simpa using z
    rw [dr,card_singleton] at cost
    have short : S.card<gamma G := by omega
    have rest (v : V) (vo : v∉S) (va : v≠a) (vb : v≠b) : 2≤nbr G v S := by
      have h := credit v vo
      rw [credits] at h
      simpa [va,vb,S] using h
    let B := insert a (insert b S)
    have good : TwoDominates G B := by
      intro v vo
      have h : v≠a ∧ v≠b ∧ v∉S := by simpa [B] using vo
      exact (rest v h.2.2 h.1 h.2.1).trans (Repair.nbr_mono G _ (fun _ hm => mem_insert_of_mem (mem_insert_of_mem hm)))
    have minB : gamma G≤B.card := Nat.sInf_le ⟨_,good,rfl⟩
    by_cases joint : B.card=gamma G
    · exact Or.inl ⟨B,good,joint,mem_insert_self ..,mem_insert_of_mem (mem_insert_self ..)⟩
    have outB : b∉S := by
      intro h
      have calcB : B.card≤S.card+1 := by unfold B; rw [insert_eq_of_mem h]; exact card_insert_le ..
      omega
    have outA : a∉S := by
      intro h
      have eq : B=insert b S := insert_eq_of_mem (mem_insert_of_mem h)
      have up := card_insert_le b S
      rw [eq] at minB joint
      omega
    have bc : B.card=S.card+2 := by
      simp [B,card_insert_of_not_mem,outA,outB,ne]
    have one (v : V) (vo : v∉S) : 1≤nbr G v S := by
      have h := credit v vo
      rw [credits] at h
      change 1≤nbr G v D.toLeft
      split at h <;> omega
    have either : nbr G a S=1 ∨ nbr G b S=1 := by
      by_contra! contra
      have full : TwoDominates G S := by
        intro v out
        by_cases va : v=a
        · subst v; have := one a outA; omega
        by_cases vb : v=b
        · subst v; have := one b outB; omega
        exact rest v out va vb
      have lower : gamma G≤S.card := Nat.sInf_le ⟨_,full,rfl⟩
      omega
    exact Or.inr ⟨S,by omega,outA,outB,rest,one _ outA,one _ outB,either⟩
  · have full : TwoDominates G S := by
      intro v out
      have h := credit v out
      rw [credits] at h
      simpa [z,S] using h
    have both : a∈S ∧ b∈S := by
      have h := dom _ z
      have f : D.filter (E.Adj (.inr ()))=(S∩{a,b}).map .inl := by
        ext i; cases i <;> simp [S,E,attach,and_assoc]
      change 2≤(D.filter (E.Adj (.inr ()))).card at h
      rw [f,card_map] at h
      have eq := eq_of_subset_of_card_le (inter_subset_right (s₁:=S) (s₂:=({a,b}:Finset V))) (by rwa [card_pair ne])
      exact ⟨(mem_inter.mp (eq ▸ mem_insert_self ..)).1,(mem_inter.mp (eq ▸ mem_insert_of_mem (mem_singleton_self _))).1⟩
    have minS : gamma G≤S.card := Nat.sInf_le ⟨_,full,rfl⟩
    exact Or.inl ⟨S,full,by omega,both⟩
end Graffiti384b.OddStars.PairAlternative
#print axioms Graffiti384b.OddStars.PairAlternative.pair_alternative
