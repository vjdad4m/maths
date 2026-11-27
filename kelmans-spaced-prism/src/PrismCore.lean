import SquareCapGeometry

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.Prism

def core (m : ℕ) (hm : 6 ≤ m) : SimpleGraph (Fin m × Bool) where
  Adj x y := (x.2=y.2 ∧ ((x.1.val+1)%m=y.1.val ∨ (y.1.val+1)%m=x.1.val)) ∨
    (x.1=y.1 ∧ x.2≠y.2)
  symm := fun _ _ h => h.elim (fun h => Or.inl ⟨h.1.symm,h.2.symm⟩)
    (fun h => Or.inr ⟨h.1.symm,h.2.symm⟩)
  loopless := fun x h => by
    rcases h with ⟨_,e|e⟩ | ⟨_,e⟩
    · have hi := x.1.isLt
      by_cases lt : x.1.val+1<m
      · rw [Nat.mod_eq_of_lt lt] at e
        omega
      · rw [show x.1.val+1=m by omega,Nat.mod_self] at e
        omega
    · have hi := x.1.isLt
      by_cases lt : x.1.val+1<m
      · rw [Nat.mod_eq_of_lt lt] at e
        omega
      · rw [show x.1.val+1=m by omega,Nat.mod_self] at e
        omega
    · exact e rfl

instance coreDec (m : ℕ) (hm : 6 ≤ m) : DecidableRel (core m hm).Adj := fun x y =>
  inferInstanceAs (Decidable ((x.2=y.2 ∧ ((x.1.val+1)%m=y.1.val ∨
    (y.1.val+1)%m=x.1.val)) ∨ (x.1=y.1 ∧ x.2≠y.2)))

private theorem bool_other {a b : Bool} (h : a≠b) : b= !a := by
  cases a <;> cases b <;> simp_all

private theorem bool_ne_not (b : Bool) : b≠ !b := by cases b <;> decide

private def nxt {m : ℕ} (hm : 6 ≤ m) (x : Fin m) : Fin m :=
  ⟨(x.val+1)%m,Nat.mod_lt _ (by omega)⟩

private def prv {m : ℕ} (hm : 6 ≤ m) (x : Fin m) : Fin m :=
  ⟨if x.val=0 then m-1 else x.val-1,by have h := x.isLt; split <;> omega⟩

private theorem nxt_prv {m : ℕ} (hm : 6 ≤ m) (x : Fin m) :
    nxt hm (prv hm x)=x := by
  apply Fin.ext
  dsimp [nxt,prv]
  split
  · rw [show m-1+1=m by omega,Nat.mod_self]
    omega
  · rw [show x.val-1+1=x.val by omega,Nat.mod_eq_of_lt x.isLt]

private theorem prv_nxt {m : ℕ} (hm : 6 ≤ m) (x : Fin m) :
    prv hm (nxt hm x)=x := by
  apply Fin.ext
  dsimp [nxt,prv]
  by_cases lt : x.val+1<m
  · rw [Nat.mod_eq_of_lt lt,if_neg (by omega)]
    omega
  · rw [show x.val+1=m by have h:=x.isLt; omega,Nat.mod_self,if_pos rfl]
    have h:=x.isLt
    omega

private theorem no_backtrack {m : ℕ} (hm : 6 ≤ m) (x : Fin m) :
    nxt hm (nxt hm x) ≠ x := by
  intro e
  have h := congrArg Fin.val e
  change ((x.val+1)%m+1)%m=x.val at h
  have hi := x.isLt
  by_cases a : x.val+1<m
  · rw [Nat.mod_eq_of_lt a] at h
    by_cases b : x.val+1+1<m
    · rw [Nat.mod_eq_of_lt b] at h
      omega
    · rw [show x.val+1+1=m by omega,Nat.mod_self] at h
      omega
  · rw [show x.val+1=m by omega,Nat.mod_self,Nat.mod_eq_of_lt (by omega : 0+1<m)] at h
    omega

theorem core_cubic (m : ℕ) (hm : 6 ≤ m) : ∀ x, (core m hm).degree x=3 := by
  intro x
  let R := (nxt hm x.1,x.2)
  let L := (prv hm x.1,x.2)
  let T := (x.1,!x.2)
  have near : (core m hm).neighborFinset x = {R,L,T} := by
    ext y
    rw [mem_neighborFinset]
    constructor
    · intro h
      rcases h with ⟨same,forward|back⟩ | ⟨col,diff⟩
      · exact mem_insert.mpr (Or.inl (Prod.ext (Fin.ext forward.symm) same.symm))
      · have t : nxt hm y.1=x.1 := Fin.ext back
        have e := congrArg (prv hm) t
        rw [prv_nxt] at e
        exact mem_insert.mpr (Or.inr (mem_insert.mpr (Or.inl (Prod.ext e same.symm))))
      · have br : y.2= !x.2 := bool_other diff
        exact mem_insert.mpr (Or.inr (mem_insert.mpr (Or.inr
          (mem_singleton.mpr (Prod.ext col.symm br)))))
    · intro h
      simp only [mem_insert,mem_singleton] at h
      rcases h with rfl|rfl|rfl
      · exact Or.inl ⟨rfl,Or.inl rfl⟩
      · exact Or.inl ⟨rfl,Or.inr (congrArg Fin.val (nxt_prv hm x.1))⟩
      · exact Or.inr ⟨rfl,bool_ne_not x.2⟩
  have rl : R≠L := by
    intro h
    exact no_backtrack hm x.1 ((congrArg (nxt hm ∘ Prod.fst) h).trans (nxt_prv hm x.1))
  have rt : R≠T := by
    intro h
    have e := congrArg Prod.snd h
    change x.2 = !x.2 at e
    exact bool_ne_not x.2 e
  have lt : L≠T := by
    intro h
    have e := congrArg Prod.snd h
    change x.2 = !x.2 at e
    exact bool_ne_not x.2 e
  rw [←card_neighborFinset_eq_degree,near]
  simp [card_insert_of_not_mem,rl,rt,lt]

private theorem mixed_step {m : ℕ} (hm : 6 ≤ m) (f : Fin m → Bool)
    (b : Bool) (yes : ∃ i,f i=b) (no : ∃ i,f i= !b) :
    ∃ i, f i=b ∧ f (nxt hm i)= !b := by
  by_contra! absent
  have mono (i : Fin m) : ∀ h : i.val+1<m,
      (if f i=b then 1 else 0 : ℕ) ≤ (if f ⟨i.val+1,h⟩=b then 1 else 0 : ℕ) := by
    intro h
    by_cases eq : f i=b
    · have z := absent i eq
      have n : nxt hm i=⟨i.val+1,h⟩ := Fin.ext (Nat.mod_eq_of_lt h)
      rw [n] at z
      have bz : f ⟨i.val+1,h⟩=b := by
        have e := bool_other z.symm
        simpa using e
      simp [eq,bz]
    · simp [eq]
  let val (i : Fin m) : ℕ := if f i=b then 1 else 0
  have rise (i j : Fin m) (le : i.val≤j.val) : val i≤val j := by
    obtain ⟨j, hj⟩ := j
    induction j with
    | zero =>
      change i.val ≤ 0 at le
      have e : i=⟨0,hj⟩ := Fin.ext (by change i.val=0; omega)
      rw [e]
    | succ j ih =>
      change i.val ≤ j+1 at le
      by_cases eq : i.val=j+1
      · exact le_of_eq (congrArg val (Fin.ext eq))
      · have h : j<m := by omega
        exact (ih h (by change i.val ≤ j; omega)).trans (mono ⟨j,h⟩ hj)
  let a : Fin m := ⟨0,by omega⟩
  let z : Fin m := ⟨m-1,by omega⟩
  have back : val z≤val a := by
    have e : nxt hm z=a := by
      apply Fin.ext
      change (m-1+1)%m=0
      rw [show m-1+1=m by omega,Nat.mod_self]
    by_cases h : f z=b
    · have nx := absent z h
      rw [e] at nx
      have br : f a=b := by
        have e := bool_other nx.symm
        simpa using e
      simp [val,h,br]
    · simp [val,h]
  obtain ⟨i,hi⟩ := yes
  obtain ⟨j,hj⟩ := no
  have bound : val i≤val j := by
    have iz := rise i z (by have l:=i.isLt; change i.val≤m-1; omega)
    exact iz.trans (back.trans (rise a j (Nat.zero_le _)))
  have opp : (!b)≠b := by cases b <;> decide
  simp [val,hi,hj,opp] at bound

private theorem in_boundary {V : Type*} [Fintype V] {G : SimpleGraph V} {c : V→Bool}
    {e : V×V} : e∈SquareCap.boundary G c ↔ c e.1=true ∧ c e.2=false ∧ G.Adj e.1 e.2 := by
  classical
  simp [SquareCap.boundary]

private abbrev RowPair (m : ℕ) := (Fin m × Bool) × (Fin m × Bool)

private theorem row_two {m : ℕ} (hm : 6≤m) (c : Fin m×Bool→Bool) (row : Bool)
    (mix : (∃ i,c (i,row)=true) ∧ (∃ i,c (i,row)=false)) :
    ∃ E : Finset (RowPair m), E.card=2 ∧ E⊆SquareCap.boundary (core m hm) c ∧
      ∀ e∈E,e.1.2=row ∧ e.2.2=row := by
  obtain ⟨i,it,ine⟩ := mixed_step hm (fun j=>c (j,row)) true mix.1 mix.2
  obtain ⟨j,jt,jne⟩ := mixed_step hm (fun j=>c (j,row)) false mix.2 mix.1
  let A : RowPair m := ((i,row),(nxt hm i,row))
  let B : RowPair m := ((nxt hm j,row),(j,row))
  have ab : A≠B := by
    intro e
    have e1 : i=nxt hm j := congrArg (Prod.fst ∘ Prod.fst) e
    have e2 : nxt hm i=j := congrArg (Prod.fst ∘ Prod.snd) e
    exact no_backtrack hm j (by rwa [←e1])
  have am : A∈SquareCap.boundary (core m hm) c :=
    in_boundary.mpr ⟨it,ine,Or.inl ⟨rfl,Or.inl rfl⟩⟩
  have bm : B∈SquareCap.boundary (core m hm) c :=
    in_boundary.mpr ⟨jne,jt,Or.inl ⟨rfl,Or.inr rfl⟩⟩
  refine ⟨{A,B},by simp [ab],?_,?_⟩
  · intro e h
    simp only [mem_insert,mem_singleton] at h
    rcases h with rfl|rfl <;> assumption
  · intro e h
    simp only [mem_insert,mem_singleton] at h
    rcases h with rfl|rfl <;> exact ⟨rfl,rfl⟩

private def vert {m : ℕ} (c : Fin m×Bool→Bool) (i : Fin m) : RowPair m :=
  if c (i,false) then ((i,false),(i,true)) else ((i,true),(i,false))

private theorem vert_mem {m : ℕ} (hm : 6≤m) (c : Fin m×Bool→Bool) (i : Fin m)
    (h : c (i,false)≠c (i,true)) : vert c i∈SquareCap.boundary (core m hm) c := by
  cases f : c (i,false) <;> cases t : c (i,true)
  · exact (h (f.trans t.symm)).elim
  · exact in_boundary.mpr (by simpa [vert,f] using
      (show c (i,true)=true ∧ c (i,false)=false ∧ (core m hm).Adj (i,true) (i,false)
        from ⟨t,f,Or.inr ⟨rfl,(by decide : true ≠ false)⟩⟩))
  · exact in_boundary.mpr (by simpa [vert,f] using
      (show c (i,false)=true ∧ c (i,true)=false ∧ (core m hm).Adj (i,false) (i,true)
        from ⟨f,t,Or.inr ⟨rfl,(by decide : false ≠ true)⟩⟩))
  · exact (h (f.trans t.symm)).elim

private theorem vert_col {m : ℕ} (c : Fin m×Bool→Bool) (i : Fin m) : (vert c i).1.1=i := by
  unfold vert; split <;> rfl

private theorem vert_diff {m : ℕ} (c : Fin m×Bool→Bool) (i : Fin m) :
    (vert c i).1.2≠(vert c i).2.2 := by
  unfold vert
  split
  · exact (by decide : false≠true)
  · exact (by decide : true≠false)

private theorem flat {m : ℕ} (c : Fin m×Bool→Bool) (b : Bool)
    (no : ¬((∃ i,c (i,b)=true) ∧ (∃ i,c (i,b)=false))) :
    ∃ t,∀ i,c (i,b)=t := by
  by_cases h : ∃ i,c (i,b)=true
  · refine ⟨true,?_⟩
    intro i
    cases e : c (i,b)
    · exact (no ⟨h,⟨i,e⟩⟩).elim
    · rfl
  · refine ⟨false,?_⟩
    intro i
    cases e : c (i,b)
    · rfl
    · exact (h ⟨i,e⟩).elim

private theorem one_flat {m : ℕ} (hm : 6≤m) (c : Fin m×Bool→Bool) (b t : Bool)
    (const : ∀ i,c (i,b)=t)
    (mixed : (∃ i,c (i,!b)=true) ∧ (∃ i,c (i,!b)=false))
    (small : (SquareCap.boundary (core m hm) c).card≤3) :
    ∀ u v,c u= !t → c v= !t → u=v := by
  obtain ⟨E,size,sub,row⟩ := row_two hm c (!b) mixed
  intro u v hu hv
  have bt : t≠ !t := by cases t <;> decide
  have out (x : Fin m×Bool) (hx : c x= !t) : x.2= !b := by
    have nx : x.2≠b := fun e => bt ((const x.1).symm.trans
      ((congrArg (fun j=>c (x.1,j)) e).symm.trans hx))
    exact bool_other nx.symm
  have vx (x : Fin m×Bool) (hx : c x= !t) :
      vert c x.1∈SquareCap.boundary (core m hm) c := by
    apply vert_mem hm c
    have j := out x hx
    have opp : c (x.1,!b)= !t := by
      obtain ⟨i,s⟩ := x
      change s = !b at j
      subst s
      exact hx
    cases b
    · intro e
      exact bt ((const x.1).symm.trans (e.trans opp))
    · intro e
      exact bt ((const x.1).symm.trans (e.symm.trans opp))
  have outside (i : Fin m) : vert c i∉E := by
    intro h
    have e := row _ h
    exact vert_diff c i (e.1.trans e.2.symm)
  have same : u.1=v.1 := by
    refine Classical.byContradiction ?_
    intro ne
    have vv : vert c u.1≠vert c v.1 := fun e =>
      ne ((vert_col c u.1).symm.trans ((congrArg (Prod.fst ∘ Prod.fst) e).trans (vert_col c v.1)))
    have inc : insert (vert c u.1) (insert (vert c v.1) E)⊆SquareCap.boundary (core m hm) c := by
      intro w h
      simp only [mem_insert] at h
      rcases h with rfl|rfl|hh
      · exact vx _ hu
      · exact vx _ hv
      · exact sub hh
    have cards := card_le_card inc
    rw [card_insert_of_not_mem (by simp [vv,outside]),card_insert_of_not_mem (outside _),size] at cards
    omega
  exact Prod.ext same ((out u hu).trans (out v hv).symm)

theorem core_small (m : ℕ) (hm : 6 ≤ m) : SquareCap.SmallTrivial (core m hm) := by
  classical
  intro c small
  let mixed (r : Bool) := (∃ i,c (i,r)=true) ∧ (∃ i,c (i,r)=false)
  by_cases f : mixed false <;> by_cases t : mixed true
  · obtain ⟨E,a,b,e⟩ := row_two hm c false f
    obtain ⟨F,d,g,k⟩ := row_two hm c true t
    have dis : Disjoint E F := disjoint_left.mpr (fun x xe xf =>
      (by decide : false≠true) ((e _ xe).1.symm.trans (k _ xf).1))
    have le := card_le_card (union_subset b g)
    rw [card_union_of_disjoint dis,a,d] at le
    omega
  · obtain ⟨b,h⟩ := flat c true t
    have z := one_flat hm c true b h f small
    cases b
    · exact Or.inl z
    · exact Or.inr z
  · obtain ⟨b,h⟩ := flat c false f
    have z := one_flat hm c false b h t small
    cases b
    · exact Or.inl z
    · exact Or.inr z
  · obtain ⟨a,ha⟩ := flat c false f
    obtain ⟨b,hb⟩ := flat c true t
    have eq : a=b := by
      by_contra ne
      let e : Fin m ↪ RowPair m := ⟨vert c,fun i j eq =>
        (vert_col c i).symm.trans ((congrArg (Prod.fst ∘ Prod.fst) eq).trans (vert_col c j))⟩
      have inc : (univ : Finset (Fin m)).map e⊆SquareCap.boundary (core m hm) c := by
        intro w h
        obtain ⟨i,_,rfl⟩ := mem_map.mp h
        exact vert_mem hm c i (by rw [ha,hb]; exact ne)
      have le := card_le_card inc
      rw [card_map,card_univ,Fintype.card_fin] at le
      omega
    have all (i : Fin m×Bool) : c i=a := by
      obtain ⟨i,row⟩ := i
      cases row
      · exact ha i
      · exact (hb i).trans eq.symm
    cases a
    · left
      intro x _ hx _
      rw [all x] at hx
      contradiction
    · right
      intro x _ hx _
      rw [all x] at hx
      contradiction

#print axioms core_cubic
#print axioms core_small
end KelmansCactus.AtomicBridge.Prism
