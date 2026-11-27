import P5CliqueFourRelayArmFans133

namespace Graffiti133P5CliqueArms
open SimpleGraph Finset Graffiti133Camby Graffiti133
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem high_client_singleton_four_port_has_fan
    (h4 : FourCycleFree G) (D : Finset V) (p : Fin 4→V)
    (pm : ∀ i,p i∈D) (pi : Function.Injective p)
    (attach : ∀ q∉D,∃ i,G.Adj q (p i))
    (palette : ∀ q∉D,∀ w∈D,G.Adj q w→∃ i,w=p i)
    (single : ∀ q∉D,∀ i,G.Adj q (p i)→∀ w∈D,G.Adj q w↔w=p i)
    (q : V) (qo : q∉D) (qa : G.Adj q (p 0)) (high : 3<localIndependence G q) :
      ∃ fn : Fin 4→V,fn 0=q ∧
        (∀ i,fn i∉D) ∧
        (∀ i x,x∈D→(G.Adj (fn i) x↔x=p i)) ∧
        ∀ i j,i<j→(G.Adj (fn i) (fn j)↔i=0) := by
  classical
  let P := (Finset.univ : Finset (Fin 4)).image p
  have p4 : P.card=4 := by rw [Finset.card_image_of_injective _ pi,Finset.card_univ]; decide
  choose lab hlab using attach
  let tag (q : V) := if h : q∉D then p (lab q h) else q
  have pick (q : V) (qo : q∉D) : tag q∈D ∧ tag q∈P ∧ G.Adj q (tag q) := by
    have e : tag q=p (lab q qo) := dif_pos qo
    rw [e]
    exact ⟨pm _,Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩,hlab q qo⟩
  have ne : (localIndependentSets G q).Nonempty := by
    refine ⟨∅,?_⟩
    simp [localIndependentSets]
  obtain ⟨S,hS,sval⟩ := Finset.exists_mem_eq_sup _ ne Finset.card
  have sc : S.card≥4 := by
    change localIndependence G q=S.card at sval
    omega
  have info : (∀ x∈S,G.Adj q x) ∧ (∀ x∈S,∀ y∈S,¬G.Adj x y) := by
    simpa only [localIndependentSets,Finset.mem_filter,Finset.mem_powerset,
      Finset.subset_iff,Finset.mem_univ,true_and] using hS
  let g (x : V) := if x∈D then x else tag x
  have hit (x : V) (xm : x∈S) : g x∈P := by
    by_cases xd : x∈D
    · obtain ⟨i,ix⟩ := palette q qo x xd (info.1 _ xm)
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,by simpa only [g,if_pos xd] using ix.symm⟩
    · simpa only [g,if_neg xd] using (pick x xd).2.1
  have inj : Set.InjOn g (S : Set V) := by
    intro v vm w wm e
    by_cases vd : v∈D
    · by_cases wd : w∈D
      · simpa only [g,if_pos vd,if_pos wd] using e
      simp only [g,if_pos vd,if_neg wd] at e
      exact ((info.2 w wm v vm) (e.symm ▸ (pick w wd).2.2)).elim
    by_cases wd : w∈D
    · simp only [g,if_neg vd,if_pos wd] at e
      exact ((info.2 v vm w wm) (e ▸ (pick v vd).2.2)).elim
    simp only [g,if_neg vd,if_neg wd] at e
    have qn : q≠tag v := fun eq=>qo (eq.symm ▸ (pick v vd).1)
    exact h4 q (tag v) v w qn (info.1 _ vm) (pick v vd).2.2.symm
      (info.1 _ wm) (e.symm ▸ (pick w wd).2.2).symm
  have sub : S.image g⊆P := by
    intro v vm
    obtain ⟨w,wm,rfl⟩ := Finset.mem_image.mp vm
    exact hit w wm
  have im := Finset.card_image_of_injOn inj
  have eq : S.image g=P := Finset.eq_of_subset_of_card_le sub (by omega)
  have repr (i : Fin 4) (i0 : i≠0) : ∃ x∈S,x∉D ∧ G.Adj x (p i) := by
    have M : p i∈S.image g := eq.symm ▸ Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
    obtain ⟨x,xS,xg⟩ := Finset.mem_image.mp M
    have xo : x∉D := by
      intro xm
      have xp : x=p 0 := (single q qo 0 qa x xm).mp (info.1 _ xS)
      simp only [g,if_pos xm] at xg
      exact i0 (pi (xg.symm.trans xp))
    simp only [g,if_neg xo] at xg
    exact ⟨x,xS,xo,xg ▸ (pick x xo).2.2⟩
  choose v vS vo va using repr
  let fn (i : Fin 4) := if h : i=0 then q else v i h
  have z : fn 0=q := dif_pos rfl
  have s (i : Fin 4) (i0 : i≠0) : fn i=v i i0 := dif_neg i0
  have out (i : Fin 4) : fn i∉D := by
    by_cases e : i=0
    · subst i
      simpa only [z] using qo
    · rw [s i e]
      exact vo i e
  have ea (i : Fin 4) : G.Adj (fn i) (p i) := by
    by_cases e : i=0
    · subst i
      simpa only [z] using qa
    · rw [s i e]
      exact va i e
  refine ⟨fn,z,out,fun i=>single _ (out i) i (ea i),?_⟩
  intro i j ij
  have j0 : j≠0 := by
    intro e
    subst j
    exact (not_lt_of_ge (Fin.zero_le i)) ij
  by_cases i0 : i=0
  · subst i
    rw [z,s j j0]
    exact ⟨fun _=>rfl,fun _=>info.1 _ (vS j j0)⟩
  · rw [s i i0,s j j0]
    exact ⟨fun e=>(info.2 _ (vS i i0) _ (vS j j0) e).elim,fun e=>(i0 e).elim⟩

#print axioms high_client_singleton_four_port_has_fan
private theorem near_three_arm_path9_of_ordered_adjacency (f : Fin 9→V)
    (h : ∀ i j, i<j → (G.Adj (f i) (f j) ↔ i.val+1=j.val)) : InducedPath G f := by
  refine ⟨?_,h⟩
  have noEq (i j : Fin 9) (lt : i<j) : f i≠f j := by
    have lij : i.val<j.val := lt
    intro e
    by_cases near : i.val+1=j.val
    · exact G.loopless _ (e ▸ (h i j lt).mpr near)
    by_cases gap : i.val+2=j.val
    · by_cases iz : i.val=0
      · let k : Fin 9 := ⟨j.val+1,by omega⟩
        have jk : j < k := by change j.val < j.val+1; omega
        have ik : i < k := lt.trans jk
        have adj : G.Adj (f i) (f k) := e.symm ▸ (h j k jk).mpr rfl
        have eq := (h i k ik).mp adj
        change i.val+1=j.val+1 at eq
        omega
      · let k : Fin 9 := ⟨i.val-1,by omega⟩
        have ki : k < i := by change i.val-1 < i.val; omega
        have kj : k < j := ki.trans lt
        have adj : G.Adj (f k) (f j) := e ▸ (h k i ki).mpr (by change (i.val-1)+1=i.val; omega)
        have eq := (h k j kj).mp adj
        change (i.val-1)+1=j.val at eq
        omega
    · let k : Fin 9 := ⟨i.val+1,by omega⟩
      have ik : i < k := by change i.val < i.val+1; omega
      have kj : k < j := by change i.val+1 < j.val; omega
      have adj : G.Adj (f k) (f j) := e ▸ ((h i k ik).mpr rfl).symm
      have eq := (h k j kj).mp adj
      change i.val+1+1=j.val at eq
      omega
  intro i j e
  rcases lt_trichotomy i j with a|a|a
  · exact (noEq i j a e).elim
  · exact a
  · exact (noEq j i a e.symm).elim

theorem high_near_three_port_on_first_two_arm_vertices
    (h4 : FourCycleFree G) (D : Finset V) (p : Fin 4→V)
    (pm : ∀ i,p i∈D) (pi : Function.Injective p)
    (t : V) (tn : ∀ i,t≠p i)
    (near : ((Finset.univ : Finset (Fin 4)).filter (fun i=>G.Adj t (p i))).card≥3)
    (indep : ∀ i j,¬G.Adj (p i) (p j))
    (attach : ∀ q∉D,∃ i,G.Adj q (p i))
    (palette : ∀ q∉D,∀ w∈D,G.Adj q w→∃ i,w=p i)
    (single : ∀ q∉D,∀ i,G.Adj q (p i)→∀ w∈D,G.Adj q w↔w=p i)
    (A : Fin 5→V) (ar : InducedPath G A) (aD : ∀ j,A j∈D) (a0 : A 0=t)
    (far : ∀ i j,G.Adj t (p i)→3≤j.val →¬G.Adj (p i) (A j))
    (farNe : ∀ i j,3≤j.val→A j≠p i)
    (h9 : NoPath G 9)
    (q : V) (qo : q∉D) (qa : G.Adj q (p 0)) (high : 3<localIndependence G q) :
    p 0=A 1 ∨ p 0=A 2 := by
  classical
  by_cases p01 : p 0=A 1
  · exact Or.inl p01
  by_cases p02 : p 0=A 2
  · exact Or.inr p02
  exfalso
  obtain ⟨f,center,fout,only,star⟩ := high_client_singleton_four_port_has_fan h4 D p pm pi
    attach palette single q qo qa high
  have edgeA (i j : Fin 5) (ij : i<j) (hc : i.val+1=j.val) : G.Adj (A i) (A j) :=
    (ar.2 i j ij).mpr hc
  have noedgeA (i j : Fin 5) (ij : i<j) (hc : i.val+1≠j.val) : ¬G.Adj (A i) (A j) :=
    fun e=>hc ((ar.2 i j ij).mp e)
  have notPort0 (i : Fin 4) : A 0≠p i := fun e=>tn i (a0.symm.trans e)
  have notPort3 (i : Fin 4) : A 3≠p i := farNe i 3 (by decide)
  have notPort4 (i : Fin 4) : A 4≠p i := farNe i 4 (by decide)
  let N := (Finset.univ : Finset (Fin 4)).filter (fun i=>G.Adj t (p i))
  let U := N.erase 0
  have u2 : 2≤U.card := by
    have le := Finset.pred_card_le_card_erase (s:=N) (a:=0)
    change 3≤N.card at near
    change 2≤(N.erase 0).card
    omega
  let Bad := U.filter (fun i=>A 1=p i ∨ G.Adj (A 1) (p i))
  have b1 : Bad.card≤1 := by
    apply Finset.card_le_one.mpr
    intro i im j jm
    obtain ⟨iu,bi⟩ := Finset.mem_filter.mp im
    obtain ⟨ju,bj⟩ := Finset.mem_filter.mp jm
    have ti := (Finset.mem_filter.mp (Finset.mem_erase.mp iu).2).2
    have tj := (Finset.mem_filter.mp (Finset.mem_erase.mp ju).2).2
    rcases bi with ei|ei <;> rcases bj with ej|ej
    · exact pi (ei.symm.trans ej)
    · exact (indep i j (ei ▸ ej)).elim
    · exact (indep j i (ej ▸ ei)).elim
    · apply pi
      exact h4 t (A 1) (p i) (p j)
        (fun e=>(by decide : (0:Fin 5)≠1) (ar.1 (a0.trans e))) ti ei tj ej
  obtain ⟨i,im⟩ := Finset.sdiff_nonempty_of_card_lt_card (show Bad.card<U.card by omega)
  obtain ⟨iu,ib⟩ := Finset.mem_sdiff.mp im
  obtain ⟨i0,iN⟩ := Finset.mem_erase.mp iu
  have ti : G.Adj t (p i) := (Finset.mem_filter.mp iN).2
  have inEQ : A 1≠p i := fun e=>ib (Finset.mem_filter.mpr ⟨iu,Or.inl e⟩)
  have inAD : ¬G.Adj (A 1) (p i) := fun e=>ib (Finset.mem_filter.mpr ⟨iu,Or.inr e⟩)
  have i2 : A 2≠p i := fun e=>noedgeA 0 2 (by decide) (by decide) (a0.symm ▸ (e.symm ▸ ti))
  let F := (Finset.univ : Finset (Fin 4)).erase 0
  have F3 : F.card=3 := by decide
  have iF : i∈F := Finset.mem_erase.mpr ⟨i0,Finset.mem_univ _⟩
  let BadTail := (Finset.univ : Finset (Fin 4)).filter (fun j=>A 1=p j ∨ A 2=p j)
  have tail1 : BadTail.card≤1 := by
    apply Finset.card_le_one.mpr
    intro x xm y ym
    rcases (Finset.mem_filter.mp xm).2 with ex|ex <;> rcases (Finset.mem_filter.mp ym).2 with ey|ey
    · exact pi (ex.symm.trans ey)
    · exact (indep x y (ex ▸ (ey ▸ edgeA 1 2 (by decide) (by decide)))).elim
    · exact (indep y x (ey ▸ (ex ▸ edgeA 1 2 (by decide) (by decide)))).elim
    · exact pi (ex.symm.trans ey)
  have f2 := Finset.card_erase_add_one iF
  obtain ⟨j,jm⟩ := Finset.sdiff_nonempty_of_card_lt_card (show BadTail.card<(F.erase i).card by omega)
  obtain ⟨jf,jb⟩ := Finset.mem_sdiff.mp jm
  obtain ⟨ji,jF⟩ := Finset.mem_erase.mp jf
  have j0 : j≠0 := (Finset.mem_erase.mp jF).1
  have ij : i≠j := ji.symm
  have jnEQ : A 1≠p j := fun e=>jb (Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inl e⟩)
  have j2 : A 2≠p j := fun e=>jb (Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inr e⟩)
  have nearport : G.Adj (A 0) (p i) := a0.symm ▸ ti
  have pno1 : ¬G.Adj (A 1) (p i) := inAD
  have pno2 : ¬G.Adj (A 2) (p i) := by
    intro adj
    have eq := h4 (A 0) (A 2) (A 1) (p i)
      (fun e=>(by decide : (0:Fin 5)≠2) (ar.1 e))
      (edgeA 0 1 (by decide) (by decide)) (edgeA 1 2 (by decide) (by decide)).symm
      (a0.symm ▸ ti) adj
    exact inEQ eq
  have outer01 (k : Fin 4) (k0 : k≠0) : G.Adj (f 0) (f k) :=
    (star 0 k (Fin.pos_iff_ne_zero.mpr k0)).mpr rfl
  have leaves : ¬G.Adj (f i) (f j) := by
    rcases lt_trichotomy i j with e|e|e
    · exact fun h=>i0 ((star i j e).mp h)
    · exact (ij e).elim
    · exact fun h=>j0 ((star j i e).mp h.symm)
  have near0 (l : Fin 4) : ¬G.Adj (A 0) (f l) :=
    fun e=>notPort0 l ((only l _ (aD 0)).mp e.symm)
  have near2 (l : Fin 4) (h : A 2≠p l) : ¬G.Adj (A 2) (f l) :=
    fun e=>h ((only l _ (aD 2)).mp e.symm)
  have near3 (l : Fin 4) : ¬G.Adj (A 3) (f l) :=
    fun e=>notPort3 l ((only l _ (aD 3)).mp e.symm)
  have near4 (l : Fin 4) : ¬G.Adj (A 4) (f l) :=
    fun e=>notPort4 l ((only l _ (aD 4)).mp e.symm)
  have near1i : ¬G.Adj (A 1) (f i) := fun e=>inEQ ((only i _ (aD 1)).mp e.symm)
  have near1j : ¬G.Adj (A 1) (f j) := fun e=>jnEQ ((only j _ (aD 1)).mp e.symm)
  have near10 : ¬G.Adj (A 1) (f 0) := fun e=>p01 ((only 0 _ (aD 1)).mp e.symm).symm
  apply h9
  let path : Fin 9→V := ![A 4,A 3,A 2,A 1,A 0,p i,f i,f 0,f j]
  refine ⟨path,near_three_arm_path9_of_ordered_adjacency path ?_⟩
  intro u v
  fin_cases u <;> fin_cases v <;> intro ord <;> try (exfalso; exact (by decide : ¬ _ < _) ord)
  · exact ⟨fun _=>by decide,fun _=>(edgeA 3 4 (by decide) (by decide)).symm⟩
  · exact ⟨fun e=>(fun h=>noedgeA 2 4 (by decide) (by decide) h.symm : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((0:Fin 9).val+1=(2:Fin 9).val)) e).elim⟩
  · exact ⟨fun e=>(fun h=>noedgeA 1 4 (by decide) (by decide) h.symm : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((0:Fin 9).val+1=(3:Fin 9).val)) e).elim⟩
  · exact ⟨fun e=>(fun h=>noedgeA 0 4 (by decide) (by decide) h.symm : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((0:Fin 9).val+1=(4:Fin 9).val)) e).elim⟩
  · exact ⟨fun e=>(fun h=>far i 4 ti (by decide) h.symm : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((0:Fin 9).val+1=(5:Fin 9).val)) e).elim⟩
  · exact ⟨fun e=>(near4 i : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((0:Fin 9).val+1=(6:Fin 9).val)) e).elim⟩
  · exact ⟨fun e=>(near4 0 : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((0:Fin 9).val+1=(7:Fin 9).val)) e).elim⟩
  · exact ⟨fun e=>(near4 j : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((0:Fin 9).val+1=(8:Fin 9).val)) e).elim⟩
  · exact ⟨fun _=>by decide,fun _=>(edgeA 2 3 (by decide) (by decide)).symm⟩
  · exact ⟨fun e=>(fun h=>noedgeA 1 3 (by decide) (by decide) h.symm : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((1:Fin 9).val+1=(3:Fin 9).val)) e).elim⟩
  · exact ⟨fun e=>(fun h=>noedgeA 0 3 (by decide) (by decide) h.symm : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((1:Fin 9).val+1=(4:Fin 9).val)) e).elim⟩
  · exact ⟨fun e=>(fun h=>far i 3 ti (by decide) h.symm : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((1:Fin 9).val+1=(5:Fin 9).val)) e).elim⟩
  · exact ⟨fun e=>(near3 i : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((1:Fin 9).val+1=(6:Fin 9).val)) e).elim⟩
  · exact ⟨fun e=>(near3 0 : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((1:Fin 9).val+1=(7:Fin 9).val)) e).elim⟩
  · exact ⟨fun e=>(near3 j : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((1:Fin 9).val+1=(8:Fin 9).val)) e).elim⟩
  · exact ⟨fun _=>by decide,fun _=>(edgeA 1 2 (by decide) (by decide)).symm⟩
  · exact ⟨fun e=>(fun h=>noedgeA 0 2 (by decide) (by decide) h.symm : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((2:Fin 9).val+1=(4:Fin 9).val)) e).elim⟩
  · exact ⟨fun e=>(pno2 : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((2:Fin 9).val+1=(5:Fin 9).val)) e).elim⟩
  · exact ⟨fun e=>(near2 i i2 : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((2:Fin 9).val+1=(6:Fin 9).val)) e).elim⟩
  · exact ⟨fun e=>(near2 0 (fun e=>p02 e.symm) : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((2:Fin 9).val+1=(7:Fin 9).val)) e).elim⟩
  · exact ⟨fun e=>(near2 j j2 : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((2:Fin 9).val+1=(8:Fin 9).val)) e).elim⟩
  · exact ⟨fun _=>by decide,fun _=>(edgeA 0 1 (by decide) (by decide)).symm⟩
  · exact ⟨fun e=>(pno1 : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((3:Fin 9).val+1=(5:Fin 9).val)) e).elim⟩
  · exact ⟨fun e=>(near1i : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((3:Fin 9).val+1=(6:Fin 9).val)) e).elim⟩
  · exact ⟨fun e=>(near10 : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((3:Fin 9).val+1=(7:Fin 9).val)) e).elim⟩
  · exact ⟨fun e=>(near1j : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((3:Fin 9).val+1=(8:Fin 9).val)) e).elim⟩
  · exact ⟨fun _=>by decide,fun _=>nearport⟩
  · exact ⟨fun e=>(near0 i : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((4:Fin 9).val+1=(6:Fin 9).val)) e).elim⟩
  · exact ⟨fun e=>(near0 0 : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((4:Fin 9).val+1=(7:Fin 9).val)) e).elim⟩
  · exact ⟨fun e=>(near0 j : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((4:Fin 9).val+1=(8:Fin 9).val)) e).elim⟩
  · exact ⟨fun _=>by decide,fun _=>((only i (p i) (pm i)).mpr rfl).symm⟩
  · exact ⟨fun e=>(fun h=>i0 (pi ((only 0 (p i) (pm i)).mp h.symm)) : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((5:Fin 9).val+1=(7:Fin 9).val)) e).elim⟩
  · exact ⟨fun e=>(fun h=>ij (pi ((only j (p i) (pm i)).mp h.symm)) : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((5:Fin 9).val+1=(8:Fin 9).val)) e).elim⟩
  · exact ⟨fun _=>by decide,fun _=>(outer01 i i0).symm⟩
  · exact ⟨fun e=>(leaves : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((6:Fin 9).val+1=(8:Fin 9).val)) e).elim⟩
  · exact ⟨fun _=>by decide,fun _=>outer01 j j0⟩

#print axioms high_near_three_port_on_first_two_arm_vertices
end Graffiti133P5CliqueArms
