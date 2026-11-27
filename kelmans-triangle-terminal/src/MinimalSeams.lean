import Substitute

open Finset
namespace KelmansCactus.MinimalSeams
open ThreePort Substitute

/-- A cyclic 3-edge seam has two odd sides, each with at least three vertices.
Capping a side introduces one vertex. The cap types are 0+2 or 4+4 mod 6,
and both caps are strictly smaller than the whole graph. -/
theorem cap_orders {a b N : ℕ}
    (ha : a % 2 = 1) (hb : b % 2 = 1) (amin : 3 ≤ a) (bmin : 3 ≤ b)
    (hN : a+b=N) (div : N % 6 = 0) :
    a+1<N ∧ b+1<N ∧
      (((a+1)%6=0 ∧ (b+1)%6=2) ∨
       ((a+1)%6=2 ∧ (b+1)%6=0) ∨
       ((a+1)%6=4 ∧ (b+1)%6=4)) := by omega

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable {X : Type*} [Fintype X] [DecidableEq X] {H : SimpleGraph X}

/-- Cutting a cap root out of one of its tiles yields precisely a width-two
single port (root was a leaf), or two width-one ports (root was the center). -/
def RecoverableWidth (w : Fin 3 → Nat) : Prop :=
  (∃ i, w=(fun j => if j=i then 2 else 0)) ∨
  (∃ i j, i≠j ∧ w=(fun k => if k=i ∨ k=j then 1 else 0))

omit [Fintype V] in
theorem mimic_complements_recoverable {B : Finset V} {q : Fin 3 → V}
    {w : Fin 3 → Nat} (hw : RecoverableWidth w) (m : Mimic G B q) :
    ∃ z, Signature (G:=G) B q z ∧ ∀ i, Opposite (w i) (z i) := by
  rcases hw with ⟨i,rfl⟩ | ⟨i,j,ne,rfl⟩
  · refine ⟨_,m.leaf i,?_⟩
    intro j
    by_cases hj : j=i <;> simp [hj,Opposite]
  · refine ⟨_,m.center i j ne,?_⟩
    intro k
    by_cases h : k=i ∨ k=j <;> simp [h,Opposite]

omit [Fintype V] in
private theorem leaf_width {A : Finset V} {p : Fin 3 → V} {i : Fin 3} {v : V}
    (hp : p i ∈ A) (hv : v ∈ A) (e : G.Adj (p i) v)
    (cl : Closed G (A \ {p i,v})) :
    Signature (G:=G) A p (fun j => if j=i then 2 else 0) := by
  let F (j : Fin 3) : Finset V := if j=i then {p i,v} else ∅
  obtain ⟨P,hP⟩ := cl
  have uni : univ.biUnion F = {p i,v} := by
    ext z
    simp only [mem_biUnion,mem_univ,true_and]
    constructor
    · rintro ⟨j,hj⟩
      by_cases h : j=i
      · subst j; simpa [F] using hj
      · simp [F,h] at hj
    · intro hz
      exact ⟨i,by simpa [F] using hz⟩
  refine ⟨F,?_,?_,P,?_⟩
  · intro j
    by_cases h : j=i
    · subst j
      have hcard : (F i).card = 2 := by simp [F,e.ne]
      refine ⟨by simpa using hcard,?_⟩
      change AtPort (G:=G) A (p i) (F i)
      rw [show F i = {p i,v} by simp [F]]
      refine ⟨insert_subset_iff.mpr ⟨hp,singleton_subset_iff.mpr hv⟩,by simp,?_⟩
      intro u hu ne
      rcases mem_insert.mp hu with hu | hu
      · exact (ne hu).elim
      · obtain rfl := mem_singleton.mp hu
        exact e
    · simp only [h,F,if_false,card_empty]
      exact ⟨trivial,⟨empty_subset _,by simp,by simp⟩⟩
  · intro j k ne
    by_cases hj : j=i
    · have hn : k ≠ i := fun hh => ne (hj.trans hh.symm)
      simp [F,hn]
    · simp [F,hj]
  · rw [uni]
    exact hP

omit [Fintype V] in
private theorem center_width {A : Finset V} {p : Fin 3 → V} {i j : Fin 3}
    (pn : p i ≠ p j) (hp : p i ∈ A) (hq : p j ∈ A)
    (cl : Closed G (A \ {p i,p j})) :
    Signature (G:=G) A p (fun k => if k=i ∨ k=j then 1 else 0) := by
  let F (k : Fin 3) : Finset V := if k=i ∨ k=j then {p k} else ∅
  obtain ⟨P,hP⟩ := cl
  have uni : univ.biUnion F = {p i,p j} := by
    ext z
    simp only [mem_biUnion,mem_univ,true_and,mem_insert,mem_singleton]
    constructor
    · rintro ⟨k,hk⟩
      by_cases hki : k=i
      · subst k
        exact Or.inl (by simpa [F] using hk)
      by_cases hkj : k=j
      · subst k
        exact Or.inr (by simpa [F] using hk)
      · simp [F,hki,hkj] at hk
    · rintro (rfl | rfl)
      · exact ⟨i,by simp [F]⟩
      · exact ⟨j,by simp [F]⟩
  refine ⟨F,?_,?_,P,?_⟩
  · intro k
    by_cases hk : k=i ∨ k=j
    · have hw : p k ∈ A := hk.elim (fun h => h.symm ▸ hp) (fun h => h.symm ▸ hq)
      simp only [hk,F,if_true,card_singleton]
      exact ⟨trivial,⟨singleton_subset_iff.mpr hw,by simp,fun v hv ne => (ne (mem_singleton.mp hv)).elim⟩⟩
    · simp only [F,hk,if_false,card_empty]
      exact ⟨trivial,⟨empty_subset _,by simp,by simp⟩⟩
  · intro k l kn
    by_cases hk : k=i ∨ k=j
    · by_cases hl : l=i ∨ l=j
      · obtain hi|hi := hk <;> obtain hj|hj := hl <;> subst k <;> subst l
        · exact (kn rfl).elim
        · simp [F,pn.symm]
        · simp [F,pn]
        · exact (kn rfl).elim
      · simp [F,hl]
    · simp [F,hk]
  · rw [uni]
    exact hP

omit [Fintype V] in
theorem cap_supplies_recoverable {K : SimpleGraph V} {A : Finset V} {r : V} {p : Fin 3 → V}
    (hcap : Closed K (insert r A)) (notin : r ∉ A)
    (nbr : ∀ x ∈ A, K.Adj r x → ∃ i, p i=x)
    (keep : ∀ x ∈ A, ∀ y ∈ A, K.Adj x y → G.Adj x y) :
    ∃ w, Signature (G:=G) A p w ∧ RecoverableWidth w := by
  obtain ⟨P,hP⟩ := hcap
  have root_mem : r ∈ P.biUnion id := hP.cover.symm ▸ mem_insert_self _ _
  obtain ⟨t,ht,rt⟩ := mem_biUnion.mp root_mem
  change r ∈ t at rt
  have tsub := hP.tile_sub K ht
  have s : (insert r A) \ t ⊆ A := by
    intro v hv
    obtain ⟨vv,vt⟩ := mem_sdiff.mp hv
    rcases mem_insert.mp vv with rfl | va
    · exact (vt rt).elim
    · exact va
  have fact := change_edges (G:=G) (remove_tile hP ht)
    (fun x hx y hy => keep x (s hx) y (s hy))
  have cl : Closed G ((insert r A) \ t) := ⟨_,fact⟩
  obtain ⟨a,b,c,ab,ac,bc,e1,e2,eq⟩ := (Kelmans.tile_iff_path K t (hP.tile t ht).1).mp (hP.tile t ht).2
  have atA : a ∈ insert r A := tsub (by simp [eq])
  have btA : b ∈ insert r A := tsub (by simp [eq])
  have ctA : c ∈ insert r A := tsub (by simp [eq])
  have cldrop {x y : V} (d : t = {r,x,y}) : Closed G (A \ {x,y}) := by
    have er : (insert r A) \ t = A \ {x,y} := by
      ext v
      simp only [d,mem_sdiff,mem_insert,mem_singleton,not_or]
      by_cases e : v=r
      · subst v
        simp [notin]
      · simp [e]
    simpa only [er] using cl
  rw [eq] at rt
  simp only [mem_insert,mem_singleton] at rt
  rcases rt with h | h | h
  · subst r
    have bA := (mem_insert.mp btA).resolve_left ab.symm
    have cA := (mem_insert.mp ctA).resolve_left ac.symm
    obtain ⟨i,ei⟩ := nbr b bA e1
    subst b
    exact ⟨_,leaf_width (i:=i) bA cA (keep _ bA _ cA e2) (cldrop eq),Or.inl ⟨i,rfl⟩⟩
  · subst r
    have aA := (mem_insert.mp atA).resolve_left ab
    have cA := (mem_insert.mp ctA).resolve_left bc.symm
    obtain ⟨i,ei⟩ := nbr a aA e1.symm
    obtain ⟨j,ej⟩ := nbr c cA e2
    subst a; subst c
    have ne : i≠j := fun h => ac (congrArg p h)
    have q := cldrop (x:=p i) (y:=p j) (by rw [eq,insert_comm])
    exact ⟨_,center_width ac aA cA q,Or.inr ⟨i,j,ne,rfl⟩⟩
  · subst r
    have aA := (mem_insert.mp atA).resolve_left ac
    have bA := (mem_insert.mp btA).resolve_left bc
    obtain ⟨i,ei⟩ := nbr b bA e2.symm
    subst b
    have q := cldrop (x:=p i) (y:=a) (by rw [eq]; ext v; simp; tauto)
    exact ⟨_,leaf_width (i:=i) bA aA (keep _ bA _ aA e1.symm) q,Or.inl ⟨i,rfl⟩⟩

#print axioms cap_supplies_recoverable

/-- Conditional 0/2 cut elimination: a factored zero-cap contributes a
recoverable width; the six good states on the order-two cap's brick
are enough, not all nine arithmetic width states. -/
theorem close_0_2 {A : Finset V} {p q : Fin 3 → V}
    (seam : Seam (G:=G) A p q)
    (recover : ∃ w, Signature (G:=G) A p w ∧ RecoverableWidth w)
    (good : Mimic G Aᶜ q) :
    KelmansStarter.HasP3Factor G := by
  obtain ⟨w,hw,hr⟩ := recover
  obtain ⟨z,hz,ok⟩ := mimic_complements_recoverable hr good
  exact (factor_iff_signatures seam).mpr ⟨w,z,hw,hz,ok⟩

omit [Fintype V] in
theorem zero_width {A : Finset V} {p : Fin 3 → V}
    (h : Closed G A) :
    Signature (G:=G) A p (fun _ => 0) := by
  obtain ⟨P,hP⟩ := h
  refine ⟨fun _ => ∅,fun _ => ⟨rfl,⟨empty_subset _,by simp,by simp⟩⟩,by simp,P,?_⟩
  have zero : (univ : Finset (Fin 3)).biUnion (fun _ => (∅ : Finset V)) = ∅ := by
    ext v
    simp
  rw [zero,sdiff_empty]
  exact hP

/-- Conditional 4/4 cut elimination. Both uncapped sides must tile without
the root; existence of an arbitrary factor on each cap is not a premise. -/
theorem close_4_4 {A : Finset V} {p q : Fin 3 → V}
    (seam : Seam (G:=G) A p q)
    (hA : Closed G A) (hB : Closed G Aᶜ) :
    KelmansStarter.HasP3Factor G :=
  (factor_iff_signatures seam).mpr ⟨_,_,zero_width hA,zero_width hB,fun _ => Or.inl ⟨rfl,rfl⟩⟩

/-- Exact monotonic transfer for a smaller tester, with arbitrary vertex
types on the two graphs. The original sides need only realize every
signature the corresponding sides of the tester can use. In an
order-minimal counterexample, a legal smaller tester is impossible. -/
theorem dominate_smaller_test {A : Finset V} {B : Finset X} {p q : Fin 3 → V}
    {r s : Fin 3 → X}
    (orig : Seam (G:=G) A p q) (tester : Seam (G:=H) B r s)
    (side₁ : ∀ w, (∀ i, w i ≤ 2) → Signature (G:=H) B r w → Signature (G:=G) A p w)
    (side₂ : ∀ w, (∀ i, w i ≤ 2) → Signature (G:=H) Bᶜ s w → Signature (G:=G) Aᶜ q w)
    (hTest : KelmansStarter.HasP3Factor H) :
    KelmansStarter.HasP3Factor G := by
  obtain ⟨u,v,hu,hv,ok⟩ := (factor_iff_signatures tester).mp hTest
  have su : ∀ i, u i ≤ 2 := by
    intro i
    have h := ok i
    unfold Opposite at h
    omega
  have sv : ∀ i, v i ≤ 2 := by
    intro i
    have h := ok i
    unfold Opposite at h
    omega
  exact (factor_iff_signatures orig).mpr ⟨u,v,side₁ u su hu,side₂ v sv hv,ok⟩

/-- A checkable obstruction-budget consequence of the three-replica
root-deletion gadget. If both 4-mod-6 caps fail root deletion, the
ordinary minimal order lower-bounds both triple blowups, not the bare
cap orders. The gadget-to-counterexample implication is a premise here. -/
theorem balanced_both_fail {m n N : ℕ} (sum : m+n=N+2)
    (left : N ≤ 3*m) (right : N ≤ 3*n) :
    N ≤ 3*m ∧ 3*m ≤ 2*N+6 ∧ N ≤ 3*n ∧ 3*n ≤ 2*N+6 := by omega

#print axioms cap_orders
#print axioms close_0_2
#print axioms close_4_4
#print axioms dominate_smaller_test
#print axioms balanced_both_fail
end KelmansCactus.MinimalSeams
