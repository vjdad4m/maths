import ReplicaShortCycles

open SimpleGraph
namespace KelmansCactus.NearPerfectReplica.Layout
noncomputable section
variable {U J : Type*} {A : SimpleGraph U} {B : SimpleGraph J} {r : U}
variable (L : Layout A B r)

private def atNat {V : Type*} {n : ℕ} [NeZero n] (f : Fin n→V) (j : ℕ) : V := f j

private theorem stepCast (n j : ℕ) [NeZero n] :
    ((j+1 : ℕ) : Fin n) = (j : Fin n)+1 := by
  apply Fin.ext
  change (j+1)%n=(j%n+1%n)%n
  exact Nat.add_mod j 1 n

private theorem adjNat {V : Type*} {G : SimpleGraph V} {n : ℕ} [NeZero n]
    {f : Fin n→V} (h : CycleList G n f) (j : ℕ) : G.Adj (atNat f j) (atNat f (j+1)) := by
  change G.Adj (f j) (f (↑(j+1)))
  rw [stepCast]
  exact h.2 _

private theorem atNat_end {V : Type*} {n : ℕ} [NeZero n] (f : Fin n→V) :
    atNat f n=f 0 := by
  unfold atNat
  congr 1
  apply Fin.ext
  exact Nat.mod_self n

private theorem atNat_injective {V : Type*} {n : ℕ} [NeZero n] {f : Fin n→V}
    (hi : Function.Injective f) {j k : ℕ} (jn : j<n) (kn : k<n)
    (same : atNat f j=atNat f k) : j=k := by
  have q := congrArg Fin.val (hi same)
  change j%n=k%n at q
  rwa [Nat.mod_eq_of_lt jn,Nat.mod_eq_of_lt kn] at q

private theorem root_at_exit {x y : Host J r} (adj : L.graph.Adj x y) (dif : x.1≠y.1) :
    A.Adj r x.2.val := by
  obtain ⟨s,e,_⟩ := (L.external_adj dif).mp adj
  have q : (L.port s.2).val=x.2.val := congrArg (fun z : Host J r=>z.2.val) e
  exact q ▸ L.edge_of_port s.2

/-- A cycle crossing a seam has a strictly shorter rooted cycle in
the original brick. Use the arc from the entry port to the first exit:
adding the removed root closes this arc, while a simple base cannot
return directly via a different seam between the same two cells. -/
theorem first_cross_gives_shorter_root_cycle {n : ℕ} [NeZero n] (nn : 3≤n)
    {f : Fin n→Host J r} (cy : CycleList L.graph n f) (cross : (f 0).1≠(f 1).1) :
    ∃ k : ℕ, ∃ t : NeZero k, 3≤k ∧ k<n ∧
      ∃ g : Fin k→U, @CycleList U A k t g ∧ g 0=r := by
  classical
  let F : ℕ→Host J r := atNat f
  let P : ℕ→Prop := fun j=>2≤j ∧ (F j).1≠(F 1).1
  have yes : ∃ j,P j := ⟨n,by
    refine ⟨by omega,?_⟩
    change (atNat f n).1≠(f 1).1
    rw [atNat_end]
    exact cross⟩
  let k := Nat.find yes
  have spec : 2≤k ∧ (F k).1≠(F 1).1 := Nat.find_spec yes
  have kn : k≤n := Nat.find_min' yes (by
    refine ⟨by omega,?_⟩
    change (atNat f n).1≠(f 1).1
    rw [atNat_end]
    exact cross)
  have central {j : ℕ} (j1 : 1≤j) (jk : j<k) : (F j).1=(F 1).1 := by
    by_cases jEq : j=1
    · rw [jEq]
    · exact Classical.not_not.mp (fun no=>Nat.find_min yes jk ⟨by omega,no⟩)
  have step (j : ℕ) : L.graph.Adj (F j) (F (j+1)) := adjNat cy j
  have last : (F (k-1)).1=(F 1).1 := central (by omega) (by omega)
  have exit : L.graph.Adj (F (k-1)) (F k) := by
    have e : k-1+1=k := by omega
    simpa only [e] using step (k-1)
  have sep : (F (k-1)).1≠(F k).1 := fun h=>spec.2 (h.symm.trans last)
  have kk : 3≤k := by
    by_contra low
    have e : k=2 := by omega
    have ex : L.graph.Adj (F 1) (F 2) := step 1
    have ne : (F 1).1≠(F 2).1 := by simpa only [e,Nat.reduceSub] using sep
    have eq := L.unique_external_of_vertex (step 0).symm ex (Ne.symm cross) ne
    have bad : (0:ℕ)=2 := atNat_injective cy.1 (by omega) (by omega) eq
    omega
  have strict : k<n := by
    by_contra! back
    have e : k=n := by omega
    have same : (F 0).1=(F k).1 := by
      change (f 0).1=(atNat f k).1
      rw [e,atNat_end]
    have neq : (F 0).1≠(F 1).1 := cross
    have eq := (L.unique_external_of_cells (step 0) exit.symm neq same last.symm).2
    have bad : (1:ℕ)=k-1 := atNat_injective cy.1 (by omega) (by omega) eq
    omega
  letI : NeZero k := ⟨by omega⟩
  let g : Fin k→U := fun j=>if j.val=0 then r else (F j.val).2.val
  have g0 : g 0=r := by simp [g]
  have one_lt : (1:ℕ)<k := by omega
  have one : (1:Fin k).val=1 := Nat.mod_eq_of_lt one_lt
  refine ⟨k,inferInstance,kk,strict,g,⟨?_,?_⟩,g0⟩
  · intro j j' eq
    by_cases j0 : j.val=0
    · by_cases j'0 : j'.val=0
      · exact Fin.ext (j0.trans j'0.symm)
      · have e : r=(F j'.val).2.val := by simpa only [g,if_pos j0,if_neg j'0] using eq
        exact ((F j'.val).2.property e.symm).elim
    · by_cases j'0 : j'.val=0
      · have e : (F j.val).2.val=r := by simpa only [g,if_neg j0,if_pos j'0] using eq
        exact ((F j.val).2.property e).elim
      · have e : (F j.val).2.val=(F j'.val).2.val := by
          simpa only [g,if_neg j0,if_neg j'0] using eq
        have eqF : F j.val=F j'.val := Prod.ext
          ((central (by omega) j.isLt).trans (central (by omega) j'.isLt).symm)
          (Subtype.ext e)
        exact Fin.ext (atNat_injective cy.1 (j.isLt.trans strict) (j'.isLt.trans strict) eqF)
  · intro j
    have jLt := j.isLt
    by_cases j0 : j.val=0
    · have jEq : j=0 := Fin.ext j0
      rw [jEq,zero_add,g0]
      have gg : g 1 = (F 1).2.val := by
        simp only [g,one,if_neg (show (1:ℕ)≠0 from by decide)]
      rw [gg]
      exact L.root_at_exit (step 0).symm (Ne.symm cross)
    by_cases jLast : j.val+1=k
    · have nov : (j+1).val=0 := by
        rw [Fin.val_add,one,jLast,Nat.mod_self]
      have je : j.val=k-1 := by omega
      simp only [g,nov,if_pos rfl,if_neg j0,je]
      exact (L.root_at_exit exit sep).symm
    · have inc : j.val+1<k := by omega
      have nov : (j+1).val=j.val+1 := by
        rw [Fin.val_add,one,Nat.mod_eq_of_lt inc]
      have nzero : j.val+1≠0 := by omega
      simp only [g,nov,if_neg j0,if_neg nzero]
      exact (L.internal_adj
        ((central (by omega) jLt).trans (central (by omega) inc).symm)).mp (step j.val)

/-- No cyclically enumerated simple cycle shorter than g. Unlike
natural-valued Mathlib girth, this convention includes forests. -/
def NoCyclesBelow {V : Type*} (G : SimpleGraph V) (g : ℕ) : Prop :=
  ∀ (n : ℕ), 3≤n → n<g → ∀ t : NeZero n, ¬@HasShortCycle V G n t

/-- Any replica cycle either stays in a cell (and so descends unchanged)
or gives a strictly shorter cycle through the root of the same brick. -/
theorem cycle_descends_or_shortens {n : ℕ} [NeZero n] (nn : 3≤n)
    (cy : HasShortCycle L.graph n) :
    HasShortCycle (rootDeleted (A:=A) (r:=r)) n ∨
      ∃ k : ℕ, ∃ t : NeZero k, 3≤k ∧ k<n ∧
        ∃ h : Fin k→U, @CycleList U A k t h ∧ h 0=r := by
  classical
  obtain ⟨f,hf⟩ := cy
  by_cases stay : ∀ i,(f i).1=(f (i+1)).1
  · left
    have t := identity_cells stay
    refine ⟨fun j=>(f j).2,⟨?_,?_⟩⟩
    · intro i j e
      exact hf.1 (Prod.ext ((t i).trans (t j).symm) e)
    · intro i
      exact (L.internal_adj (stay i)).mp (hf.2 i)
  · push_neg at stay
    obtain ⟨i,diff⟩ := stay
    right
    have c := cycle_shift hf i
    have dif : ((fun j=>f (j+i)) 0).1≠((fun j=>f (j+i)) 1).1 := by
      simpa only [zero_add,add_comm (1:Fin n) i] using diff
    exact L.first_cross_gives_shorter_root_cycle nn c dif

/-- Rooted replication preserves an arbitrary girth lower bound.
It can also raise that bound by one when deleting the root
destroys every cycle of the previous minimum length. No girth
condition is needed on the simple base. -/
theorem no_cycles_of_root_and_cell (g : ℕ)
    (near : NoCyclesBelow A (g-1))
    (inside : NoCyclesBelow (rootDeleted (A:=A) (r:=r)) g) :
    NoCyclesBelow L.graph g := by
  intro n nn ng t cy
  letI : NeZero n := t
  rcases L.cycle_descends_or_shortens nn cy with cell | ⟨k,kInst,kk,kn,h,hc,_⟩
  · exact inside n nn ng t cell
  · exact near k kk (by omega) kInst ⟨h,hc⟩

theorem root_deletion_preserves_lower_bound (g : ℕ) (clean : NoCyclesBelow A g) :
    NoCyclesBelow (rootDeleted (A:=A) (r:=r)) g := by
  intro n nn ng t h
  letI : NeZero n := t
  obtain ⟨f,cy⟩ := h
  exact clean n nn ng t ⟨fun i=>(f i).val,
    ⟨fun _ _ e=>cy.1 (Subtype.ext e),fun j=>cy.2 j⟩⟩

theorem girth_lower_bound (g : ℕ) (clean : NoCyclesBelow A g) :
    NoCyclesBelow L.graph g :=
  L.no_cycles_of_root_and_cell g (fun n nn ng t=>clean n nn (by omega) t)
    (root_deletion_preserves_lower_bound g clean)

#print axioms first_cross_gives_shorter_root_cycle
#print axioms cycle_descends_or_shortens
#print axioms no_cycles_of_root_and_cell
#print axioms girth_lower_bound
end
end KelmansCactus.NearPerfectReplica.Layout
