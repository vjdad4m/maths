import FourRingCyclicEquivalence
import FourRingCycleArc

open SimpleGraph KelmansCactus.NearPerfectReplica.Layout
namespace KelmansCactus.FourRingReplica.Layout
open FourRingPropagation FourRingCycleArc
noncomputable section
variable {U J : Type*} {A : SimpleGraph U} {r : Bool→U}
variable (L : Layout A r) (next : Equiv.Perm J)
variable {fixed : ∀i,next i≠i}

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

private theorem unique_external {x y z : Host J r} (xy : (L.graph next fixed).Adj x y)
    (xz : (L.graph next fixed).Adj x z) (diffy : x.1≠y.1) (diffz : x.1≠z.1) : y=z := by
  obtain ⟨s,sx,sy⟩ := (L.graph_cross next diffy).mp xy
  obtain ⟨t,tx,tz⟩ := (L.graph_cross next diffz).mp xz
  have e : s=t := L.port_inj_on_host (sx.trans tx.symm)
  subst t
  exact sy.symm.trans tz

/-- The index of a cross-edge target specifies which cap root
is adjacent to the projected source port. -/
private theorem exit_root {x y : Host J r} (xy : (L.graph next fixed).Adj x y)
    (different : x.1≠y.1) :
    ∃ b, A.Adj (r b) x.2.val ∧ y.1=(if b then next x.1 else next.symm x.1) := by
  obtain ⟨⟨i,b,c⟩,px,qy⟩ := (L.graph_cross next different).mp xy
  have pos : i=x.1 := congrArg Prod.fst px
  have val : (L.port (b,c)).val=x.2.val := congrArg (fun t : Host J r=>t.2.val) px
  refine ⟨b,val ▸ L.conn (b,c),?_⟩
  have qq : (L.q next i (b,c)).1=y.1 := congrArg Prod.fst qy
  rw [←pos,←qq]
  cases b <;> rfl

private theorem same_half {i j : J} (dir : next i≠next.symm i)
    {b c : Bool} (l : j=(if b then next i else next.symm i))
    (q : j=(if c then next i else next.symm i)) : b=c := by
  cases b <;> cases c
  · rfl
  · exact (dir (q.symm.trans l)).elim
  · exact (dir (l.symm.trans q)).elim
  · rfl

/-- A cycle crossing the host's paired seams descends to a cap
cycle no longer than itself. The first internal run uses a
single cap root if it exits to the same index it entered from. -/
theorem crossing_cycle_descends (dir : ∀i,next i≠next.symm i)
    {n : ℕ} [NeZero n] (nn : 3≤n)
    {f : Fin n→Host J r} (cy : CycleList (L.graph next fixed) n f)
    (cross : (f 0).1≠(f 1).1) :
    ∃ k : ℕ, ∃ inst : NeZero k,3≤k ∧ k≤n ∧ @HasShortCycle U A k inst := by
  classical
  let F : ℕ→Host J r := atNat f
  let P : ℕ→Prop := fun j=>2≤j ∧ (F j).1≠(F 1).1
  have atEnd : P n := by
    refine ⟨by omega,?_⟩
    change (atNat f n).1≠(f 1).1
    rw [atNat_end]
    exact cross
  have yes : ∃ j,P j := ⟨n,atEnd⟩
  let k := Nat.find yes
  have spec : 2≤k ∧ (F k).1≠(F 1).1 := Nat.find_spec yes
  have kn : k≤n := Nat.find_min' yes atEnd
  have central {j : ℕ} (j1 : 1≤j) (jk : j<k) : (F j).1=(F 1).1 := by
    by_cases jEq : j=1
    · rw [jEq]
    · exact Classical.not_not.mp (fun no=>Nat.find_min yes jk ⟨by omega,no⟩)
  have step (j : ℕ) : (L.graph next fixed).Adj (F j) (F (j+1)) := adjNat cy j
  have last : (F (k-1)).1=(F 1).1 := central (by omega) (by omega)
  have exit : (L.graph next fixed).Adj (F (k-1)) (F k) := by
    have e : k-1+1=k := by omega
    simpa only [e] using step (k-1)
  have sep : (F (k-1)).1≠(F k).1 := fun h=>spec.2 (h.symm.trans last)
  have first : (F 1).1≠(F 0).1 := cross.symm
  have kk : 3≤k := by
    by_contra low
    have e : k=2 := by omega
    have ex : (L.graph next fixed).Adj (F 1) (F 2) := step 1
    have ne : (F 1).1≠(F 2).1 := by simpa only [e,Nat.reduceSub] using sep
    have eq := L.unique_external next (step 0).symm ex first ne
    have bad : (0:ℕ)=2 := atNat_injective cy.1 (by omega) (by omega) eq
    omega
  obtain ⟨b,bEdge,bDir⟩ := L.exit_root next (step 0).symm first
  obtain ⟨c,cEdge,cDir⟩ := L.exit_root next exit sep
  have bc : k=n→b=c := by
    intro eq
    have same : F k=F 0 := by
      change atNat f k=f 0
      rw [eq,atNat_end]
    rw [last,same] at cDir
    exact same_half next (dir (F 1).1) bDir cDir
  let g : ℕ→U := fun j=>(F j).2.val
  have disj (j : ℕ) (_j1 : 1≤j) (_jk : j<k) (q : Bool) : g j≠r q := by
    cases q
    · exact (F j).2.property.1
    · exact (F j).2.property.2
  have inj (j t : ℕ) (j1 : 1≤j) (jk : j<k) (t1 : 1≤t) (tk : t<k) (e : g j=g t) : j=t := by
    have whole : F j=F t := Prod.ext ((central j1 jk).trans (central t1 tk).symm) (Subtype.ext e)
    exact atNat_injective cy.1 (jk.trans_le kn) (tk.trans_le kn) whole
  have adj (j : ℕ) (j1 : 1≤j) (jk : j+1<k) : A.Adj (g j) (g (j+1)) :=
    (L.internal next ((central j1 (by omega)).trans (central (by omega) jk).symm)).mp (step j)
  obtain ⟨t,t3,tC⟩ := close_arc L.rootEdge kk g b c disj inj adj bEdge cEdge.symm
  refine ⟨_,t,t3,?_,tC⟩
  by_cases h : b=c
  · simpa [h] using kn
  · have ne : k≠n := fun e=>h (bc e)
    rw [if_neg h]
    omega

private theorem all_cells {n : ℕ} [NeZero n] {f : Fin n→Host J r}
    (same : ∀i,(f i).1=(f (i+1)).1) (i : Fin n) : (f i).1=(f 0).1 := by
  obtain ⟨k,hk⟩ := i
  induction k with
  | zero => rfl
  | succ k ih =>
    have shorter : k<n := by omega
    have h := same ⟨k,shorter⟩
    have t : ((⟨k,shorter⟩ : Fin n)+1)=⟨k+1,hk⟩ := by
      apply Fin.ext
      rw [Fin.add_def]
      have p : (1 : Fin n).val=1 := Nat.mod_eq_of_lt (show 1<n by omega)
      simp only [p,Nat.mod_eq_of_lt hk]
    rw [t] at h
    exact h.symm.trans (ih shorter)

/-- Every paired-ring cycle projects or closes up to a cap
cycle no longer than itself, when previous and next are distinct. -/
theorem cycle_descends (dir : ∀i,next i≠next.symm i)
    {n : ℕ} [NeZero n] (nn : 3≤n)
    (cy : HasShortCycle (L.graph next fixed) n) :
    ∃ k : ℕ, ∃ inst : NeZero k,3≤k ∧ k≤n ∧ @HasShortCycle U A k inst := by
  obtain ⟨f,hf⟩ := cy
  by_cases stay : ∀i,(f i).1=(f (i+1)).1
  · have t := all_cells stay
    refine ⟨n,inferInstance,nn,le_rfl,fun j=>(f j).2.val,⟨?_,?_⟩⟩
    · intro i j e
      exact hf.1 (Prod.ext ((t i).trans (t j).symm) (Subtype.ext e))
    · intro i
      exact (L.internal next (stay i)).mp (hf.2 i)
  · push_neg at stay
    obtain ⟨i,diff⟩ := stay
    have tr := cycle_shift hf i
    have dif : ((fun j=>f (j+i)) 0).1≠((fun j=>f (j+i)) 1).1 := by
      simpa only [zero_add,add_comm (1:Fin n) i] using diff
    exact L.crossing_cycle_descends next dir nn tr dif

theorem preserves_girth_bound (dir : ∀i,next i≠next.symm i)
    (g : ℕ) (clean : NoCyclesBelow A g) : NoCyclesBelow (L.graph next fixed) g := by
  intro n nn ng t cyc
  letI : NeZero n := t
  obtain ⟨k,i,k3,kn,h⟩ := L.cycle_descends next dir nn cyc
  exact clean k k3 (kn.trans_lt ng) i h

theorem spin_distinct_directions {n : ℕ} [NeZero n] (n3 : 3≤n) (i : Fin n) :
    spin n i≠(spin n).symm i := by
  intro eq
  have adj : i+1=i-1 := eq
  have s := congrArg (fun j : Fin n=> j+1) adj
  change i+1+1=i-1+1 at s
  rw [sub_add_cancel] at s
  have eq0 : (2:Fin n)=0 := by
    have z : i+2=i+0 := by simpa [add_assoc,one_add_one_eq_two] using s
    exact add_left_cancel z
  have val := congrArg Fin.val eq0
  change 2%n=0 at val
  rw [Nat.mod_eq_of_lt (show 2<n by omega)] at val
  contradiction

#print axioms crossing_cycle_descends
#print axioms preserves_girth_bound
#print axioms spin_distinct_directions
end
end KelmansCactus.FourRingReplica.Layout
