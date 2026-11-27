import CubicAnchor33

namespace Graffiti384b.AnchorParity
open Finset SimpleGraph OneEar LowSample EarAnchor
open private CoreColor33.split CoreColor33.closeRoute from CoreColor33
open private OneEar.route_of_reach from OneEarFinish384b
variable {V : Type*} {G : SimpleGraph V} {e a b x y : V} {m n : ℕ}

/-- Concatenate vertex-disjoint simple paths across a single edge. -/
private def join (p : Route G e a x m) (q : Route G e y b n) (xy : G.Adj x y)
    (apart : ∀ i≤m,∀ j≤n,p.atIdx i≠q.atIdx j) : Route G e a b (m+1+n) where
  atIdx i := if i≤m then p.atIdx i else q.atIdx (i-(m+1))
  start := by simp [p.start]
  finish := by rw [if_neg (by omega : ¬m+1+n≤m),show m+1+n-(m+1)=n by omega,q.finish]
  step i h := by
    by_cases lt : i<m
    · rw [if_pos (by omega),if_pos (by omega)]; exact p.step i lt
    by_cases eq : i=m
    · subst i; rw [if_pos le_rfl,if_neg (by omega),Nat.sub_self,p.finish,q.start]; exact xy
    · rw [if_neg (by omega),if_neg (by omega),show i+1-(m+1)=(i-(m+1))+1 by omega]
      exact q.step _ (by omega)
  unique i hi j hj h := by
    by_cases il : i≤m <;> by_cases jl : j≤m
    · rw [if_pos il,if_pos jl] at h; exact p.unique _ il _ jl h
    · rw [if_pos il,if_neg jl] at h; exact (apart _ il _ (by omega) h).elim
    · rw [if_neg il,if_pos jl] at h; exact (apart _ jl _ (by omega) h.symm).elim
    · rw [if_neg il,if_neg jl] at h; have := q.unique _ (by omega) _ (by omega) h; omega
  avoid i hi := by
    by_cases low : i≤m
    · rw [if_pos low]; exact p.avoid i low
    · rw [if_neg low]; exact q.avoid _ (by omega)

private def initialPart (p : Route G e a b n) (i : ℕ) (hi : i≤n) : Route G e a (p.atIdx i) i where
  atIdx := p.atIdx
  start := p.start
  finish := rfl
  step j hj := p.step j (by omega)
  unique j hj k hk := p.unique j (by omega) k (by omega)
  avoid j hj := p.avoid j (by omega)

/-- A route meeting a clique in two vertices can be changed to either parity.
Only three clique vertices are needed. -/
theorem even_of_two_contacts [DecidableEq V] {C : Finset V} (cl : G.IsClique (C : Set V))
    (size : 3≤C.card) (miss : e∉C) (p : Route G e a b n) {r s : ℕ} (rs : r<s) (sn : s≤n)
    (rc : p.atIdx r∈C) (sc : p.atIdx s∈C) : ∃ k,k%2=0 ∧ Nonempty (Route G e a b k) := by
  classical
  let I := (range (n+1)).filter (fun i => p.atIdx i∈C)
  have rm : r∈I := mem_filter.mpr ⟨mem_range.mpr (by omega),rc⟩
  have sm : s∈I := mem_filter.mpr ⟨mem_range.mpr (by omega),sc⟩
  let non : I.Nonempty := ⟨r,rm⟩
  let i := I.min' non
  let j := I.max' non
  have im : i∈I := min'_mem .. 
  have jm : j∈I := max'_mem ..
  have ir : i≤r := min'_le _ _ rm
  have sj : s≤j := le_max' _ _ sm
  have ij : i<j := by omega
  have jn : j≤n := by have := mem_range.mp (mem_filter.mp jm).1; omega
  have ic := (mem_filter.mp im).2
  have jc := (mem_filter.mp jm).2
  have diff : p.atIdx i≠p.atIdx j := fun h => by have := p.unique i (by omega) j jn h; omega
  have pair : ({p.atIdx i,p.atIdx j} : Finset V).card=2 := card_pair diff
  obtain ⟨z,zc,zout⟩ := exists_mem_not_mem_of_card_lt_card (show ({p.atIdx i,p.atIdx j} : Finset V).card<C.card by omega)
  have zne : z≠p.atIdx i ∧ z≠p.atIdx j := by simpa [not_or] using zout
  have ze : z≠e := fun h => miss (h ▸ zc)
  let L := initialPart p i (by omega)
  let R := p.suffix j jn
  have lr (u : ℕ) (ui : u ≤ i) (v : ℕ) (vn : v≤n-j) : L.atIdx u≠R.atIdx v := by
    intro h; change p.atIdx u=p.atIdx (j+v) at h
    have := p.unique u (by omega) (j+v) (by omega) h; omega
  have left (u : ℕ) (ui : u ≤ i) : L.atIdx u≠z := by
    intro h; change p.atIdx u=z at h
    have um : u∈I := mem_filter.mpr ⟨mem_range.mpr (by omega),h ▸ zc⟩
    have lu : i≤u := min'_le _ _ um
    have eq : u=i := by omega
    exact zne.1 (eq ▸ h.symm)
  have right (v : ℕ) (vn : v≤n-j) : z≠R.atIdx v := by
    intro h; change z=p.atIdx (j+v) at h
    have vm : j+v∈I := mem_filter.mpr ⟨mem_range.mpr (by omega),h ▸ zc⟩
    have ub : j+v≤j := le_max' _ _ vm
    exact zne.2 ((show j+v=j by omega) ▸ h)
  let R' := R.prepend (cl zc jc zne.2) ze right
  have lr' (u : ℕ) (ui : u ≤ i) (v : ℕ) (vn : v≤n-j+1) : L.atIdx u≠R'.atIdx v := by
    cases v with
    | zero => exact left u ui
    | succ v => exact lr u ui v (by omega)
  by_cases even : (i+1+(n-j))%2=0
  · exact ⟨_,even,⟨join L R (cl ic jc diff) lr⟩⟩
  · exact ⟨i+1+(n-j+1),by omega,⟨join L R' (cl ic zc zne.1.symm) lr'⟩⟩

variable [Fintype V] [DecidableEq V] (G) [DecidableRel G.Adj]

/-- On the odd-order extremal side, the neighbors of the new triangular ear
are linked after opening the ear, but every simple path between them avoiding
the ear is odd. Such a path meets any clique of size at least three away from
the ear in at most one vertex. -/
theorem odd_routes (n29 : Fintype.card V=29) (g15 : gamma G=15)
    {e a b : V} (ear : G.neighborFinset e={a,b}) (ea : G.Adj e a)
    (eb : G.Adj e b) (ab : G.Adj a b) (minimum : ∀ v,v≠e → 3≤G.degree v) :
    (opened G {e,a,b}).Reachable a b ∧ (∃ n,2≤n ∧ Nonempty (Route G e a b n)) ∧
    (∀ n,Route G e a b n → n%2=1) ∧
    ∀ n (p : Route G e a b n) (C : Finset V),G.IsClique (C : Set V) → 3≤C.card → e∉C →
      ∀ i j,i≤n → j≤n → p.atIdx i∈C → p.atIdx j∈C → i=j := by
  classical
  have de : G.degree e=2 := by rw [← card_neighborFinset_eq_degree,ear,card_pair ab.ne]
  have min2 (v : V) : 2≤G.degree v := by by_cases eq : v=e; exact eq ▸ de.ge; have := minimum v eq; omega
  have only : twos G={e} := by
    ext v; simp only [twos,nonleaves,high,mem_sdiff,mem_filter,mem_univ,true_and,mem_singleton]
    constructor
    · rintro ⟨_,h⟩; apply Classical.byContradiction; intro ne; exact h (minimum v ne)
    · rintro rfl; omega
  have no : ¬CoreColor33.GoodCut G := by
    rintro ⟨A,left,right⟩
    have allm (v : V) : v∈nonleaves G := mem_filter.mpr ⟨mem_univ _,min2 v⟩
    have d1 : TwoDominates G A := fun v out => right v (allm v) (mem_compl.mpr out)
    have d2 : TwoDominates G Aᶜ := fun v out => left v (allm v) (by simpa using out)
    have l : gamma G≤A.card := Nat.sInf_le ⟨_,d1,rfl⟩
    have r : gamma G≤Aᶜ.card := Nat.sInf_le ⟨_,d2,rfl⟩
    rw [card_compl,n29] at r
    have bound := card_le_univ A; rw [n29] at bound
    omega
  have reach : (opened G {e,a,b}).Reachable a b := by
    apply Classical.byContradiction; intro notR; exact no (CoreColor33.split G only ear ab notR)
  have odd (l : ℕ) (p : Route G e a b l) : l%2=1 := by
    have notEven : ¬l%2=0 := fun h => no (CoreColor33.closeRoute p only ea eb ab.ne h)
    omega
  refine ⟨reach,OneEar.route_of_reach G ear eb ab reach,odd,?_⟩
  intro n p C cl large away i j hi hj ci cj
  have neq (i j : ℕ) (lt : i<j) (hj : j≤n) (ci : p.atIdx i∈C) (cj : p.atIdx j∈C) : False := by
    obtain ⟨k,ev,⟨q⟩⟩ := even_of_two_contacts cl large away p lt hj ci cj
    have := odd k q; omega
  exact le_antisymm (le_of_not_gt (fun gt => neq j i gt hi cj ci)) (le_of_not_gt (fun gt => neq i j gt hj ci cj))

end Graffiti384b.AnchorParity
#print axioms Graffiti384b.AnchorParity.even_of_two_contacts
#print axioms Graffiti384b.AnchorParity.odd_routes
