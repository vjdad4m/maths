import ReplicaGirth

open SimpleGraph KelmansCactus.NearPerfectReplica.Layout
namespace KelmansCactus.FourRingCycleArc

private theorem cap_root_inj {U : Type*} {A : SimpleGraph U} {r : Bool→U}
    (edge : A.Adj (r false) (r true)) : Function.Injective r := by
  intro b c eq
  cases b <;> cases c
  · rfl
  · exact (edge.ne eq).elim
  · exact (edge.ne eq.symm).elim
  · rfl

/-- Close the injectively enumerated internal arc x₁,…,xₖ₋₁
with one or two adjacent cap roots. The new length is k or k+1. -/
theorem close_arc {U : Type*} {A : SimpleGraph U} {r : Bool→U}
    (edge : A.Adj (r false) (r true)) {k : ℕ} (k3 : 3≤k)
    (f : ℕ→U) (b c : Bool)
    (disj : ∀ j,1≤j→j<k→∀ a,f j≠r a)
    (inj : ∀ j t,1≤j→j<k→1≤t→t<k→f j=f t→j=t)
    (step : ∀ j,1≤j→j+1<k→A.Adj (f j) (f (j+1)))
    (entr : A.Adj (r b) (f 1)) (exit : A.Adj (f (k-1)) (r c)) :
    let n := if b=c then k else k+1
    ∃ hn : NeZero n, 3≤n ∧ @HasShortCycle U A n hn := by
  let n := if b=c then k else k+1
  have nk : k≤n := by dsimp [n]; split <;> omega
  have up : n≤k+1 := by dsimp [n]; split <;> omega
  letI hn : NeZero n := ⟨by omega⟩
  let g : Fin n→U := fun j=>if j.val=0 then r b else if j.val=k then r c else f j.val
  have z : g 0=r b := by simp [g]
  have oneLt : (1:ℕ)<n := by omega
  have on : (1:Fin n).val=1 := Nat.mod_eq_of_lt oneLt
  have o : g 1=f 1 := by
    simp only [g,on,if_neg (show (1:ℕ)≠0 by omega),if_neg (show (1:ℕ)≠k by omega)]
  have different : k<n→b≠c := by
    intro ne eq
    have heq : n=k := if_pos eq
    omega
  have central {j : Fin n} (j0 : j.val≠0) (jK : j.val≠k) : j.val<k := by
    have := j.isLt
    omega
  refine ⟨hn,by omega, g,⟨?_,?_⟩⟩
  · intro j t eq
    by_cases j0 : j.val=0
    · by_cases t0 : t.val=0
      · exact Fin.ext (j0.trans t0.symm)
      · by_cases tK : t.val=k
        · have bk : b=c := cap_root_inj edge
            (by simpa only [g,j0,if_pos rfl,tK,if_neg t0] using eq)
          exact (different (tK ▸ t.isLt) bk).elim
        · have E : r b=f t.val := by simpa only [g,j0,if_pos rfl,if_neg t0,if_neg tK] using eq
          exact (disj t.val (by omega) (central t0 tK) b E.symm).elim
    · by_cases t0 : t.val=0
      · by_cases jK : j.val=k
        · have cb : c=b := cap_root_inj edge
            (by simpa only [g,t0,if_pos rfl,jK,if_neg j0] using eq)
          exact (different (jK ▸ j.isLt) cb.symm).elim
        · have E : f j.val=r b := by simpa only [g,t0,if_pos rfl,if_neg j0,if_neg jK] using eq
          exact (disj j.val (by omega) (central j0 jK) b E).elim
      · by_cases jK : j.val=k
        · by_cases tK : t.val=k
          · exact Fin.ext (jK.trans tK.symm)
          · have E : r c=f t.val := by simpa only [g,if_neg j0,if_neg t0,jK,if_pos rfl,if_neg tK] using eq
            exact (disj t.val (by omega) (central t0 tK) c E.symm).elim
        · by_cases tK : t.val=k
          · have E : f j.val=r c := by simpa only [g,if_neg j0,if_neg t0,tK,if_pos rfl,if_neg jK] using eq
            exact (disj j.val (by omega) (central j0 jK) c E).elim
          · refine Fin.ext (inj _ _ (by omega) (central j0 jK) (by omega) (central t0 tK) ?_)
            simpa only [g,if_neg j0,if_neg t0,if_neg jK,if_neg tK] using eq
  · intro j
    have jl := j.isLt
    by_cases j0 : j.val=0
    · rw [show j=0 from Fin.ext j0,zero_add,z,o]
      exact entr
    by_cases jK : j.val=k
    · have endval : (j+1).val=0 := by
        rw [Fin.val_add,on,show j.val+1=n by omega,Nat.mod_self]
      have be := different (by omega : k<n)
      have ed : A.Adj (r c) (r b) := by
        cases b <;> cases c
        · exact (be rfl).elim
        · exact edge.symm
        · exact edge
        · exact (be rfl).elim
      simpa only [g,if_neg j0,jK,if_pos rfl,endval] using ed
    by_cases jLast : j.val+1=k
    · have jl' : j.val=k-1 := by omega
      have gj : g j=f (k-1) := by
        change (if j.val=0 then r b else if j.val=k then r c else f j.val)=f (k-1)
        rw [if_neg j0,if_neg jK,jl']
      rw [gj]
      by_cases ends : n=k
      · have endval : (j+1).val=0 := by
          rw [Fin.val_add,on,jLast]
          change k % n=0
          rw [ends,Nat.mod_self]
        have bc : b=c := by
          by_cases yes : b=c
          · exact yes
          · have hh : (if b=c then k else k+1)=k+1 := if_neg yes
            change (if b=c then k else k+1)=k at ends
            omega
        have endeq : j+1=0 := Fin.ext endval
        rw [endeq,z,bc]
        exact exit
      · have endval : (j+1).val=k := by
          rw [Fin.val_add,on,jLast,Nat.mod_eq_of_lt (by omega : k<n)]
        have kz : k≠0 := by omega
        have gj' : g (j+1)=r c := by
          change (if (j+1).val=0 then r b else if (j+1).val=k then r c else f (j+1).val)=r c
          rw [endval,if_neg kz,if_pos rfl]
        rwa [gj']
    · have new : j.val+1<k := by omega
      have endval : (j+1).val=j.val+1 := by
        rw [Fin.val_add,on,Nat.mod_eq_of_lt (by omega : j.val+1<n)]
      have nz : j.val+1≠0 := by omega
      simpa only [g,if_neg j0,if_neg jK,endval,if_neg nz,if_neg jLast] using step j.val (by omega) new

#print axioms close_arc
end KelmansCactus.FourRingCycleArc
