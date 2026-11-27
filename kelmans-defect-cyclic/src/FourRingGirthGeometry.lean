import FourRingGirthEquivalence
import Mathlib.Combinatorics.SimpleGraph.Girth

open SimpleGraph KelmansCactus.NearPerfectReplica.Layout
namespace KelmansCactus.FourRingGirthGeometry
variable {V : Type*} {G : SimpleGraph V}

private theorem walk_segment (f : ℕ→V) (step : ∀j,G.Adj (f j) (f (j+1)))
    (t n : ℕ) : ∃ w : G.Walk (f t) (f (t+n)),
    w.length=n ∧
    (∀ j,j≤n→w.getVert j=f (t+j)) ∧
    ∀ e,e∈w.edges→∃ j,j<n ∧ e=s(f (t+j),f (t+j+1)) := by
  induction n generalizing t with
  | zero =>
    refine ⟨.nil, rfl, ?_,?_⟩
    · intro j hj
      have e : j=0 := by omega
      subst j
      rfl
    · intro e mem
      simp at mem
  | succ n ih =>
    obtain ⟨p,pl,pv,pe⟩ := ih (t+1)
    have e : f (t+1+n)=f (t+(n+1)) := by rw [show t+1+n=t+(n+1) by omega]
    let p' := p.copy rfl e
    refine ⟨.cons (step t) p', ?_,?_,?_⟩
    · simp [p',pl]
    · intro j hj
      cases j with
      | zero => rfl
      | succ j =>
        rw [Walk.getVert_cons_succ]
        simpa [p',show t+1+j=t+(j+1) by omega] using pv j (by omega)
    · intro a mem
      rw [Walk.edges_cons,List.mem_cons] at mem
      rcases mem with rfl|member
      · exact ⟨0,by omega,rfl⟩
      · have hp : a∈p.edges := by simpa [p'] using member
        obtain ⟨j,jlt,he⟩ := pe _ hp
        refine ⟨j+1,by omega,?_⟩
        rw [show t+(j+1)=t+1+j by omega]
        exact he

private def natCycle {n : ℕ} [NeZero n] (f : Fin n→V) (j : ℕ) : V := f j

private theorem nat_cycle_wrap {n : ℕ} [NeZero n] (f : Fin n→V) :
    natCycle f n=natCycle f 0 := by
  unfold natCycle
  congr 1
  apply Fin.ext
  change n%n=0%n
  simp

private theorem nat_cycle_inj {n : ℕ} [NeZero n] {f : Fin n→V} (inj : Function.Injective f)
    {i j : ℕ} (hi : i<n) (hj : j<n) (eq : natCycle f i=natCycle f j) : i=j := by
  have h := congrArg Fin.val (inj eq)
  change i%n=j%n at h
  rwa [Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hj] at h

private theorem nat_cycle_inj_shifted {n : ℕ} [NeZero n] {f : Fin n→V} (inj : Function.Injective f)
    {i j : ℕ} (hi : 1 ≤ i) (hin : i ≤ n) (hj : 1 ≤ j) (hjn : j ≤ n)
    (eq : natCycle f i=natCycle f j) : i=j := by
  by_cases ei : i=n
  · by_cases ej : j=n
    · omega
    · rw [ei,nat_cycle_wrap] at eq
      have := nat_cycle_inj inj (show 0<n by omega) (show j<n by omega) eq
      omega
  · by_cases ej : j=n
    · rw [ej,nat_cycle_wrap] at eq
      have := nat_cycle_inj inj (show i<n by omega) (show 0<n by omega) eq
      omega
    · exact nat_cycle_inj inj (by omega) (by omega) eq

/-- Translate the cyclic enumeration to Mathlib's cycle-walk
definition, preserving the number of vertices/edges. -/
theorem shortCycle_iff_walk {n : ℕ} [NeZero n] (n3 : 3≤n) :
    HasShortCycle G n ↔ ∃ (v : V) (w : G.Walk v v),w.IsCycle ∧ w.length=n := by
  constructor
  · rintro ⟨f,cy⟩
    let g := natCycle f
    have hd (j : ℕ) : G.Adj (g j) (g (j+1)) := by
      change G.Adj (f j) (f (↑(j+1)))
      have r : ((j+1 : ℕ):Fin n)=(j:Fin n)+1 := by
        apply Fin.ext
        exact Nat.add_mod _ _ _
      rw [r]
      exact cy.2 _
    let m := n-1
    have one : 1+m=n := by dsimp [m]; omega
    obtain ⟨w,wl,wv,we⟩ := walk_segment g hd 1 m
    have er : g (1+m)=g 0 := by change natCycle f (1+m)=natCycle f 0; rw [one,nat_cycle_wrap]
    let w' := w.copy rfl er
    have wl' : w'.length=m := by simp [w',wl]
    have pv (j : ℕ) (hj : j≤m) : w'.getVert j=g (1+j) := by simpa [w'] using wv j hj
    have path : w'.IsPath := by
      apply (Walk.IsPath.getVert_injOn_iff _).mp
      intro i hi j hj eq
      change i≤w'.length at hi
      change j≤w'.length at hj
      rw [wl'] at hi hj
      rw [pv i hi,pv j hj] at eq
      have e := nat_cycle_inj_shifted cy.1
        (show 1≤1+i by omega) (show 1+i≤n by omega)
        (show 1≤1+j by omega) (show 1+j≤n by omega) eq
      omega
    have no : s(g 0,g 1)∉w'.edges := by
      intro mem
      have mW : s(g 0,g 1)∈w.edges := by simpa [w'] using mem
      obtain ⟨j,jlt,he⟩ := we _ mW
      rcases Sym2.eq_iff.mp he with ⟨a,_⟩|⟨a,b⟩
      · have e := nat_cycle_inj cy.1 (show 0<n by omega) (show 1+j<n by omega) a
        omega
      · have e := nat_cycle_inj cy.1 (show 1<n by omega) (show 1+j<n by omega) b
        have j0 : j=0 := by omega
        subst j
        have e := nat_cycle_inj cy.1 (show 0<n by omega) (show 2<n by omega) a
        omega
    refine ⟨g 0,.cons (hd 0) w',(Walk.cons_isCycle_iff _ _).mpr ⟨path,no⟩,?_⟩
    rw [Walk.length_cons,wl']
    omega
  · rintro ⟨v,w,cy,len⟩
    refine ⟨fun i=>w.getVert i.val,⟨?_,?_⟩⟩
    · intro i j e
      apply Fin.ext
      apply cy.getVert_injOn'
      · change i.val≤w.length-1
        rw [len]
        omega
      · change j.val≤w.length-1
        rw [len]
        omega
      · exact e
    · intro i
      have h := i.isLt
      have a := w.adj_getVert_succ (i:=i.val) (by omega)
      have one : (1:Fin n).val=1 := Nat.mod_eq_of_lt (show 1<n by omega)
      by_cases endpos : i.val+1=n
      · have nov : (i+1).val=0 := by rw [Fin.val_add,one,endpos,Nat.mod_self]
        change G.Adj (w.getVert i.val) (w.getVert (i+1).val)
        rw [nov,Walk.getVert_zero]
        have eq : i.val+1=w.length := by omega
        simpa only [eq,Walk.getVert_length] using a
      · have nov : (i+1).val=i.val+1 := by rw [Fin.val_add,one,Nat.mod_eq_of_lt (by omega)]
        change G.Adj (w.getVert i.val) (w.getVert (i+1).val)
        rw [nov]
        exact a

/-- The formal no-short-cycle condition is Mathlib's extended
girth lower bound, including the acyclic case. -/
theorem noCycles_iff_egirth (g : ℕ) : NoCyclesBelow G g ↔ (g:ℕ∞)≤G.egirth := by
  rw [le_egirth]
  constructor
  · intro clean v w cyc
    have n3 := cyc.three_le_length
    by_contra! small
    have lt : w.length<g := by exact_mod_cast small
    letI inst : NeZero w.length := ⟨by omega⟩
    exact clean _ n3 lt inst ((shortCycle_iff_walk n3).mpr ⟨v,w,cyc,rfl⟩)
  · intro h n n3 small inst short
    letI : NeZero n := inst
    obtain ⟨v,w,c,len⟩ := (shortCycle_iff_walk n3).mp short
    have le : g≤w.length := by exact_mod_cast h v w c
    omega

#print axioms shortCycle_iff_walk
#print axioms noCycles_iff_egirth
end KelmansCactus.FourRingGirthGeometry
