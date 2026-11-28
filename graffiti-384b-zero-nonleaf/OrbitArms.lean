import HallArms

namespace Graffiti384b.OddStars.HallArms
open Finset Function SimpleGraph OneEar
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
private theorem orbit_collision {s : V→V} {D A : Set V}
    (inj : Set.InjOn s D) (avoids : ∀x∈D,s x∉A) {a b : V} (aa : a∈A) (ba : b∈A)
    {n m : ℕ} (en : ∀i<n,s^[i] a∈D) (em : ∀j<m,s^[j] b∈D)
    (hit : s^[n] a=s^[m] b) : n=m ∧ a=b := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => exact ⟨rfl,hit⟩
    | succ m =>
      rw [iterate_succ_apply'] at hit
      exact (avoids _ (em m (by omega)) (hit ▸ aa)).elim
  | succ n ih =>
    cases m with
    | zero =>
      rw [iterate_succ_apply'] at hit
      exact (avoids _ (en n (by omega)) (hit.symm ▸ ba)).elim
    | succ m =>
      rw [iterate_succ_apply',iterate_succ_apply'] at hit
      obtain ⟨eq,ab⟩ := ih (fun i hi => en i (by omega)) (fun j hj => em j (by omega))
        (inj (en n (by omega)) (em m (by omega)) hit)
      exact ⟨by omega,ab⟩

omit [DecidableEq V] in
private theorem eventually_exits {s : V→V} {D A : Set V} (inj : Set.InjOn s D)
    (avoids : ∀x∈D,s x∉A) {a : V} (aa : a∈A) : ∃k,s^[k] a∉D := by
  by_contra! never
  let f : Fin (Fintype.card V+1) → V := fun i => s^[i.val] a
  have good : Injective f := fun i j hit => Fin.ext (orbit_collision inj avoids aa aa
    (n:=i.val) (m:=j.val) (fun u _ => never u) (fun v _ => never v) hit).1
  have size := Fintype.card_le_of_injective f good
  simp at size

variable (J : SimpleGraph V) [DecidableRel J.Adj]

/-- Given the two start neighbors a,b, a feasible matching produces disjoint
simple arms to two distinct sink neighbors. Each arm avoids both terminals. -/
theorem extract_arms {e z a b : V} (ab : a≠b) (ea : J.Adj e a) (eb : J.Adj e b)
    (ad : a∈domain J e z) (bd : b∈domain J e z)
    (matching : ∃f : (v : domain J e z) → V, Injective f ∧ ∀v : domain J e z,f v∈options J e z v) :
    let K := inside J ({e,z}ᶜ)
    ∃c d : V, J.Adj z c ∧ J.Adj z d ∧ c≠d ∧
      ∃n m : ℕ, ∃p : Route K e a c n, ∃q : Route K e b d m,
      ∀i≤n,∀j≤m,p.atIdx i≠q.atIdx j := by
  classical
  let K := inside J ({e,z}ᶜ)
  let D := domain J e z
  let A := J.neighborFinset e
  obtain ⟨f,inj,hf⟩ := matching
  let s (x : V) := if h : x∈D then f ⟨x,h⟩ else x
  have eq {x : V} (h : x∈D) : s x=f ⟨x,h⟩ := dif_pos h
  have si : Set.InjOn s (D : Set V) := by
    intro x hx y hy hh
    rw [eq hx,eq hy] at hh
    exact congrArg Subtype.val (inj hh)
  have sa : ∀x∈(D : Set V),s x∉(A : Set V) := by
    intro x hx
    rw [eq hx]
    exact (mem_sdiff.mp (hf ⟨x,hx⟩)).2
  have clean {x : V} (h : x∈D) : x∉({e,z}:Finset V) :=
    fun m => mem_compl.mp h (mem_union_left _ m)
  have opt {x : V} (h : x∈D) : s x=x ∨ K.Adj x (s x) := by
    rw [eq h]
    rcases mem_insert.mp (mem_sdiff.mp (hf ⟨x,h⟩)).1 with v|v
    · exact Or.inl v
    · exact Or.inr ((K.mem_neighborFinset ..).mp v)
  have arm {x : V} (xd : x∈D) (xa : x∈A) :
      ∃n : ℕ, (∀i<n,s^[i] x∈D) ∧ J.Adj z (s^[n] x) ∧
       ∃p : Route K e x (s^[n] x) n, ∀i,p.atIdx i=s^[i] x := by
    have ex := eventually_exits si sa xa
    let n := Nat.find ex
    have gone : s^[n] x∉D := Nat.find_spec ex
    have good (i : ℕ) (hi : i<n) : s^[i] x∈D := by
      by_contra h
      have l := Nat.find_min' ex h
      omega
    have uq : ∀i≤n,∀j≤n,s^[i] x=s^[j] x → i=j :=
      fun i hi j hj hit => (orbit_collision si sa xa xa (fun l h => good l (by omega))
        (fun l h => good l (by omega)) hit).1
    have step (i : ℕ) (hi : i<n) : K.Adj (s^[i] x) (s^[i+1] x) := by
      have different : s^[i+1] x≠s^[i] x := fun h => by have := uq (i+1) (by omega) i (by omega) h; omega
      rw [iterate_succ_apply'] at different ⊢
      exact (opt (good i hi)).resolve_left different
    have exterior (i : ℕ) (hi : i≤n) : s^[i] x∉({e,z}:Finset V) := by
      cases i with
      | zero => exact clean xd
      | succ i => exact mem_compl.mp (step i (by omega)).2.2
    have endpoint : J.Adj z (s^[n] x) := by
      by_contra neg
      apply gone
      exact mem_compl.mpr (fun h => (mem_union.mp h).elim (exterior n le_rfl)
        (fun m => neg ((J.mem_neighborFinset ..).mp m)))
    exact ⟨n,good,endpoint,⟨fun i => s^[i] x,rfl,rfl,step,uq,fun i hi ve =>
      exterior i hi (mem_insert.mpr (Or.inl ve))⟩,fun _ => rfl⟩
  have aa : a∈A := (J.mem_neighborFinset ..).mpr ea
  have ba : b∈A := (J.mem_neighborFinset ..).mpr eb
  obtain ⟨n,en,zc,p,pa⟩ := arm ad aa
  obtain ⟨m,em,zd,q,qb⟩ := arm bd ba
  have sep (i : ℕ) (hi : i≤n) (j : ℕ) (hj : j≤m) : s^[i] a≠s^[j] b := fun hit =>
    ab (orbit_collision si sa aa ba (fun l h => en l (by omega)) (fun l h => em l (by omega)) hit).2
  exact ⟨_,_,zc,zd,sep n le_rfl m le_rfl,n,m,p,q,fun i hi j hj => by rw [pa,qb]; exact sep i hi j hj⟩

end Graffiti384b.OddStars.HallArms
#print axioms Graffiti384b.OddStars.HallArms.extract_arms