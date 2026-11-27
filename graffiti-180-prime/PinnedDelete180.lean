import PinnedTools180

set_option warningAsError true
namespace Minimal180.Substitution
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
open Classical
variable {V B : Type*} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]
variable {H : SimpleGraph V} {G : SimpleGraph B} {f : V→B}

theorem erase_pull_count (X : Finset V) (x : V) :
    (pull (fun z : ↥(univ.erase x) => z.val) X).card+(if x∈X then 1 else 0)=X.card := by
  classical
  have eq : X\(univ.erase x)=X∩{x} := by ext a; by_cases ax : a=x <;> simp [ax]
  have cnt := pull_card_kept (univ.erase x) X
  rw [eq] at cnt
  by_cases xm : x∈X
  · simpa [xm,inter_singleton_of_mem xm] using cnt
  · simpa [xm,inter_singleton_of_not_mem xm] using cnt

/-- A failing pinned marking survives deletion of a nonroot vertex in a
nonsingleton bag whenever that vertex is unpinned or has a pinned false
twin. The same root, parity, and restriction of the marking are used. -/
theorem Bags.pinDelete (h : Bags H G f) (gc : G.Connected) (ord : 1<Fintype.card B)
    (high : 2<Fintype.card V) (A : Finset V) (ai : Indep H A) (r x y : V) (xr : x≠r)
    (xy : x≠y) (mate : f x=f y) (p : Bool)
    (step : x∈A∩parity H r p → ∃ t∈A∩parity H r p,FalseTwins H x t)
    (bad : ¬Pinned H r p A (A∩parity H r p)) :
    let S := univ.erase x
    let j : ↥S := ⟨r,mem_erase.mpr ⟨xr.symm,mem_univ _⟩⟩
    let C := pull (fun z : ↥S => z.val)
    let Q := parity (side H S) j p
    (side H S).Connected ∧ 1<S.card ∧ S.card<Fintype.card V ∧ Indep (side H S) (C A) ∧
      ¬Pinned (side H S) j p (C A) (C A∩Q) := by
  classical
  intro S j C Q
  let P := parity H r p
  let U := eligible A P r
  let D := A∩P
  have keep (i : B) : ∃ z∈S,f z=i := by
    obtain ⟨z,zi⟩ := h.onto i
    by_cases eq : z=x
    · exact ⟨y,mem_erase.mpr ⟨xy.symm,mem_univ _⟩,mate.symm.trans (eq ▸ zi)⟩
    · exact ⟨z,mem_erase.mpr ⟨eq,mem_univ _⟩,zi⟩
  have ret := h.retained S keep
  have count := Fintype.card_le_of_surjective _ ret.onto
  change Fintype.card B≤Fintype.card ↥S at count
  rw [Fintype.card_coe] at count
  have strict : S.card<Fintype.card V := by
    have := card_erase_add_one (mem_univ x)
    change (univ.erase x).card<Fintype.card V
    rw [card_univ] at this; omega
  refine ⟨ret.connected gc ord,by omega,strict,fun v vm w wm ne e =>
    ai _ (mem_pull.mp vm) _ (mem_pull.mp wm) (fun eq => ne (Subtype.ext eq)) e,?_⟩
  rintro ⟨Z,col,inc,ok⟩
  have ⟨pp,ue⟩ := pulled_mark h gc ord S keep j p A
  change Q=C P at pp
  change eligible (C A) Q j=C U at ue
  change 1+(C A).card+Q.card≤weightedLeaves (side H S) (eligible (C A) Q j)+Z.card at ok
  rw [ue,pp] at ok
  have nh := pin_nohub h gc ord high r p A ai bad
  have loss := h.retainedLoss gc (three_of_nohub G gc ord nh) nh S keep U
  change weightedLeaves (side H S) (C U)+U.card≤weightedLeaves H U+(C U).card at loss
  have covered {v : V} (vd : v∈D) (vx : v≠x) : v∈push Z := by
    let z : ↥S := ⟨v,mem_erase.mpr ⟨vx,mem_univ _⟩⟩
    apply (in_push z).mpr
    apply inc
    refine mem_inter.mpr ⟨mem_pull.mpr (mem_inter.mp vd).1,?_⟩
    change z∈Q
    rw [pp]; exact mem_pull.mpr (mem_inter.mp vd).2
  obtain ⟨Y,bip,all,mass⟩ : ∃ Y,TwoColor H Y ∧ D⊆Y ∧ Z.card+(if x∈D then 1 else 0)≤Y.card := by
    by_cases xd : x∈D
    · obtain ⟨t,td,tw⟩ := step xd
      have miss : x∉push Z := fun m => (mem_erase.mp (push_sub Z m)).1 rfl
      refine ⟨insert x (push Z),tw.paint (push_color H S col) (covered td tw.1.symm),?_,?_⟩
      · intro v vd
        by_cases eq : v=x
        · exact eq ▸ mem_insert_self ..
        · exact mem_insert_of_mem (covered vd eq)
      · simp [xd,card_insert_of_not_mem miss]
    · exact ⟨push Z,push_color H S col,fun v vd => covered vd (fun eq => xd (eq ▸ vd)),by simp [xd]⟩
  apply bad ⟨Y,bip,all,?_⟩
  have sz (X : Finset V) : (C X).card+(if x∈X then 1 else 0)=X.card := erase_pull_count X x
  have ac := sz A
  have pc := sz P
  have uc := sz U
  have bits : (if x∈A then 1 else 0)+(if x∈P then 1 else 0)=
      (if x∈U then 1 else 0)+(if x∈D then 1 else 0) := by
    by_cases a : x∈A <;> by_cases par : x∈P <;> simp [U,D,eligible_iff,xr,a,par]
  change 1+A.card+P.card≤weightedLeaves H U+Y.card
  omega

#print axioms erase_pull_count
#print axioms Bags.pinDelete
end Minimal180.Substitution
