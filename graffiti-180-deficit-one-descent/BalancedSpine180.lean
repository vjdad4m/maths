import TwoRigidity180

set_option warningAsError true
namespace Minimal180.DescentOne.FailedTwo
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 OddBlock CutGain
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {r : V} {odd : Bool} {A : Finset V} (h : FailedTwo G r odd A)
include h

/-- If the root's memberships agree, a putative upper deficit-two failure
has one descending disagreement spine attached to a wholly unmarked vertex. -/
theorem balanced_spine :
    let P := parity G r odd
    let D := (A∪P)\(A∩P)
    r∉D → ∃ t w, Spine G r D t ∧ G.Adj t w ∧ w∉A∪P := by
  classical
  intro P D root
  let d (v : V) := G.dist v r
  obtain ⟨a,aa,ap⟩ := Finset.not_subset.mp h.not_confined
  have ad : a∈D := mem_sdiff.mpr ⟨mem_union_left _ aa,fun m => ap (mem_inter.mp m).2⟩
  obtain ⟨t,td,minimal⟩ := exists_min_image D d ⟨a,ad⟩
  have nr {i : V} (id : i∈D) : i≠r := fun eq => root (eq ▸ id)
  obtain ⟨w,tw,dt⟩ := Graffiti169.exists_predecessor G h.connected r t (nr td)
  change d t=d w+1 at dt
  have absent {v : V} (lt : d v<d t) : v∉D := fun m => (not_lt_of_ge (minimal v m)) lt
  have wd := absent (show d w<d t by omega)
  have opp : t∈P ↔ w∉P := by
    change t∈parity G r odd ↔ w∉parity G r odd
    simp only [mem_parity]
    change d t%2=odd.toNat ↔ ¬d w%2=odd.toNat
    cases odd <;> simp only [Bool.toNat_true,Bool.toNat_false] <;> omega
  have both := mem_sdiff.mp td
  have same : w∈A ↔ w∈P := by
    change w∉(A∪P)\(A∩P) at wd
    simp only [mem_sdiff,mem_union,mem_inter] at wd
    tauto
  have no : ¬(t∈A ∧ w∈A) := fun pair => h.independent t pair.1 w pair.2 tw.ne tw
  have tip : t∈P := by
    have m := mem_union.mp both.1
    tauto
  have free : w∉A∪P := by have := opp.mp tip; simp only [mem_union]; tauto
  have out {v i j : V} (vd : v∈D) (vi : G.Adj v i) (vj : G.Adj v j)
      (di : d i=d v+1) (dj : d j=d v+1) : i=j := h.outward (mem_sdiff.mp vd).1 (nr vd) vi vj di dj
  let basic (v : V) := if vr : v=r then r else (Graffiti169.exists_predecessor G h.connected r v vr).choose
  have std (v : V) (vr : v≠r) : G.Adj v (basic v) ∧ d v=d (basic v)+1 := by
    simpa [basic,d,vr] using (Graffiti169.exists_predecessor G h.connected r v vr).choose_spec
  have stay {i q : V} (id : i∈D) (it : i≠t) (iq : G.Adj i q) (step : d i=d q+1) : q∈D := by
    let p (v : V) := if v=i then q else basic v
    have down (v : V) (vr : v≠r) : G.Adj v (p v) ∧ d v=d (p v)+1 := by
      by_cases vi : v=i
      · subst v; simpa [p] using And.intro iq step
      · simpa [p,vi] using std v vr
    obtain ⟨M,mg,tree,cross,take,star⟩ := predecessor_tree G h.connected r odd p down
    obtain ⟨l,m,rl,rm,lm⟩ := block_neighbors G h.connected h.order h.block r
    have rt : r∉leaves M := fun lf => lm (leaf_unique M lf (star l rl) (star m rm))
    have cnt := (h.rigid M tree mg rt cross).2
    change (M.edgeFinset∩D.sym2).card+1=D.card at cnt
    rw [chosen_parent_count M tree r D p d (fun v vr => (down v vr).2) take] at cnt
    let F := (D.erase r).filter (fun v => p v∈D)
    have low := (down t (nr td)).2
    have off := absent (show d (p t)<d t by omega)
    have inc : F⊆D.erase t := by
      intro v f
      obtain ⟨ve,ps⟩ := mem_filter.mp f
      exact mem_erase.mpr ⟨fun eq => off (eq ▸ ps),mem_of_mem_erase ve⟩
    have size := card_erase_add_one td
    have eq : F=D.erase t := eq_of_subset_of_card_le inc (by change _≤((D.erase r).filter _).card; omega)
    have fi : i∈F := eq ▸ mem_erase.mpr ⟨it,id⟩
    simpa [p] using (mem_filter.mp fi).2
  have prev {i : V} (id : i∈D) (it : i≠t) : basic i∈D := stay id it (std i (nr id)).1 (std i (nr id)).2
  have unique (k : ℕ) : ∀ i∈D, ∀ j∈D, d i=k → d j=k → i=j := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i im j jm ik jk
      have first {v : V} (vd : v∈D) (eq : d v=d t) : v=t := by
        apply Classical.byContradiction
        intro vt
        have pp := minimal _ (prev vd vt)
        have less := (std v (nr vd)).2
        omega
      by_cases it : i=t
      · exact it.trans (first jm (by rw [←it,ik,jk])).symm
      by_cases jt : j=t
      · exact (first im (by rw [←jt,ik,jk])).trans jt.symm
      obtain ⟨ei,di⟩ := std i (nr im)
      obtain ⟨ej,dj⟩ := std j (nr jm)
      have eq := ih (d (basic i)) (by omega) _ (prev im it) _ (prev jm jt) rfl (by omega)
      exact out (prev im it) ei.symm (eq ▸ ej.symm) di (by simpa only [eq] using dj)
  refine ⟨t,w,⟨root,td,minimal,fun i im j jm eq => unique _ i im j jm rfl eq.symm,?_,
    fun _ vd _ _ => out vd,⟨a,mem_erase.mpr ⟨fun e => ap (e ▸ tip),ad⟩⟩⟩,tw,free⟩
  intro i im it
  obtain ⟨e,di⟩ := std i (nr im)
  refine ⟨basic i,prev im it,e.symm,di,?_⟩
  intro z ze dz
  change d i=d z+1 at dz
  exact unique _ z (stay im it ze.symm dz) _ (prev im it) rfl (by omega)

#print axioms balanced_spine
end Minimal180.DescentOne.FailedTwo
