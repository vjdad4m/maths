import DualLayer180

set_option warningAsError true
namespace Minimal180.RootEar
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 OddBlock CutGain DescentOne
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The two disagreement branches cannot merge. A first double predecessor
would force a singleton final layer with every earlier vertex marked singly. -/
theorem unique_prior {G : SimpleGraph V} {r : V} {odd : Bool} {A : Finset V}
    (h : FailedTwo G r odd A) {v p : V} :
    let P := parity G r odd
    let D := (A∪P)\(A∩P)
    v∈D → G.Adj p v → G.dist v r=G.dist p r+1 → Arc G r p v := by
  classical
  intro P D vd pv step
  refine ⟨pv,step,?_⟩
  intro q qv stepQ
  apply Classical.byContradiction
  intro qp
  have pd := predecessor_closed h vd pv.symm step
  have qd := predecessor_closed h vd qv.symm stepQ
  have eq : G.dist p r=G.dist q r := by omega
  have ⟨layer,earlier⟩ := dual_layer h pd qd (Ne.symm qp) eq
  have pr : p≠r := by
    intro e
    rw [e,dist_self] at eq
    exact qp ((h.connected.dist_eq_zero_iff.mp eq.symm).trans e.symm)
  have qr : q≠r := by
    intro e
    rw [e,dist_self] at eq
    exact pr (h.connected.dist_eq_zero_iff.mp eq)
  have vr : v≠r := by intro e; rw [e,dist_self] at step; omega
  have alone (z : V) (dz : G.dist z r=G.dist v r) : z=v := by
    have zr : z≠r := by intro e; rw [e,dist_self] at dz; omega
    obtain ⟨u,zu,du⟩ := Graffiti169.exists_predecessor G h.connected r z zr
    rcases layer u (by omega) with up|uq
    · subst u; exact h.outward (mem_sdiff.mp pd).1 pr zu.symm pv du step
    · subst u; exact h.outward (mem_sdiff.mp qd).1 qr zu.symm qv du stepQ
  obtain ⟨_,_,w,_,out⟩ := free_attachment h
  have all := last_singleton h.connected h.block vr alone w
  have wd : w∈D := by
    by_cases same : G.dist w r=G.dist v r
    · exact alone w same ▸ vd
    · exact earlier w (by omega)
  exact out (mem_sdiff.mp wd).1

/-- Every alternating edge inside D points to the unique predecessor of
its deeper endpoint. A spanning parity tree with an internal root must
therefore retain every such edge. -/
theorem forced_vertical {G M : SimpleGraph V} {r : V} {odd : Bool} {A : Finset V}
    (h : FailedTwo G r odd A) (tree : M.IsTree) (sub : M≤alternating G (parity G r odd))
    (internal : r∉leaves M) :
    let P := parity G r odd
    let D := (A∪P)\(A∩P)
    ∀ {i j}, i∈D → j∈D → (alternating G P).Adj i j → M.Adj i j := by
  classical
  intro P D
  let H := alternating G P
  let p (v : V) := if vr : v=r then r else (Graffiti169.exists_predecessor G h.connected r v vr).choose
  have down (v : V) (vr : v≠r) : G.Adj v (p v) ∧ G.dist v r=G.dist (p v) r+1 := by
    simpa [p,vr] using (Graffiti169.exists_predecessor G h.connected r v vr).choose_spec
  let f (v : V) := s(v,p v)
  have cover : H.edgeFinset∩D.sym2⊆(D.erase r).image f := by
    intro e mem
    induction e using Sym2.ind with
    | _ i j =>
      obtain ⟨old,inside⟩ := mem_inter.mp mem
      have ij : H.Adj i j := mem_edgeFinset.mp old
      obtain ⟨id,jd⟩ := mk_mem_sym2_iff.mp inside
      have near := h.connected.dist_triangle (u:=i) (v:=j) (w:=r)
      have far := h.connected.dist_triangle (u:=j) (v:=i) (w:=r)
      rw [dist_eq_one_iff_adj.mpr ij.1] at near
      rw [dist_eq_one_iff_adj.mpr ij.1.symm] at far
      have diff : G.dist i r≠G.dist j r := by
        intro eq
        have op := ij.2
        change i∈parity G r odd ↔ j∉parity G r odd at op
        simp only [mem_parity,eq] at op
        tauto
      have shallow {v z : V} (vd : v∈D) (vz : G.Adj v z) (inc : G.dist v r=G.dist z r+1) :
          v≠r ∧ p v=z := by
        have vr : v≠r := by intro eq; rw [eq,dist_self] at inc; omega
        have regular := down v vr
        exact ⟨vr,(unique_prior h vd vz.symm inc).2.2 _ regular.1.symm regular.2⟩
      by_cases lt : G.dist j r<G.dist i r
      · have ⟨ir,eq⟩ := shallow id ij.1 (by omega)
        exact mem_image.mpr ⟨i,mem_erase.mpr ⟨ir,id⟩,by simp only [f,eq]⟩
      · have ⟨jr,eq⟩ := shallow jd ij.1.symm (by omega)
        exact mem_image.mpr ⟨j,mem_erase.mpr ⟨jr,jd⟩,by simp only [f,eq,Sym2.eq_swap]⟩
  have count := (h.rigid M tree (fun _ _ e => (sub e).1) internal fun e => (sub e).2).2
  change (M.edgeFinset∩D.sym2).card+1=D.card at count
  have rd : r∈D := h.root_disagreement
  have size := card_erase_add_one rd
  have cap := (card_le_card cover).trans card_image_le
  have inc : M.edgeFinset∩D.sym2⊆H.edgeFinset∩D.sym2 := fun _ m =>
    mem_inter.mpr ⟨edgeFinset_mono sub (mem_inter.mp m).1,(mem_inter.mp m).2⟩
  have eq := eq_of_subset_of_card_le inc (by omega)
  intro i j id jd e
  have mem : s(i,j)∈M.edgeFinset∩D.sym2 := by rw [eq]; exact mem_inter.mpr ⟨mem_edgeFinset.mpr e,mk_mem_sym2_iff.mpr ⟨id,jd⟩⟩
  exact mem_edgeFinset.mp (mem_inter.mp mem).1

#print axioms unique_prior
#print axioms forced_vertical
end Minimal180.RootEar
