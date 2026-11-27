import CoreSplit180
set_option warningAsError true
namespace Minimal180
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- Returning a tip with no old core neighbor attaches a pendant at the other
tip. Connectivity is exactly connectivity of the retained old core. -/
private theorem pendant_core (J : SimpleGraph V) (R : Finset V) (x y : V) (xy : x≠y)
    (xr : x∉R) (yr : y∈R) (no : ¬Dominates J R x) :
    Con (J⊔SimpleGraph.edge x y) (insert x R) ↔ Con J R := by
  classical
  let G := J⊔SimpleGraph.edge x y
  have add : G.Adj x y := Or.inr ((edge_adj ..).mpr ⟨Or.inl ⟨rfl,rfl⟩,xy⟩)
  have only (b:V) (hb:b∈R) (e:G.Adj x b) : b=y := by
    rcases e with e|e
    · exact (no ⟨b,hb,e⟩).elim
    · rcases ((edge_adj ..).mp e).1 with h|h
      · exact h.2
      · exact (xy h.1).elim
  have inside (a b:V) (ha:a∈R) (hb:b∈R) (e:G.Adj a b) : J.Adj a b := by
    rcases e with e|e
    · exact e
    · rcases ((edge_adj ..).mp e).1 with h|h
      · exact (xr (h.1 ▸ ha)).elim
      · exact (xr (h.2 ▸ hb)).elim
  constructor
  · intro con
    apply (connected_cuts J R).mpr
    refine ⟨⟨y,yr⟩,?_⟩
    intro f stable
    let g (i:V) := if i=x then f y else f i
    have same (i:V) (h:i∈R) : g i=f i := if_neg (fun (e:i=x) => xr (e ▸ h))
    have gy : g x=f y := if_pos rfl
    have both : OnEdges G (insert x R) g := by
      intro a ha b hb e
      rcases mem_insert.mp ha with rfl|ar
      · rcases mem_insert.mp hb with rfl|br
        · rfl
        · rw [gy,same b br,only b br e]
      · rcases mem_insert.mp hb with rfl|br
        · rw [gy,same a ar,only a ar e.symm]
        · rw [same a ar,same b br]
          exact stable a ar b br (inside a b ar br e)
    intro a ha b hb
    simpa only [same a ha,same b hb] using
      (((connected_cuts G _).mp con).2 g both a (mem_insert_of_mem ha) b (mem_insert_of_mem hb))
  · intro con
    apply (connected_cuts G _).mpr
    refine ⟨⟨x,mem_insert_self ..⟩,?_⟩
    intro f stable
    have eqR := ((connected_cuts J R).mp con).2 f
      (fun a ha b hb e => stable a (mem_insert_of_mem ha) b (mem_insert_of_mem hb) (Or.inl e))
    have all (a:V) (ha:a∈insert x R) : f a=f y := by
      rcases mem_insert.mp ha with rfl|ar
      · exact stable _ (mem_insert_self ..) y (mem_insert_of_mem yr) add
      · exact eqR a ar y yr
    exact fun a ha b hb => (all a ha).trans (all b hb).symm

/-- Exact test for a single replacement from a specified second certificate.
The only lost old domination that matters belongs to another leaf with no
edge to the returned tip. Neither a rank nor a tightness assumption is needed. -/
theorem single_split_iff (J : SimpleGraph V) (C : Finset V) (x y z : V) (xy : x≠y)
    (tip : NeedsTip J C (univ\C) x y) (zout : z∉C) (zy : z≠y) :
    let S := univ\C
    let R := S.erase z
    let G := J⊔SimpleGraph.edge x y
    let L := insert z (C.erase x)
    (Con G (univ\L) ∧ ∀ q∈L,Dominates G (univ\L) q) ↔
      Con J R ∧ ∀ q∈C.erase x, ¬J.Adj q x → Dominates J R q := by
  classical
  let S := univ\C
  let R := S.erase z
  let G := J⊔SimpleGraph.edge x y
  let L := insert z (C.erase x)
  have xc := tip.1
  have ys : y∈S := tip.2.1
  have zs : z∈S := by simp [S,zout]
  have yr : y∈R := mem_erase.mpr ⟨zy.symm,ys⟩
  have xr : x∉R := fun h => (mem_sdiff.mp (mem_of_mem_erase h)).2 xc
  have zx : z≠x := fun e => zout (e ▸ xc)
  have eq : univ\L=insert x R := by
    ext q
    by_cases qx : q=x
    · subst q; simp [L,zx.symm]
    · simp [L,R,S,qx]
  have no : ¬Dominates J R x := by
    rintro ⟨a,h,e⟩
    exact tip.2.2.2.1 ⟨a,mem_of_mem_erase h,e⟩
  have toJ {a b:V} (ax:a≠x) (ay:a≠y) (edge:G.Adj a b) : J.Adj a b := by
    rcases edge with edge|edge
    · exact edge
    · rcases ((edge_adj ..).mp edge).1 with h|h
      · exact (ax h.1).elim
      · exact (ay h.1).elim
  have zdom : Dominates J R z := by
    by_contra bad
    let f (a:V) := decide (a=z)
    have fixed : OnEdges J S f := by
      intro a ha b hb e
      by_cases az : a=z
      · have ed : J.Adj z b := az ▸ e
        exact False.elim (bad ⟨b,mem_erase.mpr ⟨ed.ne.symm,hb⟩,ed⟩)
      by_cases bz : b=z
      · have ed : J.Adj z a := bz ▸ e.symm
        exact False.elim (bad ⟨a,mem_erase.mpr ⟨az,ha⟩,ed⟩)
      simp [f,az,bz]
    have same := ((connected_cuts J S).mp tip.2.2.1).2 f fixed z zs y ys
    simp [f,zy.symm] at same
  change (Con G (univ\L) ∧ ∀ q∈L,Dominates G (univ\L) q) ↔ _
  rw [eq,pendant_core J R x y xy xr yr no]
  constructor
  · rintro ⟨conn,dom⟩
    refine ⟨conn,?_⟩
    intro q qc old
    obtain ⟨qx,qC⟩ := mem_erase.mp qc
    have qy : q≠y := fun e => (mem_sdiff.mp ys).2 (e ▸ qC)
    obtain ⟨a,ha,edge⟩ := dom q (mem_insert_of_mem qc)
    rcases mem_insert.mp ha with rfl|ar
    · exact (old (toJ qx qy edge)).elim
    · exact ⟨a,ar,toJ qx qy edge⟩
  · rintro ⟨conn,dom⟩
    refine ⟨conn,?_⟩
    intro q h
    rcases mem_insert.mp h with rfl|qc
    · obtain ⟨a,ar,e⟩ := zdom
      exact ⟨a,mem_insert_of_mem ar,Or.inl e⟩
    · by_cases e : J.Adj q x
      · exact ⟨x,mem_insert_self ..,Or.inl e⟩
      · obtain ⟨a,ar,qa⟩ := dom q qc e
        exact ⟨a,mem_insert_of_mem ar,Or.inl qa⟩

/-- A failed single replacement exposes either a disconnected old core
after deletion, or a leaf for which the released vertex was the unique old
core neighbor and which the returning tip cannot dominate. -/
theorem single_failure_iff (J : SimpleGraph V) (C : Finset V) (x y z : V) (xy : x≠y)
    (tip : NeedsTip J C (univ\C) x y) (zout : z∉C) (zy : z≠y) :
    let S := univ\C
    let R := S.erase z
    let G := J⊔SimpleGraph.edge x y
    let L := insert z (C.erase x)
    ¬(Con G (univ\L) ∧ ∀ q∈L,Dominates G (univ\L) q) ↔
      ¬Con J R ∨ ∃ q∈C.erase x, ¬J.Adj q x ∧ J.Adj q z ∧ ∀ a∈S,J.Adj q a → a=z := by
  classical
  let S := univ\C
  let R := S.erase z
  let G := J⊔SimpleGraph.edge x y
  let L := insert z (C.erase x)
  change ¬(Con G (univ\L) ∧ ∀ q∈L,Dominates G (univ\L) q) ↔ _
  have test : (Con G (univ\L) ∧ ∀ q∈L,Dominates G (univ\L) q) ↔
      Con J R ∧ ∀ q∈C.erase x, ¬J.Adj q x → Dominates J R q :=
    single_split_iff J C x y z xy tip zout zy
  rw [test]
  constructor
  · intro fail
    by_cases conn : Con J R
    · right
      have no : ¬(∀ q∈C.erase x, ¬J.Adj q x → Dominates J R q) := fun h => fail ⟨conn,h⟩
      push_neg at no
      obtain ⟨q,qc,unused,missing⟩ := no
      have only (a:V) (ha:a∈S) (e:J.Adj q a) : a=z := by
        by_contra ne
        exact missing ⟨a,mem_erase.mpr ⟨ne,ha⟩,e⟩
      obtain ⟨a,ha,edge⟩ := tip.2.2.2.2 q (mem_of_mem_erase qc) (mem_erase.mp qc).1
      exact ⟨q,qc,unused,only a ha edge ▸ edge,only⟩
    · exact Or.inl conn
  · rintro (bad|⟨q,qc,unused,_,only⟩) ⟨conn,dom⟩
    · exact bad conn
    · obtain ⟨a,ar,e⟩ := dom q qc unused
      exact (mem_erase.mp ar).1 (only a (mem_of_mem_erase ar) e)

/-- At equality in the tip degree bound, the old neighborhood fixes the
entire second certificate in its orientation. -/
theorem second_neighborhood (J : SimpleGraph V) [DecidableRel J.Adj] (C : Finset V)
    (x y : V) (k : ℕ) (size : C.card=k+1) (tip : NeedsTip J C (univ\C) x y) :
    insert x (J.neighborFinset x)⊆C ∧ J.degree x≤k ∧
      (C=insert x (J.neighborFinset x) ↔ J.degree x=k) := by
  classical
  have sub : insert x (J.neighborFinset x)⊆C := by
    intro a ha
    rcases mem_insert.mp ha with eq|adj
    · exact eq ▸ tip.1
    · by_contra out
      exact tip.2.2.2.1 ⟨a,mem_sdiff.mpr ⟨mem_univ _,out⟩,(J.mem_neighborFinset x a).mp adj⟩
  have ct : (insert x (J.neighborFinset x)).card=J.degree x+1 := by
    rw [card_insert_of_not_mem (J.not_mem_neighborFinset_self x),card_neighborFinset_eq_degree]
  have le := card_le_card sub
  refine ⟨sub,by omega,?_⟩
  constructor
  · intro eq; rw [eq,ct] at size; omega
  · intro eq
    exact (eq_of_subset_of_card_le sub (by omega)).symm

#print axioms second_neighborhood
#print axioms single_split_iff
#print axioms single_failure_iff
end Minimal180
