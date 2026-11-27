import FourWheel28

namespace Graffiti384b.Four28
open Finset SimpleGraph HighEar EarFrame33
open private CubicShore.square_frame from CubicDiamondCut33
open private Repair.triangles_le_choose from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A fixed fan disjoint from the ear triangle works for every choice of
the fourth vertex on an ear square and every eligible center in its triangle. -/
theorem ear_fan (n : Fintype.card V=28) (pos : ∀ v,0<trianglesAt G v)
    (fi : Function.Injective (trianglesAt G)) (free : G.CliqueFree 5) (half : 14≤gamma G)
    {e a b : V} (ab : a≠b) (se : trianglesAt G e=1) (en : G.neighborFinset e={a,b}) :
    ∃ T Y,Fan G T Y ∧ Disjoint (T∪Y) {e,a,b} ∧
      (∃ v∈T,v∈remote G {a,b} 9) ∧
      ∀ s∈additional G e a b,∀ z∈T,z≠s →
        ∃ u,u∉({e,a,b}:Finset V) ∧ u≠s ∧ u∉T∪Y ∧ G.degree u=3 ∧ G.Adj u z ∧
          ∃ t∈T,¬G.Adj u t := by
  classical
  let P : Finset V := {a,b}
  have pc : P.card=2 := card_pair ab
  have pN : P=G.neighborFinset e := en.symm
  have sees : 2≤nbr G e P := by
    change 2≤(P.filter (G.Adj e)).card
    rw [filter_true_of_mem (fun u um => (G.mem_neighborFinset ..).mp (pN ▸ um)),pc]
  obtain ⟨v,vm,T,Y,fan,vt,near,dis⟩ := forced_fan G n pos fi free half P (by rw [pc]; decide) (fun _ => ⟨e,se,sees⟩)
  obtain ⟨vp,nn,_,_⟩ := (mem_filter.mp vm).2
  have ve : v≠e := by intro eq; rw [eq] at nn; omega
  have ev : ¬G.Adj e v := fun ed => vp (pN ▸ (G.mem_neighborFinset ..).mpr ed)
  have em : e∉T∪Y := by
    intro m
    rcases mem_insert.mp (near m) with eq|ed
    · exact ve eq.symm
    · exact ev ((G.mem_neighborFinset ..).mp ed).symm
  have apart : Disjoint (T∪Y) {e,a,b} := disjoint_left.mpr (by
    intro x xm xe
    rcases mem_insert.mp xe with rfl|p
    · exact em xm
    · exact disjoint_left.mp dis xm p)
  refine ⟨T,Y,fan,apart,⟨v,vt,vm⟩,?_⟩
  intro s sm z zt zs
  obtain ⟨sn,as',bs⟩ := (additional_mem G).mp sm
  have ea : G.Adj e a := (G.mem_neighborFinset ..).mp (en ▸ mem_insert_self ..)
  have eb : G.Adj e b := (G.mem_neighborFinset ..).mp (en ▸ mem_insert_of_mem (mem_singleton_self _))
  let A : Finset V := {e,s}
  let B : Finset V := {a,b}
  have fr : Frame G A B := CubicShore.square_frame G ea eb as' bs sn.symm ab
  have cover : A∪B⊆insert s ({e,a,b}:Finset V) := by
    intro x xm; simpa [A,B,or_assoc,or_comm,or_left_comm] using xm
  have over : ((A∪B)∩(T∪Y)).card≤1 := (card_le_card (show (A∪B)∩(T∪Y)⊆{s} from by
    intro x xm
    rcases mem_insert.mp (cover (mem_inter.mp xm).1) with eq|ext
    · exact mem_singleton.mpr eq
    · exact (disjoint_left.mp apart (mem_inter.mp xm).2 ext).elim)).trans_eq (card_singleton _)
  have off : z∉A∪B := by
    intro zm
    exact (mem_insert.mp (cover zm)).elim zs (disjoint_left.mp apart (mem_union_left _ zt))
  have low (w : V) (wf : w∉A∪B) : 3≤G.degree w := by
    by_contra! smal
    have le := (Repair.triangles_le_choose G w).trans (Nat.choose_le_choose 2 (by omega : G.degree w≤2))
    rw [Nat.choose_self] at le
    have eq : w=e := fi (by have := pos w; omega)
    exact wf (eq ▸ mem_union_left B (mem_insert_self e _))
  obtain ⟨u,uf,uo,du,uz,miss⟩ := wheel_blocker G fr fan low (by omega) over zt off
  have uorig : u∉({e,a,b}:Finset V) := by
    intro mem; rcases mem_insert.mp mem with rfl|p
    · exact uf (mem_union_left _ (mem_insert_self ..))
    · exact uf (mem_union_right _ p)
  exact ⟨u,uorig,fun eq => uf (eq ▸ mem_union_left B (mem_insert_of_mem (mem_singleton_self _))),uo,du,uz,miss⟩

/-- If the ear has two distinct choices of fourth vertex, the fan's central
triangle requires both cubic scores outside the fan and the entire ear triangle. -/
theorem two_blockers (n : Fintype.card V=28) (pos : ∀ v,0<trianglesAt G v)
    (fi : Function.Injective (trianglesAt G)) (free : G.CliqueFree 5) (half : 14≤gamma G)
    {e a b : V} (ab : a≠b) (se : trianglesAt G e=1) (en : G.neighborFinset e={a,b})
    (many : 2≤(additional G e a b).card) :
    ∃ T Y,Fan G T Y ∧ Disjoint (T∪Y) {e,a,b} ∧
      ∃ u v,u∉T∪Y∪{e,a,b} ∧ v∉T∪Y∪{e,a,b} ∧ G.degree u=3 ∧ G.degree v=3 ∧
        trianglesAt G u=2 ∧ trianglesAt G v=3 := by
  classical
  obtain ⟨T,Y,fan,dis,⟨z,zt,_⟩,ob⟩ := ear_fan G n pos fi free half ab se en
  have hit (w : V) (wt : w∈T) : ∃ u,u∉({e,a,b}:Finset V) ∧ u∉T∪Y ∧ G.degree u=3 ∧ G.Adj u w ∧ ∃ t∈T,¬G.Adj u t := by
    obtain ⟨s,sm,sw⟩ := exists_ne_of_one_lt_card many w
    obtain ⟨u,ue,_,uo,du,uw,extra⟩ := ob s sm w wt sw.symm
    exact ⟨u,ue,uo,du,uw,extra⟩
  obtain ⟨u,ue,uo,du,_,t,tt,miss⟩ := hit z zt
  obtain ⟨v,ve,vo,dv,vt,_⟩ := hit t tt
  have uv : u≠v := fun eq => miss (eq ▸ vt)
  have unequal : trianglesAt G u≠trianglesAt G v := fun eq => uv (fi eq)
  have de : G.degree e=2 := by rw [←card_neighborFinset_eq_degree,en,card_pair ab]
  have uu : u∉T∪Y∪{e,a,b} := fun h => (mem_union.mp h).elim uo ue
  have vv : v∉T∪Y∪{e,a,b} := fun h => (mem_union.mp h).elim vo ve
  refine ⟨T,Y,fan,dis,?_⟩
  rcases cubic_scores G de du pos fi with su|su <;> rcases cubic_scores G de dv pos fi with sv|sv
  · exact (unequal (su.trans sv.symm)).elim
  · exact ⟨u,v,uu,vv,du,dv,su,sv⟩
  · exact ⟨v,u,vv,uu,dv,du,sv,su⟩
  · exact (unequal (su.trans sv.symm)).elim

end Graffiti384b.Four28
#print axioms Graffiti384b.Four28.ear_fan
#print axioms Graffiti384b.Four28.two_blockers
