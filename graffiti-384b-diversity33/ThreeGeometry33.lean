import ThreeFibers33

namespace Graffiti384b.ThreeChoice
open Finset SimpleGraph HighEar
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

private theorem pair_turan (X : Finset V) {r : ℕ} (rp : 0<r)
    (free : ∀ Q⊆X,¬H.IsNClique (r+1) Q) :
    (pairs H X).card≤(turanGraph X.card r).edgeFinset.card := by
  classical
  let J := H.induce (X:Set V)
  let emb : X ↪ V := Function.Embedding.subtype _
  have cf : J.CliqueFree (r+1) := by
    intro Q cl
    exact free (Q.map emb) (by intro x xm; obtain ⟨w,_,rfl⟩ := mem_map.mp xm; exact w.property)
      (cl.map.mono (H.spanningCoe_induce_le (s:=(X:Set V))))
  let f : Sym2 X → Finset V := Sym2.lift ⟨fun a b => {a.val,b.val},fun a b => pair_comm _ _⟩
  have inc : pairs H X⊆J.edgeFinset.image f := by
    intro E em
    obtain ⟨p,pm,q,qm,pq,rfl⟩ := (pair_mem H).mp em
    let a : X := ⟨p,pm⟩
    let b : X := ⟨q,qm⟩
    exact mem_image.mpr ⟨s(a,b),mem_edgeFinset.mpr (show J.Adj a b from pq),rfl⟩
  obtain ⟨M,dM,maximal⟩ := exists_isTuranMaximal (V:=X) rp
  letI := dM
  obtain ⟨iso⟩ := maximal.nonempty_iso_turanGraph
  have bound : (pairs H X).card≤M.edgeFinset.card := (card_le_card inc).trans (card_image_le.trans (maximal.2 J cf))
  rwa [iso.card_edgeFinset_eq,Fintype.card_coe] at bound

/-- Three-way partition into the simplicial cubic, its three neighbors,
and their exterior. -/
def pool (s : V) := (insert s (H.neighborFinset s))ᶜ

theorem pool_mem {s w : V} : w∈pool H s ↔ w≠s ∧ ¬H.Adj s w := by simp [pool,not_or]

private theorem pairs_add {X Y : Finset V} (dis : Disjoint X Y) :
    (pairs H (X∪Y)).card≤(pairs H X).card+X.card*Y.card+Y.card.choose 2 := by
  classical
  induction Y using Finset.induction_on with
  | empty => simp
  | @insert y Y hy ih =>
    have off : y∉X := fun xm => disjoint_left.mp dis xm (mem_insert_self ..)
    have less := ih (disjoint_left.mpr (fun x xm ym => disjoint_left.mp dis xm (mem_insert_of_mem ym)))
    have eq : X∪insert y Y=insert y (X∪Y) := by ext; simp [or_left_comm]
    have d : nbr H y (X∪Y)≤X.card+Y.card := (card_filter_le ..).trans (card_union_le ..)
    have ch : (Y.card+1).choose 2=Y.card+Y.card.choose 2 := by
      simpa only [Nat.choose_one_right] using Nat.choose_succ_succ' Y.card 1
    rw [eq,pairs_insert H (by simp [off,hy]),card_insert_of_not_mem hy,Nat.mul_add,Nat.mul_one,ch]
    omega

private theorem as_cap (b r : ℕ) (bsmall : b≤10) (rpos : 0<r) (rsmall : r<10) :
    (turanGraph b r).edgeFinset.card=RankTable.cap b r :=
  RankTable.cap_table ⟨b,by omega⟩ ⟨r,rsmall⟩ rpos

theorem scores {s : V} (ds : H.degree s=3) (ss : trianglesAt H s=3)
    (meet : ∀ C,H.IsNClique 5 C → ∃ x∈C,H.Adj s x) :
    let A := H.neighborFinset s
    let W := pool H s
    (∀ w∈W,trianglesAt H w≤(nbr H w W+nbr H w A).choose 2) ∧
    (∀ w∈W,nbr H w A≤1 → nbr H w W≤10 →
      trianglesAt H w≤RankTable.cap (nbr H w W) 3+nbr H w W*nbr H w A) ∧
    (∀ a∈A,nbr H a W≤10 → trianglesAt H a≤3+2*nbr H a W+RankTable.cap (nbr H a W) 4) := by
  classical
  let A := H.neighborFinset s
  let W := pool H s
  change (∀ w∈W,_) ∧ (∀ w∈W,_) ∧ (∀ a∈A,_)
  have sz : A.card=3 := (card_neighborFinset_eq_degree ..).trans ds
  have dis : Disjoint W A := disjoint_left.mpr (fun w wm am => ((pool_mem H).mp wm).2 ((H.mem_neighborFinset ..).mp am))
  have free (Q : Finset V) (qw : Q⊆W) : ¬H.IsNClique 5 Q := by
    intro cl; obtain ⟨x,xm,sx⟩ := meet Q cl; exact ((pool_mem H).mp (qw xm)).2 sx
  have cut (w : V) (wm : w∈W) :
      H.neighborFinset w=W.filter (H.Adj w)∪A.filter (H.Adj w) := by
    ext y; simp only [H.mem_neighborFinset,mem_union,mem_filter]
    constructor
    · intro wy
      by_cases am : y∈A
      · exact Or.inr ⟨am,wy⟩
      · have ys : y≠s := fun eq => ((pool_mem H).mp wm).2 (eq ▸ wy.symm)
        exact Or.inl ⟨(pool_mem H).mpr ⟨ys,fun sy => am ((H.mem_neighborFinset ..).mpr sy)⟩,wy⟩
    · exact fun h => h.elim And.right And.right
  constructor
  · intro w wm
    have sub : pairs H (H.neighborFinset w)⊆(H.neighborFinset w).powersetCard 2 := filter_subset ..
    have h := card_le_card sub
    rw [card_powersetCard,cut w wm,card_union_of_disjoint (dis.mono (filter_subset ..) (filter_subset ..))] at h
    change (pairs H (H.neighborFinset w)).card≤_
    rw [cut w wm]; exact h
  constructor
  · intro w wm small bsmall
    let X := W.filter (H.Adj w)
    let Y := A.filter (H.Adj w)
    have freeX (Q : Finset V) (qx : Q⊆X) : ¬H.IsNClique (3+1) Q := by
      intro cl
      exact free (insert w Q) (insert_subset wm (qx.trans (filter_subset ..))) (cl.insert (fun y ym => (mem_filter.mp (qx ym)).2))
    have cap := pair_turan H X (by decide : 0<3) freeX
    rw [as_cap X.card 3 bsmall (by decide) (by decide)] at cap
    have un := pairs_add H (X:=X) (Y:=Y) (dis.mono (filter_subset ..) (filter_subset ..))
    have smallY : Y.card≤1 := small
    have zero : Y.card.choose 2=0 := Nat.choose_eq_zero_of_lt (by omega)
    change (pairs H (H.neighborFinset w)).card≤_
    rw [cut w wm]
    change (pairs H (X∪Y)).card≤RankTable.cap X.card 3+X.card*Y.card
    omega
  · intro a am bsmall
    let X := W.filter (H.Adj a)
    let Y := A.erase a
    have aS : H.Adj s a := (H.mem_neighborFinset ..).mp am
    have eq : H.neighborFinset a=insert s (X∪Y) := by
      ext y; simp only [H.mem_neighborFinset,mem_insert,mem_union,mem_filter,mem_erase,X,Y]
      constructor
      · intro ay
        by_cases ys : y=s
        · exact Or.inl ys
        by_cases ya : y∈A
        · exact Or.inr (Or.inr ⟨ay.ne.symm,ya⟩)
        · exact Or.inr (Or.inl ⟨(pool_mem H).mpr ⟨ys,fun sy => ya ((H.mem_neighborFinset ..).mpr sy)⟩,ay⟩)
      · rintro (rfl|⟨_,ay⟩|⟨ya,ym⟩)
        · exact aS.symm
        · exact ay
        · exact EarAnchor.full_neighbors H ds ss aS ((H.mem_neighborFinset ..).mp ym) ya.symm
    have sy : Y.card=2 := by dsimp [Y]; rw [card_erase_of_mem am,sz]
    have ni : s∉X∪Y := by
      intro m
      rcases mem_union.mp m with x|y
      · exact ((pool_mem H).mp (mem_filter.mp x).1).1 rfl
      · exact H.not_mem_neighborFinset_self _ (mem_erase.mp y).2
    have sub : (X∪Y).filter (H.Adj s)⊆Y := by
      intro w wm
      obtain ⟨m,edge⟩ := mem_filter.mp wm
      exact (mem_union.mp m).resolve_left (fun x => ((pool_mem H).mp (mem_filter.mp x).1).2 edge)
    have cost : nbr H s (X∪Y)≤2 := (card_le_card sub).trans sy.le
    have fs (Q : Finset V) (q : Q⊆X) := free Q (q.trans (filter_subset ..))
    have cap := pair_turan H X (by decide : 0<4) fs
    rw [as_cap X.card 4 bsmall (by decide) (by decide)] at cap
    have un := pairs_add H (X:=X) (Y:=Y) (dis.mono (filter_subset ..) (erase_subset ..))
    rw [sy,Nat.choose_self] at un
    change (pairs H (H.neighborFinset a)).card≤_
    rw [eq,pairs_insert H ni]
    change _≤3+2*X.card+RankTable.cap X.card 4
    omega

end Graffiti384b.ThreeChoice
#print axioms Graffiti384b.ThreeChoice.scores
