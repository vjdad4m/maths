import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega

/-! Graffiti.pc 177. A star is grown while recording mutually nonadjacent
witnesses for the connectors it uses. All graph invariants are finite extrema. -/
set_option warningAsError true
namespace Short177
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

def Indep (X : Finset V) := ∀ u ∈ X, ∀ v ∈ X, u ≠ v → ¬G.Adj u v
def TwoColor (W : Finset V) :=
  ∃ X Y : Finset V, Disjoint X Y ∧ X ∪ Y = W ∧ Indep G X ∧ Indep G Y
noncomputable def independence := by
  classical exact (univ.filter (Indep G)).sup Finset.card
noncomputable def bipartiteNum := by
  classical exact (univ.filter (TwoColor G)).sup Finset.card
noncomputable def leaves (T : SimpleGraph V) : Finset V := by
  classical exact univ.filter (fun v => T.degree v = 1)
noncomputable def maxLeaves := by
  classical
  exact (univ.filter (fun T : SimpleGraph V => T ≤ G ∧ T.IsTree)).sup
    (fun T => (leaves T).card)
noncomputable def secondDegree [DecidableRel G.Adj] :=
  sInf {k | ∃ u v : V, u ≠ v ∧ max (G.degree u) (G.degree v) = k}

private theorem colors {A X : Finset V} (i : Indep G A) (j : Indep G X)
    (d : Disjoint A X) : A.card + X.card ≤ bipartiteNum G := by
  classical
  rw [← card_union_of_disjoint d]
  exact le_sup (f := Finset.card) (mem_filter.mpr ⟨mem_univ _, A, X, d, rfl, i, j⟩)

private def Touch (D : Finset V) (x : V) := ∃ p ∈ D, G.Adj x p

/-- A certificate that a nonempty vertex set can be grown along edges. -/
private inductive Core : Finset V → Prop
  | one (x : V) : Core {x}
  | add {D x} : Core D → Touch G D x → Core (insert x D)

omit [Fintype V] in
private theorem Core.nonempty {D} (h : Core G D) : D.Nonempty := by
  induction h with
  | one => exact singleton_nonempty _
  | add => exact insert_nonempty _ _

omit [Fintype V] in
private theorem Core.cover {D E} (h : Core G D) (sub : D ⊆ E)
    (dom : ∀ x ∈ E, x ∉ D → Touch G D x) : Core G E := by
  classical
  have aux (F : Finset V) (hf : F ⊆ E) : Core G (F ∪ D) := by
    induction F using Finset.induction_on with
    | empty => simpa using h
    | @insert x F hx ih =>
      have old := ih ((subset_insert x F).trans hf)
      rw [insert_union]
      by_cases hd : x ∈ D
      · simpa [insert_eq_of_mem (mem_union_right F hd)] using old
      · obtain ⟨p,hp,e⟩ := dom x (hf (mem_insert_self _ _)) hd
        exact old.add ⟨p,mem_union_right F hp,e⟩
  simpa [union_eq_left.mpr sub] using aux E Subset.rfl

/-- Every vertex outside a connected dominating core can be a leaf at once. -/
private theorem leafBound {D} (h : Core G D) (dom : ∀ x ∉ D, Touch G D x) :
    (univ \ D).card ≤ maxLeaves G := by
  classical
  let f (x : V) := if hx : x ∉ D then (dom x hx).choose else x
  have par {x} (hx : x ∉ D) : f x ∈ D ∧ G.Adj x (f x) := by
    simpa [f,hx] using (dom x hx).choose_spec
  let H : SimpleGraph V :=
    { Adj := fun x y => G.Adj x y ∧ (x ∉ D → f x = y) ∧ (y ∉ D → f y = x)
      symm := fun _ _ e => ⟨e.1.symm,e.2.2,e.2.1⟩
      loopless := fun x e => G.loopless x e.1 }
  have inside (E : Finset V) (he : Core G E) (sub : E ⊆ D) :
      ∃ r ∈ E, ∀ y ∈ E, H.Reachable r y := by
    induction he with
    | one x => exact ⟨x,by simp,fun y hy => by rw [mem_singleton.mp hy]⟩
    | @add S x _ adj ih =>
      obtain ⟨r,hr,reach⟩ := ih ((subset_insert _ _).trans sub)
      obtain ⟨p,hp,e⟩ := adj
      have hp' := sub (mem_insert_of_mem hp)
      have hx' := sub (mem_insert_self _ _)
      refine ⟨r,mem_insert_of_mem hr,fun y hy => ?_⟩
      rcases mem_insert.mp hy with rfl | hy
      · exact (reach p hp).trans (show H.Adj p y from ⟨e.symm,fun n => (n hp').elim,fun n => (n hx').elim⟩).reachable
      · exact reach y hy
  obtain ⟨r,_,hr⟩ := inside D h Subset.rfl
  have hH : H.Connected := by
    apply (connected_iff_exists_forall_reachable _).mpr
    refine ⟨r,fun x => ?_⟩
    by_cases hx : x ∈ D
    · exact hr x hx
    · obtain ⟨hf,e⟩ := par hx
      exact (hr _ hf).trans (show H.Adj (f x) x from ⟨e.symm,by simp [hf],by simp⟩).reachable
  obtain ⟨T,ht,tree⟩ := hH.exists_isTree_le
  suffices hsub : univ \ D ⊆ leaves T from (card_le_card hsub).trans
    (le_sup (f := fun T => (leaves T).card)
      (mem_filter.mpr ⟨mem_univ _,fun _ _ e => (ht e).1,tree⟩))
  intro x hx
  have out := (mem_sdiff.mp hx).2
  have ne : x ≠ f x := fun eq => out (eq ▸ (par out).1)
  obtain ⟨w,hw⟩ := tree.isConnected.exists_walk_length_eq_dist x (f x)
  have pos : 0 < w.length := hw ▸ tree.isConnected.pos_dist_of_ne ne
  have edge : T.Adj x (w.getVert 1) := by simpa using w.adj_getVert_succ (i := 0) pos
  have unique {y} (e : T.Adj x y) : f x = y := (ht e).2.1 out
  have nb : T.neighborFinset x = {f x} := by
    ext y; simp only [mem_neighborFinset,mem_singleton]
    exact ⟨fun e => (unique e).symm,fun eq => by rwa [eq,unique edge]⟩
  exact mem_filter.mpr ⟨mem_univ _,by rw [← T.card_neighborFinset_eq_degree,nb,card_singleton]⟩

/-- The marks are removable leaves. All have a neighbor in the same core. -/
private structure Fringe (S M : Finset V) : Prop where
  sub : M ⊆ S
  core : Core G (S \ M)
  touch : ∀ x ∈ M, Touch G (S \ M) x

omit [Fintype V] in
private theorem star (a : V) (N : Finset V) (out : a ∉ N)
    (adj : ∀ x ∈ N, G.Adj x a) : Fringe G (insert a N) N := by
  have eq : insert a N \ N = {a} := by ext x; by_cases e : x = a <;> simp_all
  exact ⟨subset_insert _ _,eq ▸ Core.one _,fun x hx => ⟨a,by simp [eq],adj x hx⟩⟩

omit [Fintype V] in
/-- Attach a child and pass its parent's mark to it if there was one. -/
private theorem attach {S M} (h : Fringe G S M) {p x : V} (hp : p ∈ S)
    (hx : x ∉ S) (edge : G.Adj x p) :
    Fringe G (insert x S) (insert x (M.erase p)) := by
  have eq : insert x S \ insert x (M.erase p) = insert p (S \ M) := by
    ext v
    by_cases a : v = x <;> by_cases b : v = p <;> simp_all [mem_insert,mem_sdiff]
  have core : Core G (insert p (S \ M)) := by
    by_cases hm : p ∈ M
    · exact h.core.add (h.touch p hm)
    · simpa [insert_eq_of_mem (mem_sdiff.mpr ⟨hp,hm⟩)] using h.core
  refine ⟨insert_subset_insert _ (fun v hv => h.sub (mem_of_mem_erase hv)),eq ▸ core,?_⟩
  rw [eq]
  intro y hy
  rcases mem_insert.mp hy with rfl | hy
  · exact ⟨p,mem_insert_self _ _,edge⟩
  · obtain ⟨q,hq,e⟩ := h.touch y (mem_of_mem_erase hy)
    exact ⟨q,mem_insert_of_mem hq,e⟩

omit [Fintype V] in
private theorem mark_count {S M} (h : Fringe G S M) {x : V} (hx : x ∉ S) (p : V) :
    M.card ≤ (insert x (M.erase p)).card := by
  rw [card_insert_of_not_mem (fun he => hx (h.sub (mem_of_mem_erase he)))]
  by_cases hm : p ∈ M
  · rw [card_erase_of_mem hm]; omega
  · simp [erase_eq_of_not_mem hm]

private def SimpleAt (a : V) :=
  ∀ u v, G.Adj a u → G.Adj a v → u ≠ v → G.Adj u v

omit [Fintype V] [DecidableEq V] in
private theorem boundary (hc : G.Connected) {S : Finset V} (ne : S.Nonempty)
    {t : V} (out : t ∉ S) : ∃ p ∈ S, ∃ x ∉ S, G.Adj p x := by
  by_contra! h
  obtain ⟨p,hp⟩ := ne
  obtain ⟨w⟩ := hc p t
  have closed {u v} (walk : G.Walk u v) : u ∈ S → v ∈ S := by
    induction walk with
    | nil => exact id
    | cons e _ ih => exact fun hu => ih (by by_contra hv; exact h _ hu _ hv e)
  exact out (closed w hp)

/-- Grow until all vertices outside A have been reached. A paid connector
supplies a new independent witness and has two nonadjacent neighbors. -/
private theorem grow (hc : G.Connected) {A : Finset V} (ind : Indep G A)
    (S M X : Finset V) (fr : Fringe G S M) (mx : Disjoint M A)
    (xs : X ⊆ S) (ix : Indep G X) (dx : Disjoint X A) :
    ∃ E N Y : Finset V, (∀ x ∉ A, x ∈ E) ∧ Fringe G E N ∧ Disjoint N A ∧
      M.card ≤ N.card ∧ Indep G Y ∧ Disjoint Y A ∧
      (E ∩ A).card + X.card ≤ (S ∩ A).card + Y.card ∧
      ∀ v ∈ E, v ∈ A → v ∈ S ∨ ¬SimpleAt G v := by
  classical
  by_cases done : ∀ x ∉ A, x ∈ S
  · exact ⟨S,M,X,done,fr,mx,le_rfl,ix,dx,le_rfl,fun _ h _ => Or.inl h⟩
  push_neg at done
  obtain ⟨t,htA,ht⟩ := done
  by_cases direct : ∃ x ∉ A, x ∉ S ∧ ∃ p ∈ S, G.Adj x p
  · obtain ⟨x,hxA,hx,p,hp,e⟩ := direct
    have fr' := attach G fr hp hx e
    have mx' : Disjoint (insert x (M.erase p)) A := by
      rw [disjoint_insert_left]; exact ⟨hxA,mx.mono_left (erase_subset _ _)⟩
    obtain ⟨E,N,Y,allB,f,d,card,i,j,budget,old⟩ :=
      grow hc ind (insert x S) _ X fr' mx' (xs.trans (subset_insert _ _)) ix dx
    refine ⟨E,N,Y,allB,f,d,(mark_count G fr hx p).trans card,i,j,?_,?_⟩
    · simpa [insert_inter_of_not_mem,hxA] using budget
    · intro v hv ha
      simpa [mem_insert,show v ≠ x from fun h => hxA (h ▸ ha)] using old v hv ha
  · -- The first edge leaving F must run from a fresh connector to a fresh child.
    let F := S ∪ (A.filter (Touch G S))
    have out : t ∉ F := by simp [F,ht,htA]
    have ne := (fr.core.nonempty G).mono ((show S \ M ⊆ F from sdiff_subset.trans (subset_union_left)))
    obtain ⟨c,hcF,x,hxF,edge⟩ := boundary G hc ne out
    have hx : x ∉ S := fun h => hxF (mem_union_left _ h)
    have cOut : c ∉ S := by
      intro h
      by_cases ha : x ∈ A
      · exact hxF (mem_union_right _ (mem_filter.mpr ⟨ha,c,h,edge.symm⟩))
      · exact direct ⟨x,ha,hx,c,h,edge.symm⟩
    obtain ⟨ca,p,hp,cp⟩ := mem_filter.mp ((mem_union.mp hcF).resolve_left cOut)
    have xa : x ∉ A := fun h => ind c ca x h edge.ne edge
    have noEdge (v : V) (hv : v ∈ S) : ¬G.Adj x v :=
      fun e => direct ⟨x,xa,hx,v,hv,e⟩
    have bad : ¬SimpleAt G c := fun h => noEdge p hp
      (h x p edge cp (fun eq => hx (eq ▸ hp)))
    have fr1 := attach G fr hp cOut cp
    have nx : x ∉ insert c S := by simp [mem_insert,edge.ne.symm,hx]
    have fr2 := attach G fr1 (mem_insert_self _ _) nx edge.symm
    have mx2 : Disjoint (insert x ((insert c (M.erase p)).erase c)) A := by
      simp [disjoint_insert_left,xa,erase_insert,erase_eq_of_not_mem
        (show c ∉ M.erase p from fun h => cOut (fr.sub (mem_of_mem_erase h))),
        mx.mono_left (erase_subset p M)]
    have ix' : Indep G (insert x X) := by
      intro u hu v hv ne e
      rcases mem_insert.mp hu with hu | hu
      · subst u
        exact noEdge v (xs ((mem_insert.mp hv).resolve_left ne.symm)) e
      · rcases mem_insert.mp hv with hv | hv
        · subst v; exact noEdge u (xs hu) e.symm
        · exact ix _ hu _ hv ne e
    have dx' : Disjoint (insert x X) A := disjoint_insert_left.mpr ⟨xa,dx⟩
    have sub : insert x X ⊆ insert x (insert c S) :=
      insert_subset_insert _ (xs.trans (subset_insert _ _))
    obtain ⟨E,N,Y,allB,f,d,card,i,j,budget,old⟩ :=
      grow hc ind _ _ _ fr2 mx2 sub ix' dx'
    refine ⟨E,N,Y,allB,f,d,((mark_count G fr cOut p).trans
      (mark_count G fr1 nx c)).trans card,i,j,?_,?_⟩
    · have xn : x ∉ X := fun h => hx (xs h)
      simp [insert_inter_of_not_mem,xa,insert_inter_of_mem,ca,card_insert_of_not_mem,
        xn,cOut] at budget
      omega
    · intro v hv ha
      rcases old v hv ha with h | h
      · rcases mem_insert.mp h with rfl | h
        · exact (xa ha).elim
        rcases mem_insert.mp h with rfl | h
        · exact Or.inr bad
        · exact Or.inl h
      · exact Or.inr h
termination_by Fintype.card V - S.card
decreasing_by
  · have bound := card_le_univ (insert x S)
    rw [card_insert_of_not_mem hx] at bound ⊢
    omega
  · have bound := card_le_univ (insert x (insert c S))
    rw [card_insert_of_not_mem nx,card_insert_of_not_mem cOut] at bound ⊢
    omega

omit [Fintype V] [DecidableEq V] in
private theorem nbr {A : Finset V} (i : Indep G A)
    {a x : V} (ha : a ∈ A) (e : G.Adj a x) : x ∉ A := fun hx => i _ ha _ hx e.ne e

/-- Keep exactly R of the marks as leaves. Other unused independent vertices
also become leaves if they retain a neighbor. -/
private theorem harvest [DecidableRel G.Adj] {A E M R : Finset V}
    (ind : Indep G A) (cover : ∀ x ∉ A, x ∈ E) (fr : Fringe G E M)
    (sub : R ⊆ M) (dx : Disjoint M A) (s : ℕ) (small : R.card < s)
    (safe : ∀ x ∈ A, x ∉ E → s ≤ G.degree x ∨ ∃ y ∉ R, G.Adj x y) :
    A.card + R.card ≤ maxLeaves G + (E ∩ A).card := by
  classical
  let D := E \ R
  have incl : E \ M ⊆ D := sdiff_subset_sdiff Subset.rfl sub
  have old {x} (hx : x ∈ M) : Touch G D x := by
    obtain ⟨p,hp,e⟩ := fr.touch x hx
    exact ⟨p,incl hp,e⟩
  have core := fr.core.cover G incl (fun x hx miss => fr.touch x
    (Classical.byContradiction (fun hm => miss (mem_sdiff.mpr ⟨(mem_sdiff.mp hx).1,hm⟩))))
  have dom (x : V) (hx : x ∉ D) : Touch G D x := by
    by_cases he : x ∈ E
    · exact old (sub (Classical.byContradiction (fun hr => hx (mem_sdiff.mpr ⟨he,hr⟩))))
    have ha : x ∈ A := Classical.byContradiction (fun h => he (cover x h))
    have witness : ∃ y ∉ R, G.Adj x y := by
      rcases safe x ha he with high | ok
      · apply Classical.byContradiction
        intro no
        have nsub : G.neighborFinset x ⊆ R := by
          intro y hy
          exact Classical.byContradiction (fun out => no ⟨y,out,(G.mem_neighborFinset x y).mp hy⟩)
        have := card_le_card nsub
        rw [G.card_neighborFinset_eq_degree] at this
        omega
      · exact ok
    obtain ⟨y,hy,e⟩ := witness
    exact ⟨y,mem_sdiff.mpr ⟨cover _ (nbr G ind ha e),hy⟩,e⟩
  have bound := leafBound G core dom
  have sub' : (A \ E) ∪ R ⊆ univ \ D := by
    intro v hv
    refine mem_sdiff.mpr ⟨mem_univ _,fun hd => ?_⟩
    rcases mem_union.mp hv with hv | hv
    · exact (mem_sdiff.mp hv).2 (mem_sdiff.mp hd).1
    · exact (mem_sdiff.mp hd).2 hv
  have dis : Disjoint (A \ E) R := dx.symm.mono sdiff_subset sub
  have h := (card_le_card sub').trans bound
  rw [card_union_of_disjoint dis] at h
  have ar := card_sdiff_add_card_inter A E
  rw [inter_comm A E] at ar
  omega

omit [Fintype V] in
private theorem pairIndep {u v : V} (e : ¬G.Adj u v) : Indep G {u,v} := by
  intro x hx y hy ne edge
  simp only [mem_insert,mem_singleton] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact ne rfl
  · exact e edge
  · exact e edge.symm
  · exact ne rfl

private theorem anchored {z w : V} (nw : w ≠ z) :
    ∃ A : Finset V, Indep G A ∧ A.card = independence G ∧ ∃ a ∈ A, a ≠ z := by
  classical
  have one (x : V) : Indep G {x} := by simp [Indep]
  obtain ⟨A,member,maximal⟩ := exists_mem_eq_sup
    (s := univ.filter (Indep G)) (f := Finset.card)
    ⟨{w},mem_filter.mpr ⟨mem_univ _,one w⟩⟩
  have eq : A.card = independence G := maximal.symm
  by_cases anchor : ∃ a ∈ A, a ≠ z
  · exact ⟨A,(mem_filter.mp member).2,eq,anchor⟩
  push_neg at anchor
  have sub : A ⊆ {z} := fun x hx => mem_singleton.mpr (anchor x hx)
  have le := card_le_card sub
  have ge := le_sup (s := univ.filter (Indep G)) (f := Finset.card)
    (mem_filter.mpr ⟨mem_univ {w},one w⟩)
  change ({w} : Finset V).card ≤ independence G at ge
  simp only [card_singleton] at le ge
  exact ⟨{w},one _,by simp only [card_singleton]; omega,w,by simp,nw⟩

variable [DecidableRel G.Adj]

private theorem degreeBound (hc : G.Connected) {z : V} {s : ℕ}
    (pos : 0 < s) (high : ∀ x ≠ z, s ≤ G.degree x)
    (other : ∃ w, w ≠ z) (neighbor : ∃ q, G.Adj z q) :
    2 * independence G + s ≤ maxLeaves G + bipartiteNum G := by
  classical
  obtain ⟨w,hw⟩ := other
  obtain ⟨A,ind,size,a,ha,az⟩ := anchored G hw
  obtain ⟨q,eq⟩ := neighbor
  let B := univ \ A
  have memB {v : V} : v ∈ B ↔ v ∉ A := by simp [B]
  have dBA : Disjoint B A := disjoint_left.mpr (fun _ h => memB.mp h)
  have sing (v : V) : Indep G {v} := by simp [Indep]
  have na (v : V) (hv : v ∈ A) : G.neighborFinset v ⊆ B :=
    fun x hx => memB.mpr (nbr G ind hv ((G.mem_neighborFinset v x).mp hx))
  -- Every neighbor of an independent vertex is in its complement.
  have base : s ≤ (G.neighborFinset a).card := by
    rw [G.card_neighborFinset_eq_degree]; exact high a az
  have big : s ≤ B.card := base.trans (card_le_card (na a ha))
  by_cases clique : ∀ u ∈ B, ∀ v ∈ B, u ≠ v → G.Adj u v
  · -- Keep a clique center adjacent to the exceptional vertex if necessary.
    have center : ∃ p ∈ B, z ∈ A → G.Adj z p := by
      by_cases hz : z ∈ A
      · exact ⟨q,memB.mpr (nbr G ind hz eq),fun _ => eq⟩
      · obtain ⟨p,hp⟩ := card_pos.mp (pos.trans_le big)
        exact ⟨p,hp,fun h => (hz h).elim⟩
    obtain ⟨p,hp,ep⟩ := center
    have init := star G p (B.erase p) (not_mem_erase _ _)
      (fun x hx => clique _ (mem_of_mem_erase hx) _ hp (ne_of_mem_erase hx))
    rw [insert_erase hp] at init
    have count : s - 1 ≤ (B.erase p).card := by rw [card_erase_of_mem hp]; omega
    obtain ⟨R,sub,rc⟩ := exists_subset_card_eq count
    have keep : p ∉ R := fun h => (not_mem_erase _ _) (sub h)
    have bound := harvest G ind (fun _ hv => memB.mpr hv) init sub
      (dBA.mono_left (erase_subset _ _)) s (by omega) (fun x hx _ => by
        by_cases h : x = z
        · subst x; exact Or.inr ⟨p,keep,ep hx⟩
        · exact Or.inl (high x h))
    have col := colors G ind (sing p) (disjoint_singleton_right.mpr (memB.mp hp))
    rw [disjoint_iff_inter_eq_empty.mp dBA,card_empty,add_zero] at bound
    simp only [card_singleton] at col
    omega
  push_neg at clique
  obtain ⟨u,hu,v,hv,uv,nonedge⟩ := clique
  have pair {u v : V} (nu : u ∈ B) (nv : v ∈ B) : Disjoint ({u,v} : Finset V) A := by
    simp [disjoint_insert_left,memB.mp nu,memB.mp nv]
  have extra := colors G ind (pairIndep G nonedge) (pair hu hv).symm
  simp [uv] at extra
  -- Two nonadjacent neighbors pay for the initial center and the reserved mark.
  by_cases rough : ∃ c ∈ A, c ≠ z ∧ ¬SimpleAt G c
  · obtain ⟨c,hcA,cz,rough⟩ := rough
    unfold SimpleAt at rough
    push_neg at rough
    obtain ⟨i,j,ei,ej,ij,no⟩ := rough
    let N := G.neighborFinset c
    have ni : i ∈ N := (G.mem_neighborFinset c i).mpr ei
    have nj : j ∈ N := (G.mem_neighborFinset c j).mpr ej
    have outside := na c hcA
    have start := star G c N (by simp [N]) (fun x hx => ((G.mem_neighborFinset c x).mp hx).symm)
    have inside : {i,j} ⊆ insert c N := by simp [insert_subset_iff,ni,nj]
    obtain ⟨E,M,Y,cover,fr,d,marks,iy,dy,budget,_⟩ :=
      grow G hc ind _ _ _ start (dBA.mono_left outside) inside
        (pairIndep G no) (pair (outside ni) (outside nj))
    have initial : N ∩ A = ∅ := disjoint_iff_inter_eq_empty.mp (dBA.mono_left outside)
    simp [insert_inter_of_mem hcA,initial,ij] at budget
    have nh : s ≤ N.card := by simpa [N] using high c cz
    have keep : s - 1 ≤ (M.erase q).card := by
      by_cases hq : q ∈ M
      · rw [card_erase_of_mem hq]; omega
      · rw [erase_eq_of_not_mem hq]; omega
    obtain ⟨R,sub,rc⟩ := exists_subset_card_eq keep
    have bound := harvest G ind cover fr (sub.trans (erase_subset _ _)) d s (by omega)
      (fun x _ _ => by
        by_cases h : x = z
        · subst x; exact Or.inr ⟨q,fun h => (not_mem_erase _ _) (sub h),eq⟩
        · exact Or.inl (high x h))
    have col := colors G ind iy dy.symm
    omega
  · -- Every vertex of A other than z is simplicial and may be left unused.
    push_neg at rough
    let P := A.erase z
    have ps : P ⊆ A := erase_subset _ _
    have pi : Indep G P := fun x hx y hy => ind x (ps hx) y (ps hy)
    have ad : SimpleAt G a := rough a ha az
    let N := G.neighborFinset a
    obtain ⟨p,hp⟩ := card_pos.mp (pos.trans_le base)
    have init := star G p (N.erase p) (not_mem_erase _ _) (fun x hx =>
      ad x p ((G.mem_neighborFinset a x).mp (mem_of_mem_erase hx))
        ((G.mem_neighborFinset a p).mp hp) (ne_of_mem_erase hx))
    rw [insert_erase hp] at init
    have dis : Disjoint N P := dBA.mono (na a ha) ps
    obtain ⟨E,M,Y,cover,fr,d,marks,_,_,_,old⟩ :=
      grow G hc pi _ _ ∅ init (dis.mono_left (erase_subset _ _))
        (empty_subset _) (by simp [Indep]) (by simp)
    have noP : E ∩ P = ∅ := disjoint_iff_inter_eq_empty.mp
      (disjoint_left.mpr (fun x he hx => (old x he hx).elim
        (fun h => disjoint_left.mp dis h hx)
        (fun h => h (rough x (ps hx) (ne_of_mem_erase hx)))))
    have rc0 : s - 1 ≤ M.card := by
      rw [card_erase_of_mem hp] at marks
      change N.card - 1 ≤ M.card at marks
      change s ≤ N.card at base
      omega
    obtain ⟨R,sub,rc⟩ := exists_subset_card_eq rc0
    have bound := harvest G pi cover fr sub d s (by omega)
      (fun x hx _ => Or.inl (high x (ne_of_mem_erase hx)))
    rw [noP,card_empty,add_zero] at bound
    have loss : A.card ≤ P.card + 1 := by
      by_cases hz : z ∈ A
      · rw [show P = A.erase z from rfl,card_erase_of_mem hz]; omega
      · simp [P,erase_eq_of_not_mem hz]
    omega

/-- Written on the Wall II, Conjecture 177. Degrees are counted with multiplicity. -/
theorem conjecture177 (hc : G.Connected) (hn : 1 < Fintype.card V) :
    2 * independence G + secondDegree G ≤ maxLeaves G + bipartiteNum G := by
  classical
  obtain ⟨u,v,uv⟩ := Fintype.one_lt_card_iff.mp hn
  have different (x : V) : ∃ w, w ≠ x := by
    by_cases e : x = u
    · exact ⟨v,e ▸ uv.symm⟩
    · exact ⟨u,Ne.symm e⟩
  have adj (x : V) : ∃ y, G.Adj x y := by
    obtain ⟨w,hw⟩ := different x
    obtain ⟨p,hp,y,_,e⟩ := boundary G hc (singleton_nonempty x)
      (show w ∉ ({x} : Finset V) by simpa using hw)
    exact ⟨y,mem_singleton.mp hp ▸ e⟩
  obtain ⟨z,_,minD⟩ := exists_min_image (univ : Finset V) (fun x => G.degree x) ⟨u,mem_univ _⟩
  apply degreeBound G hc (z := z) _ _ (different z) (adj z)
  · obtain ⟨i,j,_,h⟩ := Nat.sInf_mem
      (show {k | ∃ i j : V, i ≠ j ∧ max (G.degree i) (G.degree j) = k}.Nonempty from
        ⟨_,u,v,uv,rfl⟩)
    unfold secondDegree; rw [← h]
    exact ((G.degree_pos_iff_exists_adj i).mpr (adj i)).trans_le (le_max_left _ _)
  · intro x hx
    exact Nat.sInf_le ⟨z,x,hx.symm,max_eq_right (minD x (mem_univ _))⟩

#print axioms conjecture177
end Short177

