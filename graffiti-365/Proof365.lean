/-
Graffiti.pc #365, Written on the Wall II, 18 February 2009.
Official statement: https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json

For every tree of order greater than two, the total domination number is
at least the number of isolates in the subgraph induced by support vertices,
plus one third of the number of edges whose endpoints both have degree two.
A support vertex is a neighbor of a leaf.

The proof assigns each degree-two edge to a vertex of a total dominating set.
Isolated support vertices are forced into the set. The assignments that land on
them are redirected to a selected neighbor. At most three assignments reach
any remaining selected vertex, giving the desired bound.

The public AI Village report on #378 records only earlier finite testing of
#365: https://grok-ai-village-news-496089.gitlab.io/articles/opus5-wow2-conj378-false-one-hundred-sixty-four
No priority claim is made.

Replay with Lean 4.19.0 and Mathlib v4.19.0. Exact theorem: Graffiti365.conjecture365.
-/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
open Finset SimpleGraph
set_option linter.unusedSectionVars false
set_option warningAsError true

namespace Graffiti365
section Root
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
omit [Fintype V] in
private theorem one_step_toward (hc : G.Connected) (r v : V) (h : v ≠ r) :
    ∃ z, G.Adj v z ∧ G.dist r z + 1 = G.dist r v := by
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist v r
  have hpos : 0 < p.length := by rw [hp]; exact hc.pos_dist_of_ne h
  have hn : ¬ p.Nil := SimpleGraph.Walk.not_nil_iff_lt_length.mpr hpos
  have h1 : G.Adj v (p.getVert 1) := by simpa using p.adj_getVert_succ (i := 0) hpos
  have h2 := SimpleGraph.dist_le p.tail
  rw [SimpleGraph.dist_comm] at h2
  change G.dist r (p.getVert 1) ≤ p.tail.length at h2
  have h3 := p.length_tail_add_one hn
  rw [hp, SimpleGraph.dist_comm] at h3
  have h4 : G.dist r v ≤ G.dist r (p.getVert 1) + 1 := by
    simpa only [dist_eq_one_iff_adj.mpr h1.symm] using
      (hc.dist_triangle (u := r) (v := p.getVert 1) (w := v))
  exact ⟨_, h1, by omega⟩

/-- Rooted shortest-path parent relation, producing an actual spanning tree. -/
private theorem exists_bfs_tree (hc : G.Connected) (r : V) :
    ∃ (par : V → V) (T : SimpleGraph V),
      T ≤ G ∧ T.IsTree ∧
      (∀ v, v ≠ r → G.dist r (par v) + 1 = G.dist r v) ∧
      (∀ u v, T.Adj u v ↔ (u ≠ r ∧ par u = v) ∨ (v ≠ r ∧ par v = u)) := by
  classical
  let par (v : V) : V :=
    if h : v = r then r else (one_step_toward G hc r v h).choose
  have props (v : V) (h : v ≠ r) :
      G.Adj v (par v) ∧ G.dist r (par v) + 1 = G.dist r v := by
    simpa [par, h] using (one_step_toward G hc r v h).choose_spec
  let T : SimpleGraph V :=
    { Adj := fun u v => (u ≠ r ∧ par u = v) ∨ (v ≠ r ∧ par v = u)
      symm := fun _ _ => Or.symm
      loopless := by
        intro v h
        have h := h.elim id id
        have e := (props v h.1).2
        rw [h.2] at e
        omega }
  have hsub : T ≤ G := by
    intro u v h
    change (u ≠ r ∧ par u = v) ∨ (v ≠ r ∧ par v = u) at h
    rcases h with ⟨h,e⟩ | ⟨h,e⟩
    · rw [← e]
      exact (props u h).1
    · rw [← e]
      exact (props v h).1.symm
  have treeReach : ∀ v, T.Reachable v r := by
    intro v
    generalize h : G.dist r v = d
    induction d using Nat.strong_induction_on generalizing v with
    | h d ih =>
      by_cases he : v = r
      · rw [he]
      · have hlt : G.dist r (par v) < d := by
          have hp := (props v he).2
          omega
        have had : T.Adj v (par v) := Or.inl ⟨he,rfl⟩
        exact had.reachable.trans (ih _ hlt _ rfl)
  have hconn : T.Connected := (connected_iff_exists_forall_reachable _).mpr
      ⟨r,fun v => (treeReach v).symm⟩
  have edgeImage : T.edgeFinset =
      ((Finset.univ : Finset V).erase r).image (fun v => s(v,par v)) := by
    ext e
    refine Sym2.inductionOn e (fun u v => ?_)
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    change ((u ≠ r ∧ par u = v) ∨ (v ≠ r ∧ par v = u)) ↔ _
    constructor
    · rintro (⟨hu,e⟩ | ⟨hv,e⟩)
      · exact Finset.mem_image.mpr ⟨u, by simp [hu], by rw [e]⟩
      · exact Finset.mem_image.mpr ⟨v, by simp [hv], by rw [e,Sym2.eq_swap]⟩
    · intro h
      obtain ⟨w, hw, he⟩ := Finset.mem_image.mp h
      have hne := (Finset.mem_erase.mp hw).1
      rcases Sym2.eq_iff.mp he with ⟨hu,hparEq⟩ | ⟨hv,hparEq⟩
      · exact Or.inl ⟨by simpa [hu] using hne, by simpa [hu] using hparEq⟩
      · exact Or.inr ⟨by simpa [hv] using hne, by simpa [hv] using hparEq⟩
  have edgeInj : Set.InjOn (fun v => s(v,par v)) (↑((Finset.univ : Finset V).erase r) : Set V) := by
    intro u hu v hv e
    have hu' := (Finset.mem_erase.mp hu).1
    have hv' := (Finset.mem_erase.mp hv).1
    rcases Sym2.eq_iff.mp e with ⟨h,_⟩ | ⟨h,j⟩
    · exact h
    · have p := (props u hu').2
      have q := (props v hv').2
      rw [← h] at q
      rw [j] at p
      omega
  have htree : T.IsTree := by
    apply isTree_iff_connected_and_card.mpr
    refine ⟨hconn, ?_⟩
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card,
      edgeImage, Finset.card_image_of_injOn edgeInj]
    have he := Finset.card_erase_add_one (Finset.mem_univ r)
    simpa using he
  exact ⟨par,T,hsub,htree,fun v h => (props v h).2,fun _ _ => Iff.rfl⟩
end Root

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
def Support (x : V) := ∃ w, G.Adj x w ∧ G.degree w = 1
def IsolSupport (x : V) := Support G x ∧ ∀ y, G.Adj x y → ¬ Support G y
def TD (D : Finset V) := ∀ v, ∃ x ∈ D, G.Adj v x
noncomputable def iso : Finset V := by classical exact univ.filter (IsolSupport G)
noncomputable def twos : Finset (Sym2 V) := by
  classical exact G.edgeFinset.filter (fun e => ∀ v ∈ e, G.degree v = 2)

private lemma nb {x y : V} : y ∈ G.neighborFinset x ↔ G.Adj x y :=
  G.mem_neighborFinset x y

private lemma leafUnique {u v w} (h : G.degree u = 1) (ev : G.Adj u v)
    (ew : G.Adj u w) : v = w := by
  have hc : (G.neighborFinset u).card ≤ 1 := by rw [G.card_neighborFinset_eq_degree,h]
  exact Finset.card_le_one.mp hc _ ((nb G).mpr ev) _ ((nb G).mpr ew)

private lemma degTwo {u v w x} (h : G.degree u = 2) (hv : G.Adj u v)
    (hw : G.Adj u w) (hvw : v ≠ w) (hx : G.Adj u x) : x = v ∨ x = w := by
  have he : ({v,w} : Finset V) = G.neighborFinset u := by
    apply eq_of_subset_of_card_le
    · intro a ha
      rcases mem_insert.mp ha with rfl | ha
      · exact (nb G).mpr hv
      · obtain rfl := mem_singleton.mp ha
        exact (nb G).mpr hw
    · rw [G.card_neighborFinset_eq_degree,h,card_insert_of_not_mem]
      · simp
      · simpa using hvw
  have hh := (nb G).mpr hx
  rw [← he] at hh
  simpa using hh


lemma bound365 (ht : G.IsTree) (D : Finset V) (hD : TD G D) :
    3 * (iso G).card + (twos G).card ≤ 3 * D.card := by
  classical
  have isoSub : iso G ⊆ D := by
    intro s hs
    have h : IsolSupport G s := (mem_filter.mp hs).2
    obtain ⟨l, el, dl⟩ := h.1
    obtain ⟨d, hd, ed⟩ := hD l
    exact (leafUnique G dl ed el.symm) ▸ hd
  have hcount := card_le_card isoSub
  by_cases hempty : twos G = ∅
  · simp [hempty]
    omega
  have memtw (u v : V) : s(u,v) ∈ twos G ↔
      G.Adj u v ∧ G.degree u = 2 ∧ G.degree v = 2 := by
    simp [twos, Sym2.mem_iff, and_assoc]
  obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  obtain ⟨u,v,rfl⟩ := (show ∃ a b, e = s(a,b) from Sym2.inductionOn e (fun a b => ⟨a,b,rfl⟩))
  obtain ⟨euv,du,dv⟩ := (memtw u v).mp he
  have ri : ∃ r, G.degree r = 2 ∧ r ∉ iso G := by
    by_cases hu : u ∈ iso G
    · refine ⟨v,dv,fun hv => ?_⟩
      exact (mem_filter.mp hu).2.2 v euv (mem_filter.mp hv).2.1
    · exact ⟨u,du,hu⟩
  obtain ⟨r,hr,hriso⟩ := ri
  obtain ⟨p,T,TG,htT,hstep,hpar⟩ := exists_bfs_tree G ht.isConnected r
  have eqGT : G = T := by
    apply le_antisymm _ TG
    by_contra h
    have hproper : T < G := lt_of_le_of_ne TG (fun hEq => h (hEq ▸ le_rfl))
    have hh := SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hproper
    have hh' := card_lt_card hh
    have h1 := ht.card_edgeFinset
    have h2 := htT.card_edgeFinset
    omega
  have orient {x y} (e : G.Adj x y) : (x ≠ r ∧ p x = y) ∨ (y ≠ r ∧ p y = x) :=
    (hpar x y).mp (eqGT ▸ e)
  have pe {x} (hx : x ≠ r) : G.Adj x (p x) :=
    TG ((hpar x (p x)).mpr (Or.inl ⟨hx,rfl⟩))
  have back {x y} (hx : x ≠ r) (hy : y ≠ r) (px : p x = y) : p y ≠ x := by
    intro py
    have h1 := hstep x hx
    have h2 := hstep y hy
    rw [px] at h1
    rw [py] at h2
    omega
  let X := univ.filter (fun x => x ≠ r ∧ G.degree x = 2 ∧ G.degree (p x) = 2)
  have xm {x} (hx : x ∈ X) := (mem_filter.mp hx).2
  have edgeCard : (twos G).card = X.card := by
    symm
    apply card_bij (fun x _ => s(x,p x))
    · intro x hx
      exact (memtw x (p x)).mpr ⟨pe (xm hx).1,(xm hx).2⟩
    · intro x hx y hy e
      rcases Sym2.eq_iff.mp e with ⟨ee,_⟩ | ⟨ee,ee'⟩
      · exact ee
      · exact False.elim (back (xm hx).1 (xm hy).1 ee' ee.symm)
    · intro e he'
      obtain ⟨x,y,rfl⟩ := (show ∃ a b, e = s(a,b) from Sym2.inductionOn e (fun a b => ⟨a,b,rfl⟩))
      obtain ⟨ex,dx,dy⟩ := (memtw x y).mp he'
      rcases orient ex with ⟨hx,hp⟩ | ⟨hy,hp⟩
      · exact ⟨x,mem_filter.mpr ⟨mem_univ _,hx,dx,hp ▸ dy⟩,by rw [hp]⟩
      · exact ⟨y,mem_filter.mpr ⟨mem_univ _,hy,dy,hp ▸ dx⟩,by rw [hp,Sym2.eq_swap]⟩
  let f (x : V) := Classical.choose (hD x)
  have fd (x : V) : f x ∈ D := (Classical.choose_spec (hD x)).1
  have fe (x : V) : G.Adj x (f x) := (Classical.choose_spec (hD x)).2
  have noIsoPar {x} (hx : x ∈ X) : p x ∉ iso G := by
    intro hi
    let d := p x
    have dx := (xm hx).2.1
    have dd := (xm hx).2.2
    have edge : G.Adj d x := (pe (xm hx).1).symm
    have dn : d ≠ r := fun h => hriso (h ▸ hi)
    have pdd : p d ≠ x := back (xm hx).1 dn rfl
    obtain ⟨l, el, dl⟩ := (mem_filter.mp hi).2.1
    rcases degTwo G dd edge (pe dn) pdd.symm el with h | h
    · rw [h,dx] at dl
      omega
    · have hdpr : p d ≠ r := fun eq => by rw [h,eq,hr] at dl; omega
      have ed' : G.Adj (p d) (p (p d)) := pe hdpr
      have equal : d = p (p d) := leafUnique G (h ▸ dl) (pe dn).symm ed'
      exact back dn hdpr rfl equal.symm
  have fcase {x} (hx : x ∈ X) :
      f x = p x ∨ (f x ≠ r ∧ p (f x) = x) := by
    rcases orient (fe x) with ⟨_,h⟩ | h
    · exact Or.inl h.symm
    · exact Or.inr h
  have si {x} (hx : x ∈ X) (hf : f x ∈ iso G) :
      f x ≠ r ∧ p (f x) = x := (fcase hx).resolve_left
      (fun h => noIsoPar hx (h ▸ hf))
  let dest (x : V) := if f x ∈ iso G then f (f x) else f x
  have ds {x} (hx : x ∈ X) : dest x ∈ D \ iso G := by
    by_cases hi : f x ∈ iso G
    · rw [show dest x = f (f x) by simp [dest,hi]]
      refine mem_sdiff.mpr ⟨fd _,fun h => ?_⟩
      exact (mem_filter.mp hi).2.2 _ (fe _) (mem_filter.mp h).2.1
    · simpa [dest,hi] using (mem_sdiff.mpr ⟨fd x,hi⟩ : f x ∈ D \ iso G)
  have hasTwo {x : V} (h : G.degree x = 2) :
      ∃ a b, a ≠ b ∧ G.Adj x a ∧ G.Adj x b := by
    have hh : 1 < (G.neighborFinset x).card := by rw [G.card_neighborFinset_eq_degree,h]; decide
    obtain ⟨a,ha,b,hb,he⟩ := Finset.one_lt_card.mp hh
    exact ⟨a,b,he,(nb G).mp ha,(nb G).mp hb⟩
  obtain ⟨q,q',hqq,eq,eq'⟩ := hasTwo hr
  have childUnique {d x y} (dh : G.degree d = 2) (dn : d ≠ r) (hx : x ≠ r)
      (hy : y ≠ r) (xp : p x = d) (yp : p y = d) : x = y := by
    have ex : G.Adj d x := xp ▸ (pe hx).symm
    have ey : G.Adj d y := yp ▸ (pe hy).symm
    exact (degTwo G dh ex (pe dn) (back hx dn xp).symm ey).resolve_right
      (back hy dn yp).symm |>.symm
  have shiftCross {x y} (hx : x ∈ X) (hy : y ∈ X) (hi : f y ∈ iso G)
      (px : p x = f y) : False := by
    obtain ⟨fyn,fyp⟩ := si hy hi
    have dfy : G.degree (f y) = 2 := px ▸ (xm hx).2.2
    have ey : G.Adj (f y) y := by simpa only [fyp] using pe fyn
    have ex : G.Adj (f y) x := px ▸ (pe (xm hx).1).symm
    have ne : x ≠ y := fun h => back (xm hx).1 fyn px (fyp.trans h.symm)
    obtain ⟨l,el,dl⟩ := (mem_filter.mp hi).2.1
    rcases degTwo G dfy ex ey ne el with h | h
    · rw [h,(xm hx).2.1] at dl
      omega
    · rw [h,(xm hy).2.1] at dl
      omega
  have shiftedInj {x y} (hx : x ∈ X) (hy : y ∈ X)
      (hi : f x ∈ iso G) (hj : f y ∈ iso G)
      (ee : f (f x) = f (f y)) : x = y := by
    obtain ⟨_,fxp⟩ := si hx hi
    obtain ⟨_,fyp⟩ := si hy hj
    rcases orient (fe (f x)) with ⟨_,px⟩ | ⟨_,px⟩ <;>
      rcases orient (fe (f y)) with ⟨_,py⟩ | ⟨_,py⟩
    · exact fxp.symm.trans (px.trans (ee.trans (py.symm.trans fyp)))
    · have xeq : x = f (f y) := fxp.symm.trans (px.trans ee)
      exact (shiftCross hx hy hj (xeq.symm ▸ py)).elim
    · have yeq : y = f (f x) := fyp.symm.trans (py.trans ee.symm)
      exact (shiftCross hy hx hi (yeq.symm ▸ px)).elim
    · have hxy : f x = f y := by rw [← ee] at py; exact px.symm.trans py
      exact fxp.symm.trans ((congrArg p hxy).trans fyp)
  let kind (x : V) : Fin 3 :=
    if f x ∈ iso G then 2
    else if f x = p x then
      if p x = r ∧ x ≠ q then 1 else 0
    else 1
  have hv : X.card ≤ ((D \ iso G) ×ˢ (univ : Finset (Fin 3))).card := by
    apply Finset.card_le_card_of_injOn (fun x => (dest x,kind x))
    · intro x hx
      exact mem_product.mpr ⟨ds hx, mem_univ _⟩
    · intro x hx y hy hp
      have hx : x ∈ X := hx
      have hy : y ∈ X := hy
      have ed := congrArg Prod.fst hp
      have ek := congrArg Prod.snd hp
      change dest x = dest y at ed
      change kind x = kind y at ek
      by_cases hi : f x ∈ iso G
      · by_cases hj : f y ∈ iso G
        · exact shiftedInj hx hy hi hj (by simpa [dest,hi,hj] using ed)
        · simp [kind,hi,hj] at ek
          split at ek
          · split at ek <;> contradiction
          · contradiction
      · by_cases hj : f y ∈ iso G
        · simp [kind,hi,hj] at ek
          split at ek
          · split at ek <;> contradiction
          · contradiction
        have eF : f x = f y := by simpa [dest,hi,hj] using ed
        have parCase (a b : V) (ha : a ∈ X) (hb : b ∈ X)
            (pa : f a = p a) (pb : f b = p b) (eqf : f a = f b)
            (eqk : kind a = kind b) (ia : f a ∉ iso G) (ib : f b ∉ iso G) : a = b := by
          have abp : p a = p b := pa.symm.trans (eqf.trans pb)
          by_cases ar : p a = r
          · have br : p b = r := abp.symm.trans ar
            have ea : G.Adj r a := ar ▸ (pe (xm ha).1).symm
            have eb : G.Adj r b := br ▸ (pe (xm hb).1).symm
            rcases degTwo G hr eq eq' hqq ea with h | h <;>
              rcases degTwo G hr eq eq' hqq eb with j | j
            · exact h.trans j.symm
            · have k : b ≠ q := j ▸ hqq.symm
              have ka : ¬ (p a = r ∧ a ≠ q) := fun hx => hx.2 h
              have kb : p b = r ∧ b ≠ q := ⟨br,k⟩
              simp only [kind,if_neg ia,if_neg ib,if_pos pa,if_pos pb,if_neg ka,if_pos kb] at eqk
              exact False.elim (by exact (show (0 : Fin 3) ≠ 1 by decide) eqk)
            · have k : a ≠ q := h ▸ hqq.symm
              have ka : p a = r ∧ a ≠ q := ⟨ar,k⟩
              have kb : ¬ (p b = r ∧ b ≠ q) := fun hx => hx.2 j
              simp only [kind,if_neg ia,if_neg ib,if_pos pa,if_pos pb,if_pos ka,if_neg kb] at eqk
              exact False.elim (by exact (show (1 : Fin 3) ≠ 0 by decide) eqk)
            · exact h.trans j.symm
          · exact childUnique (xm ha).2.2 ar (xm ha).1 (xm hb).1 rfl abp.symm
        have crossKind (a b : V) (ha : a ∈ X) (hb : b ∈ X)
            (pa : f a = p a) (pb : f b ≠ p b) (eqf : f a = f b)
            (eqk : kind a = kind b) (ia : f a ∉ iso G) (ib : f b ∉ iso G) : False := by
          have nr := ((fcase hb).resolve_left pb).1
          have ar : p a ≠ r := fun hr' => nr (eqf.symm.trans (pa.trans hr'))
          simp only [kind,if_neg ia,if_neg ib,if_pos pa,if_neg pb,ar,false_and,if_false] at eqk
          exact (show (0 : Fin 3) ≠ 1 by decide) eqk
        by_cases px : f x = p x <;> by_cases py : f y = p y
        · exact parCase x y hx hy px py eF ek hi hj
        · exact (crossKind x y hx hy px py eF ek hi hj).elim
        · exact (crossKind y x hy hx py px eF.symm ek.symm hj hi).elim
        · have ex := ((fcase hx).resolve_left px).2
          have ey := ((fcase hy).resolve_left py).2
          exact ex.symm.trans ((congrArg p eF).trans ey)
  rw [card_product,card_univ,Fintype.card_fin,card_sdiff isoSub] at hv
  omega

noncomputable def totalDomination : Nat :=
  sInf {k | ∃ D, TD G D ∧ D.card = k}

/-- Graffiti.pc #365, with the denominator 3 cleared. -/
theorem conjecture365 (hT : G.IsTree) (hn : 2 < Fintype.card V) :
    3 * (iso G).card + (twos G).card ≤ 3 * totalDomination G := by
  classical
  have hd : TD G Finset.univ := by
    intro v
    obtain ⟨w,hne⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card V) v
    obtain ⟨p⟩ := hT.isConnected v w
    cases p with
    | nil => exact False.elim (hne rfl)
    | @cons _ u _ he _ => exact ⟨u,Finset.mem_univ _,he⟩
  have ha : ({k : Nat | ∃ D : Finset V, TD G D ∧ D.card = k}).Nonempty :=
    ⟨_,_,hd,rfl⟩
  obtain ⟨D,hD,he⟩ := Nat.sInf_mem ha
  rw [show totalDomination G = D.card from he.symm]
  exact bound365 G hT D hD

#print axioms conjecture365
end Graffiti365
