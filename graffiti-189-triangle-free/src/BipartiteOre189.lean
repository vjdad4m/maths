import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Chain
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Combinatorics.SimpleGraph.Path
import GraphPathLift

/- The list-cycle reversal scaffold is adapted from TraceClosure208.lean. -/
namespace Graffiti189TriangleFree
open SimpleGraph

def Cyclic {α : Type*} (R : α → α → Prop) (l : List α) : Prop :=
  l.Chain' R ∧ ∀ x ∈ l.getLast?, ∀ y ∈ l.head?, R x y

def CycleList {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ l : List V, l.Nodup ∧ (∀ v, v ∈ l) ∧ Cyclic G.Adj l

private theorem chain_reverse {α : Type*} {R : α → α → Prop}
    (hs : ∀ x y, R x y → R y x) {l : List α} (h : l.Chain' R) :
    l.reverse.Chain' R :=
  List.chain'_reverse.mpr (h.imp hs)

private theorem cycled {α : Type*} {R : α → α → Prop}
    (hs : ∀ x y, R x y → R y x)
    {l : List α} {x y : α}
    (hx : l.head? = some x) (hy : l.getLast? = some y)
    (hc : l.Chain' R)
    {L : List α} {v w : α} {M : List α} (he : l = L ++ v :: w :: M)
    (hyv : R y v) (hxw : R x w) :
    ∃ c : List α, Cyclic R c ∧ c.Perm l := by
  let A := L ++ [v]
  let B := w :: M
  have he' : l = A ++ B := by simp [A,B,he]
  have hA : A ≠ [] := by simp [A]
  have hB : B ≠ [] := by simp [B]
  rw [he'] at hc
  have hAh : A.head? = some x := by
    rw [he', List.head?_append_of_ne_nil A hA] at hx
    exact hx
  have hBt : B.getLast? = some y := by
    rw [he', List.getLast?_append_of_ne_nil A hB] at hy
    exact hy
  have hAt : A.getLast? = some v := by simp [A,List.getLast?_append_cons]
  have hBh : B.head? = some w := rfl
  refine ⟨A ++ B.reverse, ⟨?_,?_⟩,?_⟩
  · apply hc.left_of_append.append (chain_reverse hs hc.right_of_append)
    simp [hAt,List.head?_reverse,hBt,hs y v hyv]
  · have hrev : B.reverse ≠ [] := by simp [hB]
    rw [List.getLast?_append_of_ne_nil A hrev, List.getLast?_reverse, hBh,
        List.head?_append_of_ne_nil A hA, hAh]
    simpa using hs x w hxw
  · rw [he']
    exact (List.reverse_perm B).append_left A

private theorem rotate_cycle {α : Type*} {R : α → α → Prop} {A B : List α}
    (h : Cyclic R (A ++ B)) : Cyclic R (B ++ A) := by
  by_cases hA : A = []
  · simpa [hA] using h
  by_cases hB : B = []
  · simpa [hB] using h
  obtain ⟨h1, h2⟩ := h
  have h3 := (List.chain'_append.mp h1).2.2
  rw [List.getLast?_append_of_ne_nil A hB, List.head?_append_of_ne_nil A hA] at h2
  refine ⟨h1.right_of_append.append h1.left_of_append h2,?_⟩
  rwa [List.getLast?_append_of_ne_nil B hA, List.head?_append_of_ne_nil B hB]

private theorem split_at_mem {α : Type*} (x : α) (l : List α) (h : x ∈ l) :
    ∃ A B : List α, l = A ++ x :: B := by
  induction l with
  | nil => simp at h
  | cons a t ih =>
    rcases List.mem_cons.mp h with e | e
    · exact ⟨[],t,by simp [e]⟩
    · obtain ⟨A,B,he⟩ := ih e
      exact ⟨a :: A,B,by simp [he]⟩

private theorem option_map_some {α : Type*} (l : List (Option α)) (h : none ∉ l) :
    ∃ p : List α, p.map some = l := by
  induction l with
  | nil => exact ⟨[],rfl⟩
  | cons a t ih =>
    rcases a with _ | v
    · exact (h (by simp)).elim
    · obtain ⟨p,hp⟩ := ih (fun hh => h (List.mem_cons_of_mem _ hh))
      exact ⟨v :: p,by simp [hp]⟩


private def univRel {V : Type*} (G : SimpleGraph V) : Option V → Option V → Prop
  | some x, some y => G.Adj x y
  | none, none => False
  | _, _ => True

private noncomputable def mark {α : Type*} (R : α → α → Prop) (x : α) (v : α) : Bool :=
  @decide (R x v) (Classical.propDecidable _)

@[simp] private theorem mark_true {α : Type*} {R : α → α → Prop} {x y : α} :
    mark R x y = true ↔ R x y := by
  classical
  exact Iff.of_eq (@decide_eq_true_eq (R x y) (Classical.propDecidable _))

private theorem mark_false {α : Type*} {R : α → α → Prop} {x y : α} (h : ¬R x y) :
    mark R x y = false := by
  cases he : mark R x y
  · rfl
  · exact (h (mark_true.mp he)).elim

private theorem full_toFinset {V : Type*} [Fintype V] [DecidableEq V]
    {p : List V} (hn : p.Nodup) (hl : p.length = Fintype.card V) :
    p.toFinset = Finset.univ := by
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  rw [Finset.card_univ, List.toFinset_card_of_nodup hn, hl]

private theorem split_left {V : Type*} (G : SimpleGraph V) {x y : V} {L M : List V}
    (hn : (L ++ x :: y :: M).Nodup)
    (hc : (L ++ x :: y :: M).Chain' (G ⊔ SimpleGraph.edge x y).Adj) :
    (L ++ [x]).Chain' G.Adj := by
  have hn' : ((L ++ [x]) ++ y :: M).Nodup := by simpa using hn
  have hd := (List.nodup_append.mp hn').2.2
  have hy : y ∉ L ++ [x] := fun hy => hd hy (by simp)
  have head := (List.chain'_append_cons_cons.mp hc).1
  apply (List.Chain'.iff_mem.mp head).imp
  intro a b ⟨ha,hb,hab⟩
  rcases (SimpleGraph.sup_adj _ _ _ _).mp hab with hag | hae
  · exact hag
  · rcases ((SimpleGraph.edge_adj _ _ _ _).mp hae).1 with ⟨_,rfl⟩ | ⟨rfl,_⟩
    · exact (hy hb).elim
    · exact (hy ha).elim

private theorem split_right {V : Type*} (G : SimpleGraph V) {x y : V} {L M : List V}
    (hn : (L ++ x :: y :: M).Nodup)
    (hc : (L ++ x :: y :: M).Chain' (G ⊔ SimpleGraph.edge x y).Adj) :
    (y :: M).Chain' G.Adj := by
  have hn' : ((L ++ [x]) ++ y :: M).Nodup := by simpa using hn
  have hd := (List.nodup_append.mp hn').2.2
  have hx : x ∉ y :: M := fun hx => hd (by simp) hx
  have tail := (List.chain'_append_cons_cons.mp hc).2.2
  apply (List.Chain'.iff_mem.mp tail).imp
  intro a b ⟨ha,hb,hab⟩
  rcases (SimpleGraph.sup_adj _ _ _ _).mp hab with hag | hae
  · exact hag
  · rcases ((SimpleGraph.edge_adj _ _ _ _).mp hae).1 with ⟨rfl,_⟩ | ⟨_,rfl⟩
    · exact (hx ha).elim
    · exact (hx hb).elim

private theorem edge_comm {V : Type*} (x y : V) :
    SimpleGraph.edge x y = SimpleGraph.edge y x := by
  ext a b
  simp only [SimpleGraph.edge_adj]
  tauto

private lemma no_pair_count_cross {α : Type*} (color a b : α → Bool)
    (ha : ∀ u, a u = true → color u = true)
    (hb : ∀ v, b v = true → color v = false) (l : List α)
    (h : l.Chain' fun u v => color u ≠ color v ∧ ¬ (a u = true ∧ b v = true)) :
    l.dropLast.countP a + l.tail.countP b ≤ l.countP color := by
  induction l with
  | nil => simp
  | cons u t ih =>
    cases t with
    | nil => simp
    | cons v r =>
      have ht := ih h.tail
      have hrel := h.rel_head
      rw [List.dropLast_cons₂]
      simp only [List.countP_cons (a := u), List.tail_cons] at *
      rw [List.countP_cons (a := v) (p:=b)]
      cases hau : a u <;> cases hbv : b v
      · simp [hau,hbv] at *; split <;> omega
      · have hcu : color u = true := by
          have hcv := hb v hbv
          cases hu : color u
          · exact (hrel.1 (hu.trans hcv.symm)).elim
          · rfl
        simp [hau,hbv,hcu] at *
        omega
      · have hcu := ha u hau
        simp [hau,hbv,hcu] at *
        omega
      · exact (hrel.2 ⟨hau,hbv⟩).elim

private lemma find_cross_pair {α : Type*} {color a b : α → Bool} {l : List α} {x y : α}
    (hx : l.head? = some x) (hy : l.getLast? = some y)
    (hax : a y = false) (hby : b x = false)
    (ha : ∀ u, a u = true → color u = true)
    (hb : ∀ v, b v = true → color v = false)
    (hcol : l.Chain' (fun u v => color u ≠ color v))
    (ht : l.countP color < l.countP a + l.countP b) :
    ∃ (L : List α) (u v : α) (M : List α), l = L ++ u :: v :: M ∧ a u = true ∧ b v = true := by
  classical
  by_contra hn
  have hchain : l.Chain' (fun u v => color u ≠ color v ∧ ¬ (a u = true ∧ b v = true)) := by
    apply List.chain'_iff_forall_rel_of_append_cons_cons.mpr
    intro u v L M hl
    refine ⟨List.chain'_iff_forall_rel_of_append_cons_cons.mp hcol hl, ?_⟩
    intro h
    exact hn ⟨L,u,v,M,hl,h⟩
  have hc := no_pair_count_cross color a b ha hb l hchain
  have hA : l.countP a = l.dropLast.countP a := by
    have he : l.dropLast ++ [y] = l := List.dropLast_append_getLast? y (by rw [hy]; rfl)
    have hh := congrArg (List.countP a) he
    simpa [List.countP_append,hax] using hh.symm
  have hB : l.countP b = l.tail.countP b := by
    obtain ⟨t,ht⟩ := List.head?_eq_some_iff.mp hx
    rw [ht]
    simp [List.countP_cons,hby]
  omega

private theorem count_full {V : Type*} [Fintype V] {l : List V} (hn : l.Nodup)
    (hu : ∀ x, x ∈ l) (f : V → Bool) :
    l.countP f = (Finset.univ.filter fun x => f x = true).card := by
  classical
  have hU : l.toFinset = Finset.univ := by ext x; simp [hu x]
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hn.filter f)]
  simp [List.toFinset_filter,hU]

private def CutPath {V : Type*} (G : SimpleGraph V) (x y : V) : Prop :=
  ∃ l : List V, l.Nodup ∧ (∀ v, v ∈ l) ∧ l.Chain' G.Adj ∧
    l.head? = some x ∧ l.getLast? = some y

private lemma CutPath.reverse {V : Type*} {G : SimpleGraph V} {x y : V} :
    CutPath G x y → CutPath G y x := by
  rintro ⟨l,hn,hu,hc,hx,hy⟩
  exact ⟨l.reverse, List.nodup_reverse.mpr hn, fun v => List.mem_reverse.mpr (hu v),
    chain_reverse (fun _ _ e => G.symm e) hc,
    by simpa [List.head?_reverse] using hy,
    by simpa [List.getLast?_reverse] using hx⟩

private theorem cut_fake {V : Type*} [Fintype V] {G : SimpleGraph V}
    {x y : V} (hxy : ¬ G.Adj x y) (card : 3 ≤ Fintype.card V)
    {p : List V} (hn : p.Nodup) (hu : ∀ v, v ∈ p)
    (hc : Cyclic (G ⊔ SimpleGraph.edge x y).Adj p) :
    CycleList G ∨ CutPath G x y := by
  classical
  have orient {x y : V} (hnxy : ¬ G.Adj x y)
      (L M : List V) (hn : (L ++ x :: y :: M).Nodup)
      (hu : ∀ v, v ∈ L ++ x :: y :: M)
      (hc : Cyclic (G ⊔ SimpleGraph.edge x y).Adj (L ++ x :: y :: M)) :
      CutPath G y x := by
    let A := L ++ [x]
    let B := y :: M
    let t := B ++ A
    have he : L ++ x :: y :: M = A ++ B := by simp [A,B]
    have ht : t.Perm (L ++ x :: y :: M) := by
      rw [he]
      exact List.perm_append_comm
    have hnt := ht.nodup_iff.mpr hn
    have hut u := ht.mem_iff.mpr (hu u)
    have htH : t.head? = some y := rfl
    have htT : t.getLast? = some x := by simp [t,A,List.getLast?_append_cons]
    have hleft : A.Chain' G.Adj := split_left G hn hc.1
    have hright : B.Chain' G.Adj := split_right G hn hc.1
    have hjoin : ∀ u ∈ B.getLast?, ∀ v ∈ A.head?, G.Adj u v := by
      intro u um v vm
      have eqn : L ++ x :: y :: M = A ++ B := he
      have edge := hc.2
      rw [eqn,List.getLast?_append_of_ne_nil A (by simp [B]),
        List.head?_append_of_ne_nil A (by simp [A])] at edge
      rcases (SimpleGraph.sup_adj _ _ _ _).mp (edge u um v vm) with e | e
      · exact e
      · have nd := (List.nodup_append.mp (he ▸ hn)).2.2
        have hyA : y ∉ A := fun h => nd h (by simp [B])
        have hxB : x ∉ B := fun h => nd (by simp [A]) h
        rcases ((SimpleGraph.edge_adj _ _ _ _).mp e).1 with ⟨e1,e2⟩ | ⟨e1,e2⟩
        · subst u
          subst v
          exact (hxB (List.mem_of_mem_getLast? um)).elim
        · subst u
          subst v
          have hB : B = [y] := by
            cases M with
            | nil => rfl
            | cons w M =>
              have hyM : y ∈ w :: M := by
                apply List.mem_of_mem_getLast?
                simpa [B] using um
              exact ((List.nodup_cons.mp ((he ▸ hn).of_append_right : B.Nodup)).1 hyM).elim
          have hA : A = [x] := by
            cases L with
            | nil => rfl
            | cons w L =>
              have h : w = x := by simpa [A,eq_comm] using vm
              subst w
              have hnA : (x :: (L ++ [x])).Nodup := (he ▸ hn).of_append_left
              exact ((List.nodup_cons.mp hnA).1 (by simp)).elim
          have n : Fintype.card V ≤ 2 := by
            let T : Finset V := {x,y}
            have hsub : (Finset.univ : Finset V) ⊆ T := by
              intro q _
              have hh := hu q
              rw [he,hA,hB] at hh
              simpa [T] using hh
            have hh := Finset.card_le_card hsub
            rw [Finset.card_univ] at hh
            exact hh.trans ((Finset.card_insert_le x {y}).trans (by simp))
          omega
    exact ⟨t,hnt,hut,hright.append hleft hjoin,htH,htT⟩
  by_cases hp : p.Chain' G.Adj
  · by_cases hclose : ∀ x ∈ p.getLast?, ∀ y ∈ p.head?, G.Adj x y
    · exact Or.inl ⟨p,hn,hu,hp,hclose⟩
    · push_neg at hclose
      obtain ⟨a,ha,b,hb,hnab⟩ := hclose
      have he := ((SimpleGraph.sup_adj _ _ _ _).mp (hc.2 a ha b hb)).resolve_left hnab
      rcases ((SimpleGraph.edge_adj _ _ _ _).mp he).1 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact Or.inr (CutPath.reverse ⟨p,hn,hu,hp,Option.mem_def.mp hb,Option.mem_def.mp ha⟩)
      · exact Or.inr ⟨p,hn,hu,hp,Option.mem_def.mp hb,Option.mem_def.mp ha⟩
  · have hex : ∃ (a b : V) (L M : List V), p = L ++ a :: b :: M ∧ ¬ G.Adj a b := by
      apply Classical.byContradiction
      intro hh
      exact hp (List.chain'_iff_forall_rel_of_append_cons_cons.mpr (by
        intro a b L M hp'
        apply Classical.byContradiction
        intro hnab
        exact hh ⟨a,b,L,M,hp',hnab⟩))
    rcases hex with ⟨a,b,L,M,rfl,hab⟩
    have he := ((SimpleGraph.sup_adj _ _ _ _).mp (List.chain'_append_cons_cons.mp hc.1).2.1).resolve_left hab
    rcases ((SimpleGraph.edge_adj _ _ _ _).mp he).1 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact Or.inr (CutPath.reverse (orient hab L M hn hu hc))
    · rw [edge_comm] at hc
      exact Or.inr (orient hab L M hn hu hc)

def colorCount {V : Type*} [Fintype V] (color : V → Bool) (b : Bool) : ℕ :=
  (Finset.univ.filter fun v => color v = b).card

private theorem count_mark_degree {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {l : List V} (hn : l.Nodup) (hu : ∀ v, v ∈ l) (x : V) :
    l.countP (mark G.Adj x) = G.degree x := by
  classical
  rw [count_full hn hu, ← G.card_neighborFinset_eq_degree]
  congr 1
  ext u
  simp [mark_true,G.mem_neighborFinset]

private theorem close_one_cross {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (color : V → Bool)
    (cross : ∀ x y, G.Adj x y → color x ≠ color y)
    {x y : V} (cx : color x = true) (cy : color y = false)
    (hxy : ¬ G.Adj x y) (card : 3 ≤ Fintype.card V)
    (hd : colorCount color true + 1 ≤ G.degree x + G.degree y) :
    CycleList (G ⊔ SimpleGraph.edge x y) → CycleList G := by
  classical
  rintro ⟨p,hn,hu,hc⟩
  rcases cut_fake hxy card hn hu hc with h | ⟨p,hn,hu,hc,hx,hy⟩
  · exact h
  have hcnt := count_full hn hu color
  have hdx := count_mark_degree G hn hu x
  have hdy := count_mark_degree G hn hu y
  have hs : p.countP color < p.countP (mark G.Adj y) + p.countP (mark G.Adj x) := by
    change p.countP color = colorCount color true at hcnt
    omega
  have hT (u : V) (h : mark G.Adj y u = true) : color u = true := by
    have h := cross y u (mark_true.mp h)
    rw [cy] at h
    cases he : color u
    · exact (h he.symm).elim
    · rfl
  have hF (u : V) (h : mark G.Adj x u = true) : color u = false := by
    have h := cross x u (mark_true.mp h)
    rw [cx] at h
    cases he : color u
    · rfl
    · exact (h he.symm).elim
  obtain ⟨A,a,b,B,hsep,ha,hb⟩ := find_cross_pair hx hy (mark_false (G.loopless y))
    (mark_false (G.loopless x)) hT hF (hc.imp cross) hs
  obtain ⟨t,ht,hperm⟩ := cycled (fun _ _ h => G.symm h) hx hy hc hsep
    (mark_true.mp ha) (mark_true.mp hb)
  exact ⟨t,hperm.nodup_iff.mpr hn,fun v => hperm.mem_iff.mpr (hu v),ht⟩

private def weave {α : Type*} : List α → List α → List α
  | a::l, b::r => a::b::weave l r
  | _, _ => []

private lemma weave_spec {α : Type*} (color : α → Bool) (L R : List α)
    (hl : ∀ x ∈ L, color x = true) (hr : ∀ x ∈ R, color x = false)
    (hn : L.length = R.length) :
    (weave L R).Perm (L ++ R) ∧ (weave L R).Chain' (fun x y => color x ≠ color y) ∧
    (∀ x ∈ (weave L R).head?, color x = true) ∧
    (∀ x ∈ (weave L R).getLast?, color x = false) := by
  induction L generalizing R with
  | nil =>
    have : R = [] := List.length_eq_zero_iff.mp (by simpa using hn.symm)
    subst R
    simp [weave]
  | cons a l ih =>
    cases R with
    | nil => simp at hn
    | cons b r =>
      have heq : l.length = r.length := Nat.succ.inj hn
      obtain ⟨hp,hc,hh,ht⟩ := ih r
        (fun x hx => hl x (by simp [hx])) (fun x hx => hr x (by simp [hx])) heq
      have ca := hl a (by simp)
      have cb := hr b (by simp)
      have cab : color a ≠ color b := by simp [ca,cb]
      change (a::b::weave l r).Perm ((a::l) ++ b::r) ∧
        (a::b::weave l r).Chain' (fun x y => color x ≠ color y) ∧ _
      refine ⟨List.Perm.cons a ((hp.cons b).trans List.perm_middle.symm), ?_, ?_, ?_⟩
      · apply List.chain'_cons.mpr
        refine ⟨cab,?_⟩
        apply hc.cons'
        intro x hx
        simp [cb,hh x hx]
      · simp [weave,ca]
      · cases h : weave l r with
        | nil => simp [weave,h,cb]
        | cons w t => simpa [weave,h] using ht

private theorem cycle_complete_cross {V : Type*} [Fintype V] {H : SimpleGraph V}
    (color : V → Bool) (allCross : ∀ x y, color x ≠ color y → H.Adj x y)
    (balance : colorCount color true = colorCount color false) :
    CycleList H := by
  classical
  let l := List.ofFn (Fintype.equivFin V).symm
  have hl : l.Nodup := List.nodup_ofFn.mpr (Fintype.equivFin V).symm.injective
  have hu : ∀ x, x ∈ l := by
    intro x
    apply List.mem_ofFn.mpr
    exact ⟨Fintype.equivFin V x, (Fintype.equivFin V).symm_apply_apply x⟩
  let L := l.filter color
  let R := l.filter (fun x => !(color x))
  have ha (x : V) (hx : x ∈ L) := (List.mem_filter.mp hx).2
  have hb (x : V) (hx : x ∈ R) : color x = false := by
    have := (List.mem_filter.mp hx).2
    simpa using this
  have hes : L.length = R.length := by
    change (l.filter color).length = (l.filter (fun x => !color x)).length
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter,
      count_full hl hu, count_full hl hu]
    simpa [colorCount] using balance
  obtain ⟨hp,hchain,hhead,htail⟩ := weave_spec color L R ha hb hes
  have hn : (L ++ R).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hl.filter _, hl.filter _,?_⟩
    intro x hx hx'
    exact Bool.noConfusion ((ha x hx).symm.trans (hb x hx'))
  have hU : ∀ v, v ∈ L ++ R := by
    intro x
    have hh := hu x
    cases h : color x <;> simp [L,R,hh,h]
  refine ⟨weave L R,hp.nodup_iff.mpr hn,fun v => hp.mem_iff.mpr (hU v),
    hchain.imp allCross, ?_⟩
  intro x hx y hy
  apply allCross
  rw [htail x hx,hhead y hy]
  decide

/-- The balanced bipartite Ore–Moon–Moser degree-sum condition. -/
theorem bipartite_ore_cycle {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (color : V → Bool) (cross : ∀ x y, G.Adj x y → color x ≠ color y)
    (balance : colorCount color true = colorCount color false)
    (pos : 2 ≤ colorCount color true)
    (deg : ∀ x y, color x ≠ color y → ¬ G.Adj x y →
      colorCount color true + 1 ≤ G.degree x + G.degree y) :
    CycleList G := by
  classical
  apply Classical.byContradiction
  intro bad
  let S : Set (SimpleGraph V) := {H | G ≤ H ∧
    (∀ x y, H.Adj x y → color x ≠ color y) ∧ ¬ CycleList H}
  obtain ⟨H,hH,hm⟩ := (Set.toFinite S).exists_maximal_wrt id S ⟨G,le_rfl,cross,bad⟩
  have hgh : G ≤ H := hH.1
  have hcross : ∀ x y, H.Adj x y → color x ≠ color y := hH.2.1
  letI : DecidableRel H.Adj := Classical.decRel _
  have missing : ∃ x y, color x = true ∧ color y = false ∧ ¬H.Adj x y := by
    apply Classical.byContradiction
    intro hi
    apply hH.2.2
    apply cycle_complete_cross color _ balance
    intro x y hc
    apply Classical.byContradiction
    intro hab
    cases ex : color x <;> cases ey : color y
    · exact hc (ex.trans ey.symm)
    · exact hi ⟨y,x,ey,ex,fun e => hab e.symm⟩
    · exact hi ⟨x,y,ex,ey,hab⟩
    · exact hc (ex.trans ey.symm)
  obtain ⟨x,y,cx,cy,no⟩ := missing
  have hcol : color x ≠ color y := by simp [cx,cy]
  have hne : x ≠ y := fun e => hcol (congrArg color e)
  let J := H ⊔ SimpleGraph.edge x y
  have hsub : H ≤ J := le_sup_left
  have hxy : J.Adj x y := (SimpleGraph.sup_adj _ _ _ _).mpr
    (Or.inr ((SimpleGraph.edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl,rfl⟩,hne⟩))
  have hJ : CycleList J := by
    apply Classical.byContradiction
    intro hb
    have hjCross (u v : V) (he : J.Adj u v) : color u ≠ color v := by
      rcases (SimpleGraph.sup_adj _ _ _ _).mp he with e | e
      · exact hcross u v e
      · rcases ((SimpleGraph.edge_adj _ _ _ _).mp e).1 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact hcol
        · exact hcol.symm
    have eq : H = J := hm J ⟨hgh.trans hsub,hjCross,hb⟩ hsub
    exact no (eq.symm ▸ hxy)
  have base := deg x y hcol (fun h => no (hgh h))
  have hx := SimpleGraph.degree_le_of_le (v:=x) hgh
  have hy := SimpleGraph.degree_le_of_le (v:=y) hgh
  have size : 3 ≤ Fintype.card V := by
    have ht := Finset.card_sdiff_add_card_inter
      (s := (Finset.univ : Finset V)) (t := Finset.univ.filter fun v => color v = true)
    have hT : ((Finset.univ : Finset V) ∩ (Finset.univ.filter fun v => color v = true)).card =
        colorCount color true := by simp [colorCount]
    have hF : ((Finset.univ : Finset V) \ (Finset.univ.filter fun v => color v = true)).card =
        colorCount color false := by
      congr 1
      ext i
      cases h : color i <;> simp [colorCount,h]
    rw [Finset.card_univ,hT,hF] at ht
    omega
  exact hH.2.2 (close_one_cross H color hcross cx cy no size (by omega) hJ)

#print axioms bipartite_ore_cycle


lemma spanning_path_of_chain {V : Type*} {G : SimpleGraph V}
    {l : List V} (hne : l ≠ []) (hn : l.Nodup) (hu : ∀ v, v ∈ l) (hc : l.Chain' G.Adj) :
    GraphPathLift.HasSpanningPath G := by
  have pairs {p : List V} : p.Chain' G.Adj →
      ∀ e ∈ GraphPathLift.edgePairs p, G.Adj e.1 e.2 := by
    intro h e he
    induction p with
    | nil => simp [GraphPathLift.edgePairs] at he
    | cons a t ih =>
      cases t with
      | nil => simp [GraphPathLift.edgePairs] at he
      | cons b q =>
        simp only [GraphPathLift.edgePairs, List.mem_cons] at he
        rcases he with rfl | he
        · exact h.rel_head
        · exact ih h.tail he
  exact GraphPathLift.spanningPath_of_list G l hne hn hu (pairs hc)

private def dummyGraph {V : Type*} (G : SimpleGraph V) (color : V → Bool) :
    SimpleGraph (Option V) where
  Adj
    | some x, some y => G.Adj x y
    | some x, none => color x = true
    | none, some y => color y = true
    | none, none => False
  symm := by
    intro x y h
    cases x <;> cases y
    · exact h
    · exact h
    · exact h
    · exact G.symm h
  loopless := by
    intro x h
    cases x
    · exact h
    · exact G.loopless _ h

private def padColor {V : Type*} (color : V → Bool) : Option V → Bool
  | none => false
  | some v => color v

private theorem dummy_degree {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (color : V → Bool) (J : SimpleGraph (Option V))
    [DecidableRel J.Adj] (hJ : J = dummyGraph G color) (x : V) :
    J.degree (some x) = G.degree x + (if color x then 1 else 0) := by
  classical
  rw [← J.card_neighborFinset_eq_degree, ← G.card_neighborFinset_eq_degree]
  let s := G.neighborFinset x
  let f : V ↪ Option V := ⟨some, Option.some_injective V⟩
  have mem (v : Option V) : v ∈ J.neighborFinset (some x) ↔
      (if color x then v ∈ s.insertNone else v ∈ s.map f) := by
    rw [J.mem_neighborFinset, hJ]
    cases hc : color x <;> cases v <;>
      simp [dummyGraph,hc,s,f,G.mem_neighborFinset]
  cases h : color x
  · have eq : J.neighborFinset (some x) = s.map f := by ext v; simpa [h] using mem v
    rw [eq,Finset.card_map]
    simp [s,h]
  · have eq : J.neighborFinset (some x) = s.insertNone := by ext v; simpa [h] using mem v
    rw [eq,Finset.card_insertNone]
    simp [s,h]

private theorem padded_counts {V : Type*} [Fintype V] (color : V → Bool) :
    colorCount (padColor color) true = colorCount color true ∧
    colorCount (padColor color) false = colorCount color false + 1 := by
  classical
  let T := Finset.univ.filter (fun v => color v = true)
  let F := Finset.univ.filter (fun v => color v = false)
  let f : V ↪ Option V := ⟨some, Option.some_injective V⟩
  have ht : Finset.univ.filter (fun v => padColor color v = true) = T.map f := by
    ext v
    cases v <;> simp [padColor,T,f]
  have hf : Finset.univ.filter (fun v => padColor color v = false) = F.insertNone := by
    ext v
    cases v <;> simp [padColor,F]
  exact ⟨by unfold colorCount; rw [ht,Finset.card_map],
    by unfold colorCount; rw [hf,Finset.card_insertNone]⟩

private theorem remove_dummy {V : Type*} [Nonempty V] {G : SimpleGraph V}
    {col : V → Bool} : CycleList (dummyGraph G col) → GraphPathLift.HasSpanningPath G := by
  rintro ⟨l,hn,hu,hc⟩
  obtain ⟨A,B,hAB⟩ := split_at_mem none l (hu none)
  rw [hAB] at hn hc
  have hrot := rotate_cycle (A:=A) (B:=none::B) hc
  have hp : (none :: (B ++ A)).Perm l := hAB ▸ (List.perm_append_comm (l₁ := none :: B) (l₂ := A))
  have hnod : (none :: (B ++ A)).Nodup := hp.nodup_iff.mpr (hAB.symm ▸ hn)
  obtain ⟨q,hq⟩ := option_map_some (B ++ A) (List.nodup_cons.mp hnod).1
  have hfull (v : V) : v ∈ q := by
    have hmem := hp.mem_iff.mpr (hu (some v))
    have hm : some v ∈ B ++ A := (List.mem_cons.mp hmem).resolve_left (by simp)
    rw [← hq] at hm
    obtain ⟨w,hw,he⟩ := List.mem_map.mp hm
    cases he
    exact hw
  have hne : q ≠ [] := by
    intro he
    obtain ⟨v⟩ := (inferInstance : Nonempty V)
    simpa [he] using hfull v
  have hchain : (q.map some).Chain' (dummyGraph G col).Adj := hq ▸ hrot.1.tail
  exact spanning_path_of_chain hne
    (List.Nodup.of_map some (hq ▸ (List.nodup_cons.mp hnod).2)) hfull
    ((List.chain'_map (some : V → Option V)).mp hchain)

/-- A balanced or near-balanced bipartite version for paths. In the latter
case add one universal dummy on the smaller side and then remove it from
the cycle. The degree sum includes that single extra neighbor. -/
theorem bipartite_ore_path {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (color : V → Bool) (cross : ∀ x y, G.Adj x y → color x ≠ color y)
    (pos : 2 ≤ colorCount color true)
    (lower : colorCount color false ≤ colorCount color true)
    (upper : colorCount color true ≤ colorCount color false + 1)
    (deg : ∀ x y, color x ≠ color y → ¬ G.Adj x y →
      colorCount color true + 1 ≤ G.degree x + G.degree y +
        (colorCount color true - colorCount color false)) :
    GraphPathLift.HasSpanningPath G := by
  classical
  have existsTrue : ∃ x : V, color x = true := by
    have h : 0 < colorCount color true := by omega
    obtain ⟨x,hx⟩ := Finset.card_pos.mp h
    exact ⟨x,(Finset.mem_filter.mp hx).2⟩
  obtain ⟨x,hx⟩ := existsTrue
  letI : Nonempty V := ⟨x⟩
  by_cases he : colorCount color true = colorCount color false
  · have d : ∀ x y, color x ≠ color y → ¬ G.Adj x y →
      colorCount color true + 1 ≤ G.degree x + G.degree y := by
      intro x y h h'
      simpa [he] using deg x y h h'
    obtain ⟨l,hn,hu,hc⟩ := bipartite_ore_cycle G color cross he pos d
    exact spanning_path_of_chain (fun h => by simpa [h] using hu x) hn hu hc.1
  · let J := dummyGraph G color
    letI : DecidableRel J.Adj := Classical.decRel _
    have hcol (x y : Option V) (h : J.Adj x y) :
        padColor color x ≠ padColor color y := by
      cases x <;> cases y
      · exact h.elim
      · have h' : color _ = true := h
        simp [padColor,h']
      · have h' : color _ = true := h
        simp [padColor,h']
      · exact cross _ _ h
    have counts := padded_counts color
    have bal : colorCount (padColor color) true = colorCount (padColor color) false := by omega
    have p : 2 ≤ colorCount (padColor color) true := by omega
    have d (x y : Option V) (h : padColor color x ≠ padColor color y) (h' : ¬ J.Adj x y) :
        colorCount (padColor color) true + 1 ≤ J.degree x + J.degree y := by
      cases x <;> cases y
      · exact (h rfl).elim
      · cases hcy : color _
        · exact (h hcy.symm).elim
        · exact (h' hcy).elim
      · cases hcx : color _
        · exact (h hcx).elim
        · exact (h' hcx).elim
      · have hd := deg _ _ h h'
        rw [dummy_degree G color J rfl, dummy_degree G color J rfl]
        rename_i a b
        cases hca : color a <;> cases hcb : color b <;> simp [hca,hcb]
        · exact (h (hca.trans hcb.symm)).elim
        · omega
        · omega
        · exact (h (hca.trans hcb.symm)).elim
    exact remove_dummy (bipartite_ore_cycle J _ hcol bal p d)

#print axioms bipartite_ore_path

end Graffiti189TriangleFree
