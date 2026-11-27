import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Chain
import Mathlib.Data.Finset.Card
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Tactic.Linarith

/- Proof module: TraceClosure -/

namespace TraceClosure

universe u

def Traceable {V : Type u} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ p : List V, p.Nodup ∧ p.length = Fintype.card V ∧ p.Chain' G.Adj

private theorem chain_reverse {α : Type*} {R : α → α → Prop}
    (hs : ∀ x y, R x y → R y x) {l : List α} (h : l.Chain' R) :
    l.reverse.Chain' R :=
  List.chain'_reverse.mpr (h.imp hs)

private theorem no_pair_count {α : Type*} (a b : α → Bool) (l : List α)
    (h : l.Chain' fun u v => ¬ (a u = true ∧ b v = true)) :
    l.dropLast.countP a + l.tail.countP b ≤ l.length - 1 := by
  induction l with
  | nil => simp
  | cons u t ih =>
    cases t with
    | nil => simp
    | cons v r =>
      have ht := ih h.tail
      have hrel := h.rel_head
      rw [List.dropLast_cons₂]
      simp only [List.countP_cons (a := u), List.tail_cons, List.length_cons] at *
      rw [List.countP_cons (a := v)]
      cases ha : a u <;> cases hb : b v
      · simp [ha,hb] at *; omega
      · simp [ha,hb] at *; omega
      · simp [ha,hb] at *; omega
      · exact (hrel ⟨ha,hb⟩).elim

private theorem find_pair {α : Type*} {a b : α → Bool} {l : List α} {x y : α}
    (hx : l.head? = some x) (hy : l.getLast? = some y)
    (hax : a y = false) (hby : b x = false)
    (ht : l.length ≤ l.countP a + l.countP b) :
    ∃ (L : List α) (u v : α) (M : List α), l = L ++ u :: v :: M ∧ a u = true ∧ b v = true := by
  classical
  by_contra hn
  have hchain : l.Chain' (fun u v => ¬ (a u = true ∧ b v = true)) := by
    apply List.chain'_iff_forall_rel_of_append_cons_cons.mpr
    intro u v L M hl hab
    exact hn ⟨L,u,v,M,hl,hab⟩
  have hc := no_pair_count a b l hchain
  have hA : l.countP a = l.dropLast.countP a := by
    have he : l.dropLast ++ [y] = l := List.dropLast_append_getLast? y (by rw [hy]; rfl)
    have hh := congrArg (List.countP a) he
    simpa [List.countP_append,hax] using hh.symm
  have hB : l.countP b = l.tail.countP b := by
    obtain ⟨t,ht⟩ := List.head?_eq_some_iff.mp hx
    rw [ht]
    simp [List.countP_cons,hby]
  have hpos : 0 < l.length := by
    obtain ⟨t,ht⟩ := List.head?_eq_some_iff.mp hx
    simp [ht]
  omega

private def Cyclic {α : Type*} (R : α → α → Prop) (l : List α) : Prop :=
  l.Chain' R ∧ ∀ x ∈ l.getLast?, ∀ y ∈ l.head?, R x y

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

private theorem univRel_symm {V : Type*} (G : SimpleGraph V) :
    ∀ x y, univRel G x y → univRel G y x := by
  intro x y h
  rcases x with _ | x <;> rcases y with _ | y
  · exact h
  · trivial
  · trivial
  · exact G.symm h

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

private theorem count_deg {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {p : List V} (hn : p.Nodup) (hl : p.length = Fintype.card V) (x : V) :
    (none :: p.map some).countP (mark (univRel G) (some x)) = G.degree x + 1 := by
  classical
  have ht : mark (univRel G) (some x) none = true := mark_true.mpr trivial
  let f := mark (univRel G) (some x) ∘ some
  have hfil : (p.filter f).toFinset = G.neighborFinset x := by
    rw [List.toFinset_filter, full_toFinset hn hl]
    ext y
    simp [f,univRel, G.mem_neighborFinset]
  have hc : (p.filter f).length = G.degree x := by
    rw [← List.toFinset_card_of_nodup (hn.filter f), hfil, G.card_neighborFinset_eq_degree]
  have hd : p.countP f = G.degree x := by
    rw [List.countP_eq_length_filter, hc]
  simpa [List.countP_cons,List.countP_map,ht,f] using hd

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

private theorem chain_option {V : Type*} (G : SimpleGraph V) {p : List V}
    (h : p.Chain' G.Adj) : (p.map some).Chain' (univRel G) := by
  exact (List.chain'_map (some : V → Option V)).mpr h

private theorem augmentation {V : Type*} (G : SimpleGraph V) {x y : V} {L M : List V}
    (h1 : (L ++ [x]).Chain' G.Adj) (h2 : (y :: M).Chain' G.Adj) :
    ∃ t : List (Option V), t.head? = some (some x) ∧ t.getLast? = some (some y) ∧
      t.Chain' (univRel G) ∧ t.Perm (none :: (L ++ x :: y :: M).map some) := by
  let A : List (Option V) := (L ++ [x]).reverse.map some
  let B : List (Option V) := (y :: M).reverse.map some
  have hnA : A ≠ [] := by simp [A]
  have hnB : B ≠ [] := by simp [B]
  have hCA : A.Chain' (univRel G) := chain_option G (chain_reverse (fun _ _ h => G.symm h) h1)
  have hCB : B.Chain' (univRel G) := chain_option G (chain_reverse (fun _ _ h => G.symm h) h2)
  have ha : A.head? = some (some x) := by
    simp [A,List.head?_map,List.head?_reverse,List.getLast?_append_cons]
  have hb : B.getLast? = some (some y) := by simp [B,List.getLast?_map,List.getLast?_reverse]
  refine ⟨A ++ none :: B, ?_, ?_, ?_, ?_⟩
  · rwa [List.head?_append_of_ne_nil A hnA]
  · rw [show A ++ none :: B = (A ++ [none]) ++ B by simp]
    rwa [List.getLast?_append_of_ne_nil _ hnB]
  · have haNone : none ∉ A := by simp [A]
    have hbNone : none ∉ B := by simp [B]
    have hFront : (none :: B).Chain' (univRel G) := by
      apply hCB.cons'
      intro v hv
      cases v
      · exact (hbNone (List.mem_of_mem_head? hv)).elim
      · trivial
    apply hCA.append hFront
    intro u hu v hv
    have he : none = v := by simpa using hv
    subst v
    cases u
    · exact (haNone (List.mem_of_mem_getLast? hu)).elim
    · trivial
  · have hpA := (List.reverse_perm (L ++ [x])).map (some : V → Option V)
    have hpB := (List.reverse_perm (y :: M)).map (some : V → Option V)
    have him : (A ++ B).Perm ((L ++ x :: y :: M).map some) := by
      rw [show L ++ x :: y :: M = (L ++ [x]) ++ y :: M by simp,List.map_append]
      exact hpA.append hpB
    have hm : (A ++ none :: B).Perm (none :: (A ++ B)) := by
      simpa only [List.append_assoc] using
        (List.perm_append_comm (l₁ := A) (l₂ := [none])).append_right B
    exact hm.trans (him.cons _)

private theorem omit_hub {V : Type*} [Fintype V] (G : SimpleGraph V)
    {p : List V} (hn : p.Nodup) (hl : p.length = Fintype.card V)
    {c : List (Option V)} (hc : Cyclic (univRel G) c) (hp : c.Perm (none :: p.map some)) :
    Traceable G := by
  have hn' : (none :: p.map some).Nodup :=
    List.nodup_cons.mpr ⟨by simp, hn.map (Option.some_injective V)⟩
  have hmem : none ∈ c := hp.mem_iff.mpr (by simp)
  obtain ⟨A,B,he⟩ := split_at_mem none c hmem
  rw [he] at hc hp
  have hrot := rotate_cycle (A := A) (B := none :: B) hc
  have hpc : (none :: (B ++ A)).Perm (none :: p.map some) :=
    (List.perm_append_comm (l₁ := none :: B) (l₂ := A)).trans hp
  have hnod : (none :: (B ++ A)).Nodup := hpc.nodup_iff.mpr hn'
  obtain ⟨q,hq⟩ := option_map_some (B ++ A) (List.nodup_cons.mp hnod).1
  refine ⟨q, ?_, ?_, ?_⟩
  · exact List.Nodup.of_map some (hq ▸ (List.nodup_cons.mp hnod).2)
  · have ht := hpc.length_eq
    simpa [← hq, hl] using ht
  · have hChain : (q.map some).Chain' (univRel G) := hq ▸ hrot.1.tail
    exact (List.chain'_map (some : V → Option V)).mp hChain

private theorem close_split {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (x y : V) (L M : List V)
    (hn : (L ++ x :: y :: M).Nodup) (hl : (L ++ x :: y :: M).length = Fintype.card V)
    (hc : (L ++ x :: y :: M).Chain' (G ⊔ SimpleGraph.edge x y).Adj)
    (hd : Fintype.card V - 1 ≤ G.degree x + G.degree y) : Traceable G := by
  obtain ⟨t,hx,hy,ht,hperm⟩ :=
    augmentation G (split_left G hn hc) (split_right G hn hc)
  have hlen : t.length = Fintype.card V + 1 := by
    simpa only [List.length_cons, List.length_map, hl] using hperm.length_eq
  have hdx := (hperm.countP_eq (mark (univRel G) (some x))).trans (count_deg G hn hl x)
  have hdy := (hperm.countP_eq (mark (univRel G) (some y))).trans (count_deg G hn hl y)
  have hcx : mark (univRel G) (some x) (some x) = false := mark_false (G.loopless x)
  have hcy : mark (univRel G) (some y) (some y) = false := mark_false (G.loopless y)
  have ht' : t.length ≤ t.countP (mark (univRel G) (some y)) +
      t.countP (mark (univRel G) (some x)) := by
    omega
  obtain ⟨A,a,b,B,hsep,ha,hb⟩ := find_pair hx hy hcy hcx ht'
  obtain ⟨c,hc,hpc⟩ := cycled (univRel_symm G) hx hy ht hsep (mark_true.mp ha) (mark_true.mp hb)
  exact omit_hub G hn hl hc (hpc.trans hperm)

private theorem edge_comm {V : Type*} (x y : V) :
    SimpleGraph.edge x y = SimpleGraph.edge y x := by
  ext a b
  simp only [SimpleGraph.edge_adj]
  tauto

/-- The traceability form of the Bondy–Chvátal edge-closure step. -/
theorem traceable_sup_edge {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (x y : V) (hd : Fintype.card V - 1 ≤ G.degree x + G.degree y) :
    Traceable (G ⊔ SimpleGraph.edge x y) → Traceable G := by
  classical
  rintro ⟨p,hn,hl,hc⟩
  by_cases hgood : p.Chain' G.Adj
  · exact ⟨p,hn,hl,hgood⟩
  have hex : ∃ (a b : V) (L M : List V), p = L ++ a :: b :: M ∧ ¬ G.Adj a b := by
    by_contra hh
    apply hgood
    apply List.chain'_iff_forall_rel_of_append_cons_cons.mpr
    intro a b L M hp
    by_contra hd
    exact hh ⟨a,b,L,M,hp,hd⟩
  rcases hex with ⟨a,b,L,M,rfl,hab⟩
  have he := (List.chain'_append_cons_cons.mp hc).2.1
  have he := ((SimpleGraph.sup_adj _ _ _ _).mp he).resolve_left hab
  rcases ((SimpleGraph.edge_adj _ _ _ _).mp he).1 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact close_split G _ _ L M hn hl hc hd
  · rw [edge_comm] at hc
    exact close_split G _ _ L M hn hl hc (by omega)

#print axioms traceable_sup_edge


theorem traceable_mono {V : Type*} [Fintype V] {G H : SimpleGraph V} (h : G ≤ H) :
    Traceable G → Traceable H := by
  rintro ⟨p,hn,hl,hc⟩
  exact ⟨p,hn,hl,hc.imp (fun _ _ h' => h h')⟩

theorem traceable_top (V : Type*) [Fintype V] : Traceable (⊤ : SimpleGraph V) := by
  let e := (Fintype.equivFin V).symm
  let p := List.ofFn e
  have hn : p.Nodup := List.nodup_ofFn.mpr e.injective
  refine ⟨p,hn,List.length_ofFn,?_⟩
  apply List.chain'_iff_forall_rel_of_append_cons_cons.mpr
  intro a b L M he
  apply (SimpleGraph.top_adj _ _).mpr
  intro hh
  have hN : (a :: b :: M).Nodup := (he ▸ hn).of_append_right
  exact (List.nodup_cons.mp hN).1 (by simp [hh])



/-- A nontraceable finite graph has an edge-maximal nontraceable supergraph. -/
theorem exists_maximal_nontraceable_supergraph {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hnt : ¬Traceable G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ ¬Traceable H ∧
      ∀ x y, Hᶜ.Adj x y → Traceable (H ⊔ SimpleGraph.edge x y) := by
  classical
  let S : Set (SimpleGraph V) := {H | G ≤ H ∧ ¬Traceable H}
  obtain ⟨H,hH,hm⟩ := (Set.toFinite S).exists_maximal_wrt id S ⟨G,le_rfl,hnt⟩
  refine ⟨H,hH.1,hH.2,?_⟩
  intro x y hxy
  obtain ⟨hne,hna⟩ := (SimpleGraph.compl_adj H x y).mp hxy
  by_contra ht
  let J := H ⊔ SimpleGraph.edge x y
  have hsub : H ≤ J := le_sup_left
  have hj : J.Adj x y := (SimpleGraph.sup_adj _ _ _ _).mpr
    (Or.inr ((SimpleGraph.edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl,rfl⟩,hne⟩))
  have hJ : J ∈ S := ⟨hH.1.trans hsub,ht⟩
  have heq : H = J := hm J hJ hsub
  exact hna (heq.symm ▸ hj)

/-- Ore's degree-sum condition for spanning paths. -/
theorem ore_traceable {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (hd : ∀ x y, x ≠ y → ¬G.Adj x y → Fintype.card V - 1 ≤ G.degree x + G.degree y) :
    Traceable G := by
  classical
  by_contra hn
  obtain ⟨H,hgh,hnt,hmax⟩ := exists_maximal_nontraceable_supergraph G hn
  letI : DecidableRel H.Adj := Classical.decRel _
  have hxyn : ∃ x y, x ≠ y ∧ ¬H.Adj x y := by
    by_contra h
    apply hnt
    have heq : H = ⊤ := by
      ext x y
      rw [SimpleGraph.top_adj]
      exact ⟨fun hh => hh.ne, fun hne => by_contra fun hh => h ⟨x,y,hne,hh⟩⟩
    rw [heq]
    exact traceable_top V
  obtain ⟨x,y,hne,hnxy⟩ := hxyn
  have ht := hmax x y ((SimpleGraph.compl_adj H x y).mpr ⟨hne,hnxy⟩)
  have hdg := hd x y hne (fun h => hnxy (hgh h))
  have hx := SimpleGraph.degree_le_of_le (v := x) hgh
  have hy := SimpleGraph.degree_le_of_le (v := y) hgh
  exact hnt (traceable_sup_edge H x y (by omega) ht)

#print axioms exists_maximal_nontraceable_supergraph
#print axioms ore_traceable

end TraceClosure
