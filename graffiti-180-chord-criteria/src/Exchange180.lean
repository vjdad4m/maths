import Converse180

set_option warningAsError true
namespace Converse180
open Finset SimpleGraph Graffiti177 Rooted180
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

noncomputable def ear (N : Finset V) : SimpleGraph (V ⊕ Unit) where
  Adj := Sum.elim (fun a => Sum.elim (G.Adj a) (fun _ => a∈N))
    (fun _ => Sum.elim (fun a => a∈N) (fun _ => False))
  symm := by rintro (a|a) (b|b) e <;> first | exact e.symm | exact e
  loopless := by rintro (a|a) e; exact G.loopless _ e; exact e

omit [DecidableEq V] in
theorem leaf_of_unique (T : SimpleGraph V) (con : T.Connected) (hn : 1 < Fintype.card V)
    (v : V) (unique : ∀ {a b}, T.Adj v a → T.Adj v b → a=b) : v ∈ leaves T := by
  classical
  obtain ⟨a,e⟩ := exists_adj T con hn v
  have sing : T.neighborFinset v = {a} := by
    ext b
    simp only [mem_neighborFinset,mem_singleton]
    exact ⟨fun h => unique h e,fun eq => eq ▸ e⟩
  exact mem_filter.mpr ⟨mem_univ _,by rw [← card_neighborFinset_eq_degree,sing,card_singleton]⟩

omit [Fintype V] [DecidableEq V] in
theorem ear_connected (hc : G.Connected) (N : Finset V) (nz : N.Nonempty) : (ear G N).Connected := by
  obtain ⟨a,ha⟩ := nz
  let inc : G →g ear G N := ⟨Sum.inl,fun e => e⟩
  apply (connected_iff_exists_forall_reachable _).mpr
  refine ⟨.inl a,?_⟩
  rintro (v|v)
  · exact (hc a v).map inc
  · exact (show (ear G N).Adj (.inl a) (.inr v) from ha).reachable

theorem attach_lower (hn : 1 < Fintype.card V) (U N : Finset V) (x : V) (xn : x ∈ N) :
    weightedLeaves G (U.erase x) ≤ weightedLeaves (ear G N) (U.disjSum ∅) := by
  classical
  apply Finset.sup_le
  intro T ht
  obtain ⟨st,tr⟩ := (mem_filter.mp ht).2
  let J := ear T {x}
  obtain ⟨K,ks,kt⟩ := (ear_connected T tr.isConnected _ (singleton_nonempty x)).exists_isTree_le
  have mono : K ≤ ear G N := by
    rintro (a|a) (b|b) e
    all_goals have h := ks e
    · exact st h
    · exact (mem_singleton.mp (show a∈({x}:Finset V) from h)) ▸ xn
    · exact (mem_singleton.mp (show b∈({x}:Finset V) from h)) ▸ xn
    · exact h.elim
  let L := U.erase x ∩ leaves T
  have inc : L.disjSum (∅ : Finset Unit) ⊆ (U.disjSum ∅) ∩ leaves K := by
    rintro (v|v) hv
    · have h := mem_inter.mp (inl_mem_disjSum.mp hv)
      refine mem_inter.mpr ⟨inl_mem_disjSum.mpr (mem_of_mem_erase h.1),?_⟩
      apply leaf_of_unique K kt.isConnected (by simp [Fintype.card_sum]; omega)
      rintro (a|a) (b|b) e f
      all_goals have p := ks e
      all_goals have q := ks f
      · exact congrArg Sum.inl (leaf_unique T h.2 p q)
      · exact ((mem_erase.mp h.1).1 (mem_singleton.mp (show v∈({x}:Finset V) from q))).elim
      · exact ((mem_erase.mp h.1).1 (mem_singleton.mp (show v∈({x}:Finset V) from p))).elim
      · exact congrArg Sum.inr (Subsingleton.elim a b)
    · simp at hv
  have count := card_le_card inc
  rw [card_disjSum,card_empty,Nat.add_zero] at count
  exact count.trans (le_sup (f := fun R => ((U.disjSum ∅) ∩ leaves R).card)
    (mem_filter.mpr ⟨mem_univ _,mono,kt⟩))

noncomputable def squash (T : SimpleGraph (V ⊕ Unit)) (c : V) : SimpleGraph V where
  Adj a b := T.Adj (.inl a) (.inl b) ∨
    (a=c ∧ b≠c ∧ T.Adj (.inr ()) (.inl b)) ∨
    (a≠c ∧ b=c ∧ T.Adj (.inl a) (.inr ()))
  symm := by
    rintro a b (e|⟨ha,hb,e⟩|⟨ha,hb,e⟩)
    · exact Or.inl e.symm
    · exact Or.inr (Or.inr ⟨hb,ha,e.symm⟩)
    · exact Or.inr (Or.inl ⟨hb,ha,e.symm⟩)
  loopless := by rintro a (e|⟨ha,hb,_⟩|⟨ha,hb,_⟩); exact e.ne rfl; exact hb ha; exact ha hb

noncomputable def foldPoint (c : V) : V ⊕ Unit → V := Sum.elim id (fun _ => c)

omit [Fintype V] [DecidableEq V] in
theorem squash_connected (T : SimpleGraph (V ⊕ Unit)) (con : T.Connected) (c : V) :
    (squash T c).Connected := by
  let f := foldPoint c
  have step {a b} (e : T.Adj a b) : f a = f b ∨ (squash T c).Adj (f a) (f b) := by
    rcases a with a|⟨⟩ <;> rcases b with b|⟨⟩
    · exact Or.inr (Or.inl e)
    · by_cases h : a=c
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr ⟨h,rfl,e⟩))
    · by_cases h : b=c
      · exact Or.inl h.symm
      · exact Or.inr (Or.inr (Or.inl ⟨rfl,h,e⟩))
    · exact Or.inl rfl
  have proj {a b} (p : T.Walk a b) : (squash T c).Reachable (f a) (f b) := by
    induction p with
    | nil => exact Reachable.refl _
    | cons e _ ih =>
      rcases step e with h|h
      · exact h ▸ ih
      · exact h.reachable.trans ih
  letI : Nonempty V := ⟨c⟩
  refine ⟨fun a b => ?_⟩
  obtain ⟨p⟩ := con (.inl a) (.inl b)
  exact proj p

theorem triangle_leaf_exchange (hn : 2 < Fintype.card V) (x y : V) (xy : G.Adj x y)
    (U : Finset V) :
    weightedLeaves (ear G {x,y}) (U.disjSum ∅) =
      max (weightedLeaves G (U.erase x)) (weightedLeaves G (U.erase y)) := by
  classical
  have h1 : 1 < Fintype.card V := by omega
  apply le_antisymm _ (max_le (attach_lower G h1 U _ x (by simp)) (attach_lower G h1 U _ y (by simp)))
  apply Finset.sup_le
  intro T ht
  obtain ⟨st,tr⟩ := (mem_filter.mp ht).2
  have out : ∃ k : V, k ∉ ({x,y} : Finset V) := by
    by_contra! h
    have hsub : (univ : Finset V) ⊆ {x,y} := fun v _ => h v
    have bound := card_le_card hsub
    rw [card_univ,card_pair xy.ne] at bound
    omega
  obtain ⟨k,kn⟩ := out
  let z : V ⊕ Unit := .inr ()
  obtain ⟨c,cn,internal⟩ : ∃ c ∈ ({x,y}:Finset V), Sum.inl c ∉ leaves T := by
    obtain ⟨q,eq,dq⟩ := Graffiti169.exists_predecessor T tr.isConnected (.inl k) z (fun e => Sum.noConfusion e)
    rcases q with c|q
    · have cn : c ∈ ({x,y} : Finset V) := st eq
      have ck : c ≠ k := fun e => kn (e ▸ cn)
      obtain ⟨w,ew,dw⟩ := Graffiti169.exists_predecessor T tr.isConnected (.inl k) (.inl c)
        (fun e => ck (Sum.inl.inj e))
      refine ⟨c,cn,fun leaf => ?_⟩
      have e := leaf_unique T leaf eq.symm ew
      rw [← e] at dw
      omega
    · exact (st eq).elim
  have clique {a b : V} (ha : a ∈ ({x,y}:Finset V)) (hb : b ∈ ({x,y}:Finset V)) (ne : a≠b) :
      G.Adj a b := by
    simp only [mem_insert,mem_singleton] at ha hb
    rcases ha with rfl|rfl <;> rcases hb with rfl|rfl <;> first | exact (ne rfl).elim | exact xy | exact xy.symm
  obtain ⟨K,ks,kt⟩ := (squash_connected T tr.isConnected c).exists_isTree_le
  have kg : K ≤ G := by
    intro a b e
    rcases ks e with old|⟨ha,hb,adj⟩|⟨ha,hb,adj⟩
    · exact st old
    · subst a; exact clique cn (st adj) hb.symm
    · subst b; exact clique (st adj) cn ha
  have inc : (U.disjSum (∅ : Finset Unit)) ∩ leaves T ⊆ (U.erase c ∩ leaves K).disjSum ∅ := by
    rintro (v|v) hv
    · obtain ⟨uv,leaf⟩ := mem_inter.mp hv
      have ne : v≠c := fun e => internal (e ▸ leaf)
      refine inl_mem_disjSum.mpr (mem_inter.mpr ⟨mem_erase.mpr ⟨ne,inl_mem_disjSum.mp uv⟩,?_⟩)
      apply leaf_of_unique K kt.isConnected h1
      have lift {a} (e : K.Adj v a) : ∃ t, T.Adj (.inl v) t ∧ foldPoint c t = a := by
        rcases ks e with e|⟨h,_,_⟩|⟨_,h,edge⟩
        · exact ⟨.inl a,e,rfl⟩
        · exact (ne h).elim
        · exact ⟨z,edge,h.symm⟩
      intro a b ea eb
      obtain ⟨t,et,dt⟩ := lift ea
      obtain ⟨j,ej,dj⟩ := lift eb
      exact dt.symm.trans ((congrArg (foldPoint c) (leaf_unique T leaf et ej)).trans dj)
    · simpa using (mem_inter.mp hv).1
  have count := card_le_card inc
  rw [card_disjSum,card_empty,Nat.add_zero] at count
  have bound := count.trans (le_sup (f := fun K => (U.erase c ∩ leaves K).card)
    (s := univ.filter (fun K : SimpleGraph V => K ≤ G ∧ K.IsTree)) (mem_filter.mpr ⟨mem_univ _,kg,kt⟩))
  change _ ≤ weightedLeaves G (U.erase c) at bound
  rcases mem_insert.mp cn with e|e
  · exact (e ▸ bound).trans (le_max_left _ _)
  · exact ((mem_singleton.mp e) ▸ bound).trans (le_max_right _ _)

#print axioms attach_lower
#print axioms triangle_leaf_exchange
end Converse180
