import DegreesLeaves
import Mathlib.Combinatorics.SimpleGraph.Circulant

open Finset SimpleGraph Graffiti271 GraffitiLeaves GraffitiDegrees
namespace GraffitiDegreeTwo
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

omit [Fintype V] in
theorem mem_support_label {a b : V} (p : G.Walk a b) {x : V} (hx : x ∈ p.support) :
    ∃ i : ℕ, i ≤ p.length ∧ p.getVert i = x := by
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem hx
  have hc : i ≤ p.length := by rw [p.length_support] at hi; omega
  refine ⟨i,hc,?_⟩
  have h := p.getVert_eq_support_get? hc
  rw [List.getElem?_eq_getElem hi, he] at h
  exact Option.some.inj h

theorem internal_neighbors [DecidableEq V] {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    {i : ℕ} (hi₀ : 0 < i) (hi : i < p.length)
    (hdeg : (nbr G (p.getVert i)).card ≤ 2) :
    nbr G (p.getVert i) = {p.getVert (i-1),p.getVert (i+1)} := by
  classical
  have hleft : G.Adj (p.getVert i) (p.getVert (i-1)) := by
    have he : i-1+1 = i := by omega
    have h := p.adj_getVert_succ (i := i-1) (by omega)
    rw [he] at h
    exact h.symm
  have hright := p.adj_getVert_succ hi
  have hne : p.getVert (i-1) ≠ p.getVert (i+1) := fun he => by
    have hn := hp.getVert_injOn (by show i-1 ≤ p.length; omega)
      (by show i+1 ≤ p.length; omega) he
    omega
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact (mem_nbr G).mpr hleft
    · exact (mem_nbr G).mpr hright
  · rw [Finset.card_pair hne]
    exact hdeg

theorem degree_some {v w : V} (h : G.Adj v w) (hdeg : (nbr G v).card = 1) :
    nbr G v = {w} := by
  classical
  symm
  apply Finset.eq_of_subset_of_card_le
  · simpa using (mem_nbr G).mpr h
  · simp [hdeg]

private theorem support_closed_of_ends_leaves (T : SimpleGraph V)
    {a b : V} (hne : a ≠ b) (p : T.Walk a b) (hp : p.IsPath)
    (hda : (nbr T a).card = 1) (hdb : (nbr T b).card = 1)
    (hdeg : ∀ v, (nbr T v).card ≤ 2) :
    ∀ u ∈ p.support, ∀ v, T.Adj u v → v ∈ p.support := by
  classical
  have hpos : 0 < p.length := by
    cases p with
    | nil => exact (hne rfl).elim
    | cons => simp
  intro u hu v huv
  obtain ⟨i,hil,rfl⟩ := mem_support_label T p hu
  by_cases hi0 : i=0
  · subst i
    rw [p.getVert_zero] at huv
    have hadj : T.Adj a (p.getVert 1) := by simpa using p.adj_getVert_succ (i := 0) hpos
    have hm := (mem_nbr T).mpr huv
    rw [degree_some T hadj hda, Finset.mem_singleton] at hm
    rw [hm]; exact p.getVert_mem_support _
  by_cases hie : i=p.length
  · rw [hie,p.getVert_length] at huv
    have hadj : T.Adj b (p.getVert (p.length-1)) := by
      have h := p.adj_getVert_succ (i := p.length-1) (by omega)
      have hl : p.length-1+1=p.length := by omega
      rw [hl,p.getVert_length] at h
      exact h.symm
    have hm := (mem_nbr T).mpr huv
    rw [degree_some T hadj hdb, Finset.mem_singleton] at hm
    rw [hm]; exact p.getVert_mem_support _
  have hm := (mem_nbr T).mpr huv
  rw [internal_neighbors T p hp (by omega) (by omega) (hdeg _)] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl <;> exact p.getVert_mem_support _

private theorem path_span (T : SimpleGraph V) (hT : T.Connected)
    {a b : V} (hne : a ≠ b) (p : T.Walk a b) (hp : p.IsPath)
    (hda : (nbr T a).card = 1) (hdb : (nbr T b).card = 1)
    (hdeg : ∀ v, (nbr T v).card ≤ 2) :
    ∀ v, v ∈ p.support := by
  have hclose := support_closed_of_ends_leaves T hne p hp hda hdb hdeg
  have hpath : ∀ {u v : V}, T.Walk u v → u ∈ p.support → v ∈ p.support := by
    intro u v q
    induction q with
    | nil => exact id
    | cons hadj q ih =>
      intro h
      exact ih (hclose _ h _ hadj)
  intro v
  obtain ⟨q⟩ := hT a v
  apply hpath q
  have hh := p.getVert_mem_support 0
  rw [p.getVert_zero] at hh
  exact hh

/-- Exact indexed classification: a path with a possible closing edge. -/
theorem degree_two_indexed (hc : G.Connected) (hn : 2 ≤ Fintype.card V)
    (hd : ∀ v, (nbr G v).card ≤ 2) :
    ∃ (m : ℕ) (_h : 1 ≤ m) (e : Fin (m+1) ≃ V) (wrap : Prop),
      ∀ i j : Fin (m+1), G.Adj (e i) (e j) ↔
        i.val+1=j.val ∨ j.val+1=i.val ∨
        (wrap ∧ ((i.val=0 ∧ j.val=m) ∨ (j.val=0 ∧ i.val=m))) := by
  classical
  obtain ⟨T,hTG,hT⟩ := hc.exists_isTree_le
  obtain ⟨r⟩ := hc.nonempty
  have hl := (tree_count T hT hn r).1
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp hl
  have hda : (nbr T a).card = 1 := (Finset.mem_filter.mp ha).2
  have hdb : (nbr T b).card = 1 := (Finset.mem_filter.mp hb).2
  have hdt : ∀ v, (nbr T v).card ≤ 2 := by
    intro v
    apply le_trans (Finset.card_le_card (t := nbr G v) ?_) (hd v)
    intro u hu
    exact (mem_nbr G).mpr (hTG ((mem_nbr T).mp hu))
  obtain ⟨p,hp,heq⟩ := hT.isConnected.exists_path_of_dist a b
  have hpos : 0 < p.length := by rw [heq]; exact hT.isConnected.pos_dist_of_ne hab
  let f : Fin (p.length+1) → V := fun i => p.getVert i.val
  have hfi : Function.Injective f := by
    intro i j he
    apply Fin.ext
    exact hp.getVert_injOn (by show i.val ≤ p.length; omega)
      (by show j.val ≤ p.length; omega) he
  have hfs : Function.Surjective f := by
    intro v
    obtain ⟨i,hi,he⟩ :=
      mem_support_label T p (path_span T hT.isConnected hab p hp hda hdb hdt v)
    exact ⟨⟨i,by omega⟩,he⟩
  let e : Fin (p.length+1) ≃ V := Equiv.ofBijective f ⟨hfi,hfs⟩
  let wrap := G.Adj a b
  refine ⟨p.length,hpos,e,wrap,?_⟩
  intro i j
  change G.Adj (p.getVert i.val) (p.getVert j.val) ↔ _
  have hli : i.val ≤ p.length := by omega
  have hlj : j.val ≤ p.length := by omega
  have same {k l : ℕ} (hk : k ≤ p.length) (hl : l ≤ p.length)
      (he : p.getVert k = p.getVert l) : k = l := hp.getVert_injOn hk hl he
  have hcG : ∀ {k : ℕ}, k < p.length → G.Adj (p.getVert k) (p.getVert (k+1)) :=
    fun h => hTG (p.adj_getVert_succ h)
  have hv {k : ℕ} (hk : k ≤ p.length) (h0 : k ≠ 0) (hm : k ≠ p.length) {l : ℕ}
      (hl : l ≤ p.length) (ha : G.Adj (p.getVert k) (p.getVert l)) :
      k+1 = l ∨ l+1 = k := by
    have hleft : G.Adj (p.getVert k) (p.getVert (k-1)) := by
      have hh := hcG (k := k-1) (by omega)
      have he : k-1+1=k := by omega
      rw [he] at hh
      exact hh.symm
    have hright := hcG (k := k) (by omega)
    have hne : p.getVert (k-1) ≠ p.getVert (k+1) := fun he => by
      have ht := same (k := k-1) (l := k+1) (by omega) (by omega) he
      omega
    have hpair : nbr G (p.getVert k) = {p.getVert (k-1),p.getVert (k+1)} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro v hv
        simp only [Finset.mem_insert,Finset.mem_singleton] at hv
        rcases hv with rfl | rfl
        · exact (mem_nbr G).mpr hleft
        · exact (mem_nbr G).mpr hright
      · rw [Finset.card_pair hne]
        exact hd _
    have hmem := (mem_nbr G).mpr ha
    rw [hpair] at hmem
    simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · have he := same hl (l := k-1) (by omega) h
      omega
    · have he := same hl (l := k+1) (by omega) h
      omega
  constructor
  · intro ha
    by_cases hi : i.val=0 ∨ i.val=p.length
    · by_cases hj : j.val=0 ∨ j.val=p.length
      · rcases hi with hi | hi <;> rcases hj with hj | hj
        · rw [hi,hj] at ha
          exact (G.loopless _ ha).elim
        · rw [hi,hj,p.getVert_zero,p.getVert_length] at ha
          exact Or.inr (Or.inr ⟨ha,Or.inl ⟨hi,hj⟩⟩)
        · rw [hi,hj,p.getVert_zero,p.getVert_length] at ha
          exact Or.inr (Or.inr ⟨ha.symm,Or.inr ⟨hj,hi⟩⟩)
        · rw [hi,hj] at ha
          exact (G.loopless _ ha).elim
      · have hr := hv hlj (fun hh => hj (Or.inl hh)) (fun hh => hj (Or.inr hh)) hli ha.symm
        exact hr.symm.imp_right Or.inl
    · have hr := hv hli (fun hh => hi (Or.inl hh)) (fun hh => hi (Or.inr hh)) hlj ha
      exact hr.imp_right Or.inl
  · rintro (h | h | ⟨h,(⟨hi,hj⟩ | ⟨hj,hi⟩)⟩)
    · rw [← h]; exact hcG (by omega)
    · rw [← h]; exact (hcG (by omega)).symm
    · simpa [hi,hj,p.getVert_zero,p.getVert_length] using h
    · simpa [hi,hj,p.getVert_zero,p.getVert_length] using (show G.Adj a b from h).symm

private theorem cycle_adj_linear {m : ℕ} (hm : 1 ≤ m) (i j : Fin (m+1)) :
    (cycleGraph (m+1)).Adj i j ↔
      i.val+1=j.val ∨ j.val+1=i.val ∨
        ((i.val=0 ∧ j.val=m) ∨ (j.val=0 ∧ i.val=m)) := by
  wlog h : i.val ≤ j.val generalizing i j
  · rw [show (cycleGraph (m+1)).Adj i j ↔ (cycleGraph (m+1)).Adj j i from
          ⟨fun e => e.symm, fun e => e.symm⟩, this j i (by omega)]
    tauto
  by_cases he : i=j
  · subst j
    have hf : ¬(cycleGraph (m+1)).Adj i i := (cycleGraph (m+1)).loopless i
    simp only [hf, false_iff]
    omega
  have hne : i.val ≠ j.val := fun hp => he (Fin.ext hp)
  have hj : (j-i).val = j.val-i.val := Fin.sub_val_of_le (show i ≤ j from h)
  have hi : (i-j).val = m+1-j.val+i.val := by
    rw [Fin.sub_def]
    simp only
    apply Nat.mod_eq_of_lt
    omega
  rw [cycleGraph_adj',hi,hj]
  omega

theorem degree_two_path_or_cycle (hc : G.Connected) (hn : 2 ≤ Fintype.card V)
    (hd : ∀ v, (nbr G v).card ≤ 2) :
    ∃ m : ℕ, 1 ≤ m ∧
      (Nonempty (G ≃g pathGraph (m+1)) ∨ Nonempty (G ≃g cycleGraph (m+1))) := by
  classical
  obtain ⟨m,hm,e,w,he⟩ := degree_two_indexed G hc hn hd
  refine ⟨m,hm,?_⟩
  by_cases hw : w
  · right
    let iso : cycleGraph (m+1) ≃g G :=
      { toEquiv := e
        map_rel_iff' := by
          intro i j
          rw [he,cycle_adj_linear hm]
          simp [hw] }
    exact ⟨iso.symm⟩
  · left
    let iso : pathGraph (m+1) ≃g G :=
      { toEquiv := e
        map_rel_iff' := by
          intro i j
          rw [he,pathGraph_adj]
          simp [hw] }
    exact ⟨iso.symm⟩

#print axioms degree_two_path_or_cycle
end GraffitiDegreeTwo
