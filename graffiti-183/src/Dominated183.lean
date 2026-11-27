import BlockTrim183

namespace Graffiti183.Exceptional
open SimpleGraph Finset Short177
set_option maxHeartbeats 1600000
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] [DecidableRel G.Adj] in
private theorem within_cross {D B : Finset V} (sub : D ⊆ B)
    (conn : Graffiti177.Con G B) (d : D.Nonempty) (pr : D ≠ B) :
    ∃ a ∈ D, ∃ b ∈ B, b ∉ D ∧ G.Adj a b := by
  classical
  obtain ⟨a,da⟩ := d
  obtain ⟨b,bb,bd⟩ : ∃ b ∈ B, b ∉ D := by
    by_contra! e
    exact pr (Subset.antisymm sub e)
  let D' : Finset (B : Set V) := univ.filter (fun x => x.val ∈ D)
  let u : (B : Set V) := ⟨a,sub da⟩
  let v : (B : Set V) := ⟨b,bb⟩
  obtain ⟨p⟩ := conn u v
  have uu : u ∈ D' := by simp [D',u,da]
  have vv : v ∉ D' := by simp [D',v,bd]
  obtain ⟨x,hx,y,hy,e⟩ := Graffiti179.walk_cross (G.induce (B : Set V)) p uu vv
  exact ⟨x.val,(mem_filter.mp hx).2,y.val,y.property,by simpa [D'] using hy,e⟩

omit [DecidableRel G.Adj] in
private theorem trim_at_seed {B : Finset V} {s : V} (sb : s ∈ B)
    (co : Graffiti177.Con G B) (large : 1 < B.card) :
    ∃ x ∈ B, x ≠ s ∧ Graffiti177.Con G (B.erase x) ∧
      (∃ y ∈ B.erase x, G.Adj x y) := by
  classical
  let good (D : Finset V) := s ∈ D ∧ D ⊆ B ∧ D ≠ B ∧ Graffiti177.Con G D
  let all := (univ : Finset (Finset V)).filter good
  have cand : ({s} : Finset V) ∈ all := by
    apply mem_filter.mpr
    refine ⟨mem_univ _,by simp,singleton_subset_iff.mpr sb,?_,Graffiti177.con_single G s⟩
    intro e
    have eq := congrArg Finset.card e
    simp at eq
    omega
  obtain ⟨D,dm,maxD⟩ := exists_max_image all Finset.card ⟨{s},cand⟩
  obtain ⟨sd,sub,ne,dc⟩ := (mem_filter.mp dm).2
  obtain ⟨y,yd,x,xb,nxd,exy⟩ := within_cross G sub co ⟨s,sd⟩ ne
  have eq : insert x D = B := by
    by_contra no
    have mem : insert x D ∈ all := mem_filter.mpr ⟨mem_univ _,mem_insert_of_mem sd,
      insert_subset xb sub,no,Graffiti177.con_insert G dc yd exy.symm⟩
    have fin := maxD _ mem
    rw [card_insert_of_not_mem nxd] at fin
    omega
  have e : B.erase x = D := by rw [← eq, erase_insert nxd]
  refine ⟨x,xb,fun h => nxd (h.symm ▸ sd),?_,?_⟩
  · rw [e]; exact dc
  · exact ⟨y,e.symm ▸ yd,exy.symm⟩


omit [Fintype V] [DecidableRel G.Adj] in
private lemma erase_leaf_connected {T : Finset V} {w q : V}
    (hc : Graffiti177.Con G T) (hqw : q ≠ w) (hq : q ∈ T)
    (huniq : ∀ x ∈ T, G.Adj w x → x = q) :
    Graffiti177.Con G (T.erase w) := by
  classical
  let φ (x : (T : Set V)) : (↑(T.erase w) : Set V) :=
    if h : x.val = w then ⟨q,mem_erase.mpr ⟨hqw,hq⟩⟩ else
      ⟨x.val,mem_erase.mpr ⟨h,x.prop⟩⟩
  let H := G.induce (T : Set V)
  let K := G.induce (↑(T.erase w) : Set V)
  have he {x y : (T : Set V)} (e : H.Adj x y) :
      φ x = φ y ∨ K.Adj (φ x) (φ y) := by
    by_cases hx : x.val = w
    · have hyq := huniq y.val y.prop (show G.Adj w y.val from hx ▸ e)
      have hyw : y.val ≠ w := hyq ▸ hqw
      left
      apply Subtype.ext
      simp only [φ,dif_pos hx,dif_neg hyw]
      exact hyq.symm
    by_cases hy : y.val = w
    · have hxq := huniq x.val x.prop (show G.Adj w x.val from hy ▸ e.symm)
      left
      apply Subtype.ext
      simp only [φ,dif_neg hx,dif_pos hy]
      exact hxq
    · right
      simp only [φ,dif_neg hx,dif_neg hy]
      exact e
  have reach {x y : (T : Set V)} (p : H.Walk x y) : K.Reachable (φ x) (φ y) := by
    induction p with
    | nil => exact SimpleGraph.Reachable.rfl
    | cons e _ ih =>
      rcases he e with h | h
      · exact h.symm ▸ ih
      · exact h.reachable.trans ih
  have sur : Function.Surjective φ := by
    intro z
    obtain ⟨hn,hm⟩ := mem_erase.mp z.prop
    refine ⟨⟨z.val,hm⟩,?_⟩
    apply Subtype.ext
    simp only [φ,dif_neg hn]
  apply (connected_iff_exists_forall_reachable _).mpr
  refine ⟨φ ⟨q,hq⟩,?_⟩
  intro z
  obtain ⟨z,rfl⟩ := sur z
  obtain ⟨p⟩ := hc.preconnected ⟨q,hq⟩ z
  exact reach p

/-- Strict inclusion of closed neighborhoods at adjacent vertices is enough for the
order-plus-two leaf/bipartite bound. The strictness supplies an induced P3 seed. -/
theorem order_two_of_strict_adjacent_domination (hc : G.Connected)
    {w q z : V} (hwq : G.Adj w q) (hqz : G.Adj q z)
    (hwz : ¬G.Adj w z) (hnez : w ≠ z)
    (hinc : ∀ x, G.Adj w x → x ≠ q → G.Adj q x) :
    Fintype.card V + 2 ≤ Graffiti183.maxLeaves G + Graffiti183.bipartiteNumber G := by
  classical
  let seed : Finset V := {w,q,z}
  have conn : Graffiti177.Con G seed := by
    have hq : Graffiti177.Con G ({q,z} : Finset V) :=
      Graffiti177.con_insert G (Graffiti177.con_single G z) (mem_singleton_self _) hqz
    exact Graffiti177.con_insert G hq (by simp) hwq
  have bseed : Short177.TwoColor G seed := by
    refine ⟨{q},{w,z},?_,?_,?_,?_⟩
    · simp [hwq.ne,hqz.ne.symm]
    · ext x; simp [seed,or_assoc,or_left_comm,or_comm]
    · simp [Short177.Indep]
    · intro x hx y hy hn he
      simp only [mem_insert,mem_singleton] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact hn rfl
      · exact hwz he
      · exact hwz he.symm
      · exact hn rfl
  obtain ⟨b⟩ := Graffiti179.exists_block G (subset_univ seed) conn bseed
  let T := b.A ∪ b.B
  have hwT : w ∈ T := b.seeded (by simp [seed])
  have hqT : q ∈ T := b.seeded (by simp [seed])
  have hzT : z ∈ T := b.seeded (by simp [seed])
  have huniq (x : V) (hx : x ∈ T) (e : G.Adj w x) : x = q := by
    by_cases hne : x = q
    · exact hne
    exfalso
    have eqx := hinc x e hne
    rcases mem_union.mp hwT with hw | hw
    · have hqB : q ∈ b.B := (mem_union.mp hqT).resolve_left
        (fun hq => b.indA _ hw _ hq hwq.ne hwq)
      have hxB : x ∈ b.B := (mem_union.mp hx).resolve_left
        (fun hx => b.indA _ hw _ hx e.ne e)
      exact b.indB _ hqB _ hxB (fun h => hne h.symm) eqx
    · have hqA : q ∈ b.A := (mem_union.mp hqT).resolve_right
        (fun hq => b.indB _ hw _ hq hwq.ne hwq)
      have hxA : x ∈ b.A := (mem_union.mp hx).resolve_right
        (fun hx => b.indB _ hw _ hx e.ne e)
      exact b.indA _ hqA _ hxA (fun h => hne h.symm) eqx
  let T' := T.erase w
  have hq' : q ∈ T' := mem_erase.mpr ⟨hwq.ne.symm,hqT⟩
  have hz' : z ∈ T' := mem_erase.mpr ⟨hnez.symm,hzT⟩
  have hl : 1 < T'.card := by
    have hs : ({q,z}: Finset V) ⊆ T' := by simp [insert_subset_iff,hq',hz']
    have hh := card_le_card hs
    rw [card_pair hqz.ne] at hh
    omega
  have hcon' := erase_leaf_connected G b.conn hwq.ne.symm hqT huniq
  obtain ⟨d,hd,hdq,hdcon,y,hy,edy⟩ := trim_at_seed G hq' hcon' hl
  have hdT : d ∈ T := (mem_erase.mp hd).2
  have hdw : d ≠ w := (mem_erase.mp hd).1
  have hdEq : T'.erase d = T \ {w,d} := by
    ext x
    simp [T', and_assoc, and_comm, and_left_comm]
  have hqD : q ∈ T'.erase d := mem_erase.mpr ⟨hdq.symm,hq'⟩
  rw [hdEq] at hdcon hy hqD
  apply two_gain_from_block G b hc hwT hdT hdw.symm hdcon
  · exact ⟨q,hqD,hwq⟩
  · exact ⟨y,hy,edy⟩
  · rintro ⟨x,hx,xw,_xd,hn⟩
    have hxq : x ≠ q := fun e => hx (e.symm ▸ hqT)
    exact hn q hqD (hinc x xw.symm hxq).symm

#print axioms order_two_of_strict_adjacent_domination
end Graffiti183.Exceptional
