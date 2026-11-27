import SmallSeparator189

namespace Graffiti189TriangleOre
open SimpleGraph Finset Graffiti189LongestPath
set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

private lemma one_step (hc : G.Connected) (v : V) {x y : V} (h : G.Adj x y) :
    G.dist v x ≤ G.dist v y + 1 ∧ G.dist v y ≤ G.dist v x + 1 := by
  have dx := hc.dist_triangle (u:=v) (v:=y) (w:=x)
  have dy := hc.dist_triangle (u:=v) (v:=x) (w:=y)
  rw [dist_eq_one_iff_adj.mpr h.symm] at dx
  rw [dist_eq_one_iff_adj.mpr h] at dy
  exact ⟨dx, dy⟩

private lemma predecessor (hc : G.Connected) {v x : V} {i : ℕ}
    (hx : G.dist v x = i + 1) : ∃ y, G.Adj x y ∧ G.dist v y = i := by
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist x v
  have he := (dist_comm (G:=G) (u:=x) (v:=v))
  cases p with
  | nil => simp_all
  | @cons x y v h p =>
    refine ⟨y,h,?_⟩
    have u := G.dist_le p
    have hy := one_step hc v h
    rw [G.dist_comm] at u
    simp only [Walk.length_cons] at hp
    omega

private lemma two_step (hc : G.Connected)
    (tf : ∀ ⦃x y z : V⦄, G.Adj x y → G.Adj y z → ¬G.Adj x z)
    {x y z : V} (hne : x ≠ z) (h : G.Adj x y) (h' : G.Adj y z) :
    G.dist x z = 2 := by
  have l := hc.one_lt_dist_of_ne_of_not_adj hne (tf h h')
  have u := G.dist_le (Walk.cons h (Walk.cons h' .nil))
  simp at u
  omega

private lemma cut_at_frontier (hc : G.Connected)
    (conn : ∀ S : Finset V, S.card < 2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (v z : V) (hz : 3 ≤ G.dist v z) :
    2 ≤ ((Shell G v 2).filter fun b => ∃ c, G.dist v c = 3 ∧ G.Adj b c).card := by
  classical
  let S := (Shell G v 2).filter fun b => ∃ c, G.dist v c = 3 ∧ G.Adj b c
  change 2 ≤ S.card
  by_contra! h
  let W : Set V := (↑S : Set V)ᶜ
  let r : W := ⟨v, by simp [W,S,mem_shell,SimpleGraph.dist_self]⟩
  let t : W := ⟨z, by simp [W,S,mem_shell,SimpleGraph.dist_self]; omega⟩
  obtain ⟨p⟩ := (conn S h) r t
  have propagate {a b : W} (q : (G.induce W).Walk a b)
      (ha : G.dist v a.val ≤ 2) : G.dist v b.val ≤ 2 := by
    induction q with
    | nil => exact ha
    | @cons a b c e q ih =>
      apply ih
      change G.Adj a.val b.val at e
      have hb := (one_step hc v e).2
      apply Nat.le_of_not_gt
      intro htoo
      exact a.prop (Finset.mem_filter.mpr ⟨mem_shell.mpr (by omega), b.val, by omega, e⟩)
  have := propagate p (by simp [r,SimpleGraph.dist_self])
  exact (by change G.dist v z ≤ 2 at this; omega : False)

/-- Degree with the graph decision procedure supplied as data. -/
def degWith (H : SimpleGraph V) (dec : DecidableRel H.Adj) (v : V) : ℕ :=
  letI : DecidableRel H.Adj := dec
  H.degree v

def truePart (color : V → Bool) : Finset V := univ.filter fun x => color x = true
def falsePart (color : V → Bool) : Finset V := univ.filter fun x => color x = false

/-- A spanning subgraph whose balanced bipartite Ore hypothesis is obtained
after adding at most one dummy vertex to the smaller (false) part. -/
structure NearOre (G : SimpleGraph V) where
  graph : SimpleGraph V
  dec : DecidableRel graph.Adj
  sub : graph ≤ G
  color : V → Bool
  cross : ∀ u v, graph.Adj u v → color u ≠ color v
  large : 2 ≤ (truePart color).card
  first : (falsePart color).card ≤ (truePart color).card
  second : (truePart color).card ≤ (falsePart color).card + 1
  sumDeg : ∀ u v, color u ≠ color v → ¬graph.Adj u v →
    (truePart color).card + 1 ≤ degWith graph dec u + degWith graph dec v +
      ((truePart color).card - (falsePart color).card)

private theorem from_ordered (H : SimpleGraph V) [DecidableRel H.Adj] (sub : H ≤ G)
    (L R : Finset V) (part : ∀ v, v ∈ L ∨ v ∈ R) (dis : Disjoint L R)
    (cross : ∀ u v, H.Adj u v → (u∈L ∧ v∈R) ∨ (u∈R ∧ v∈L))
    (large : 2 ≤ L.card) (first : R.card ≤ L.card) (second : L.card ≤ R.card+1)
    (hdeg : ∀ u∈L, ∀ v∈R, ¬H.Adj u v → L.card+1 ≤ H.degree u + H.degree v + (L.card-R.card)) :
    Nonempty (NearOre G) := by
  let color : V → Bool := fun v => decide (v∈L)
  have t : truePart color = L := by ext v; simp [truePart,color]
  have f : falsePart color = R := by
    ext v
    simp [falsePart,color]
    constructor
    · intro hn
      exact (part v).resolve_left hn
    · intro hh h
      exact disjoint_left.mp dis h hh
  have ct {v : V} : color v = true ↔ v ∈ L := by simp [color]
  have cf {v : V} : color v = false ↔ v ∈ R := by
    have h : v ∈ falsePart color ↔ v ∈ R := by rw [f]
    simpa [falsePart] using h
  refine ⟨⟨H,inferInstance,sub,color,?_,by rw [t]; exact large,by rwa [t,f],
    by rwa [t,f],?_⟩⟩
  · intro u v e
    rcases cross u v e with ⟨uL,vR⟩|⟨uR,vL⟩
    · rw [ct.mpr uL,cf.mpr vR]; decide
    · rw [cf.mpr uR,ct.mpr vL]; decide
  · intro u v ne notA
    rw [t,f]
    change _ ≤ H.degree u + H.degree v + _
    cases uC : color u <;> cases vC : color v
    · exact (ne (uC.trans vC.symm)).elim
    · simpa only [Nat.add_comm (H.degree v) (H.degree u)] using
        hdeg v (ct.mp vC) u (cf.mp uC) (fun e => notA e.symm)
    · exact hdeg u (ct.mp uC) v (cf.mp vC) notA
    · exact (ne (uC.trans vC.symm)).elim

private theorem from_bip (L R : Finset V) (part : ∀ v, v ∈ L ∨ v∈R) (dis : Disjoint L R)
    (cross : ∀ u v,G.Adj u v → (u∈L∧v∈R) ∨ (u∈R∧v∈L))
    (d : ℕ) (ls : 2 ≤ L.card) (rs : 2 ≤ R.card)
    (lc : L.card ≤ d+1) (rc : R.card ≤ d+1)
    (lnear : L.card ≤ R.card+1) (rnear : R.card ≤ L.card+1)
    (mindeg : ∀ x,2≤G.degree x)
    (high : ∀ u v, u≠v → d ≤ G.degree u ∨ d ≤ G.degree v) : Nonempty (NearOre G) := by
  have ds (u v : V) (ne : u≠v) : d+2 ≤ G.degree u + G.degree v := by
    have a := mindeg u
    have b := mindeg v
    rcases high u v ne with h|h <;> omega
  by_cases h : R.card ≤ L.card
  · apply from_ordered G le_rfl L R part dis cross ls h lnear
    intro u hu v hv _
    have w := ds u v (fun he => disjoint_left.mp dis (he ▸ hu) hv)
    omega
  · apply from_ordered G le_rfl R L (fun v => (part v).symm) dis.symm
      (fun u v e => (cross u v e).symm) rs (by omega) rnear
    intro u hu v hv _
    have w := ds u v (fun he => disjoint_left.mp dis hv (he ▸ hu))
    omega

theorem ore_at_high_root
    (hc : G.Connected)
    (conn : ∀ S : Finset V, S.card < 2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (tf : ∀ ⦃x y z : V⦄, G.Adj x y → G.Adj y z → ¬G.Adj x z)
    {d : ℕ} (hd : 3 ≤ d)
    (cap : ∀ x, (EvenFrom G x).card ≤ d + 1)
    (high : ∀ u v : V, u ≠ v → d ≤ G.degree u ∨ d ≤ G.degree v)
    (mindeg : ∀ x, 2 ≤ G.degree x)
    (v : V) (hv : d ≤ G.degree v) :
    Nonempty (NearOre G) := by
  classical
  let A := Shell G v 1
  let B := Shell G v 2
  have mA {x : V} : x ∈ A ↔ G.Adj v x := mem_shell.trans dist_eq_one_iff_adj
  have mB {x : V} : x ∈ B ↔ G.dist v x = 2 := mem_shell
  have ac : A.card = G.degree v := by
    rw [← G.card_neighborFinset_eq_degree]
    congr 1
    ext x
    exact mA.trans (G.mem_neighborFinset v x).symm
  have bc : B.card ≤ d := distanceTwo_le_of_even d v (cap v)
  have dc (a : V) : (DistanceTwo G a).card ≤ d := distanceTwo_le_of_even d a (cap a)
  have aBudget {a b : V} (ha : a ∈ A) (hab : G.Adj a b) (hb : b ∈ B) :
      A.card - 1 + ((G.neighborFinset b) \ A).card ≤ d := by
    have dis : Disjoint (A.erase a) (G.neighborFinset b \ A) := by
      rw [Finset.disjoint_left]
      intro x hx hy
      exact (Finset.mem_sdiff.mp hy).2 (Finset.mem_of_mem_erase hx)
    have sub : A.erase a ∪ (G.neighborFinset b \ A) ⊆ DistanceTwo G a := by
      intro x hx
      simp only [DistanceTwo, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases Finset.mem_union.mp hx with hx | hx
      · exact two_step hc tf (Finset.ne_of_mem_erase hx).symm
          (mA.mp ha).symm (mA.mp (Finset.mem_of_mem_erase hx))
      · exact two_step hc tf (fun e => (Finset.mem_sdiff.mp hx).2 (e ▸ ha))
          hab ((G.mem_neighborFinset b x).mp (Finset.mem_sdiff.mp hx).1)
    have h := (Finset.card_le_card sub).trans (dc a)
    rwa [Finset.card_union_of_disjoint dis,Finset.card_erase_of_mem ha] at h
  have outside (b : V) (hb : b ∈ B) :
      A.card - 1 + ((G.neighborFinset b) \ A).card ≤ d := by
    obtain ⟨a,hba,ha⟩ := predecessor hc (mB.mp hb : G.dist v b = 1 + 1)
    exact aBudget (mem_shell.mpr ha) hba.symm hb
  obtain ⟨a,ha,haD⟩ : ∃ a ∈ A, d ≤ G.degree a := by
    have haC : 1 < A.card := by omega
    obtain ⟨a,ha,b,hb,hne⟩ := Finset.one_lt_card.mp haC
    rcases high a b hne with h | h
    · exact ⟨a,ha,h⟩
    · exact ⟨b,hb,h⟩
  have bcLower : d - 1 ≤ B.card := by
    have sub : (G.neighborFinset a).erase v ⊆ B := by
      intro x hx
      exact mB.mpr (two_step hc tf (Finset.ne_of_mem_erase hx).symm (mA.mp ha)
        ((G.mem_neighborFinset a x).mp (Finset.mem_of_mem_erase hx)))
    have h := Finset.card_le_card sub
    rw [Finset.card_erase_of_mem ((G.mem_neighborFinset a v).mpr (mA.mp ha).symm),
       G.card_neighborFinset_eq_degree] at h
    omega
  have acUpper : A.card ≤ d + 1 := by
    have sub : A.erase a ⊆ DistanceTwo G a := by
      intro x hx
      simp only [DistanceTwo, Finset.mem_filter, Finset.mem_univ, true_and]
      exact two_step hc tf (Finset.ne_of_mem_erase hx).symm
        (mA.mp ha).symm (mA.mp (Finset.mem_of_mem_erase hx))
    have h := (Finset.card_le_card sub).trans (dc a)
    rw [Finset.card_erase_of_mem ha] at h
    omega
  let R := insert v B
  have r0 : v ∉ B := by simp [B,mem_shell,SimpleGraph.dist_self]
  have rcard : R.card = B.card+1 := by
    dsimp [R]
    rw [Finset.card_insert_of_not_mem r0]
  have rcase {x : V} (hx : x∈R) : G.dist v x=0 ∨ G.dist v x=2 := by
    rcases Finset.mem_insert.mp hx with eq|b
    · simp [eq,SimpleGraph.dist_self]
    · exact Or.inr (mB.mp b)
  have dis : Disjoint A R := by
    apply disjoint_left.mpr
    intro x h1 h2
    have hA := (mem_shell.mp h1 : G.dist v x=1)
    rcases rcase h2 with eq|eq <;> omega
  have eq_near {x : V} (hx : G.dist v x≤2) : x∈A ∨ x∈R := by
    rcases (show G.dist v x=0 ∨ G.dist v x=1 ∨ G.dist v x=2 by omega) with da|da|da
    · exact Or.inr (mem_insert.mpr (Or.inl (hc.dist_eq_zero_iff.mp da).symm))
    · exact Or.inl (mem_shell.mpr da)
    · exact Or.inr (mem_insert_of_mem (mB.mpr da))
  have Aind {x y : V} (hx : x∈A) (hy : y∈A) : ¬G.Adj x y :=
    tf (mA.mp hx).symm (mA.mp hy)
  have Rind (hind : ∀ x∈B, ∀ y∈B, ¬G.Adj x y) {x y : V}
      (hx : x∈R) (hy : y∈R) : ¬G.Adj x y := by
    rcases mem_insert.mp hx with rfl|hx <;> rcases mem_insert.mp hy with rfl|hy
    · exact G.loopless _
    · intro e
      have e' := dist_eq_one_iff_adj.mpr e
      have d2 := mB.mp hy
      omega
    · intro e
      have e' := dist_eq_one_iff_adj.mpr e.symm
      have d2 := mB.mp hx
      omega
    · exact hind _ hx _ hy
  by_cases far : ∃ x, 3 ≤ G.dist v x
  · obtain ⟨x,hx⟩ := far
    let F := B.filter fun b => ∃ c, G.dist v c = 3 ∧ G.Adj b c
    have f2 : 2 ≤ F.card := cut_at_frontier hc conn v x hx
    obtain ⟨b,hb,c,hcF,hne⟩ := Finset.one_lt_card.mp (show 1 < F.card by omega)
    obtain ⟨b,hb,bd⟩ : ∃ b ∈ F, d ≤ G.degree b := by
      rcases high b c hne with h | h
      · exact ⟨b,hb,h⟩
      · exact ⟨c,hcF,h⟩
    obtain ⟨hbB,z,hz,hbz⟩ := Finset.mem_filter.mp hb
    have nzA : z ∉ A := by
      intro h
      have h' := (mem_shell.mp h : G.dist v z = 1)
      omega
    have bzOut : z ∈ G.neighborFinset b \ A := Finset.mem_sdiff.mpr
      ⟨(G.mem_neighborFinset b z).mpr hbz,nzA⟩
    have acEq : A.card = d := by
      have l := outside b hbB
      have k := Finset.card_pos.mpr ⟨z,bzOut⟩
      omega
    have outOne {b' : V} (hb' : b' ∈ B) : (G.neighborFinset b' \ A).card ≤ 1 := by
      have h := outside b' hb'
      omega
    have sameOut {b' y : V} (hb' : b' ∈ B) (hbD : d ≤ G.degree b')
        (hy : y ∈ G.neighborFinset b' \ A) : y = z := by
      let S := G.neighborFinset b ∩ A
      let T := G.neighborFinset b' ∩ A
      have cards (w : V) (hw : w ∈ B) (hdw : d ≤ G.degree w) :
          d - 1 ≤ (G.neighborFinset w ∩ A).card := by
        have h := Finset.card_sdiff_add_card_inter (s := G.neighborFinset w) (t := A)
        rw [G.card_neighborFinset_eq_degree] at h
        have h' := outOne hw
        omega
      obtain ⟨a,ha⟩ : (S ∩ T).Nonempty := by
        apply Classical.byContradiction
        intro hh
        have hdj := Finset.disjoint_iff_inter_eq_empty.mpr (Finset.not_nonempty_iff_eq_empty.mp hh)
        have h := Finset.card_le_card (show S ∪ T ⊆ A by
          intro i hi
          rcases Finset.mem_union.mp hi with hi | hi
          · exact (Finset.mem_inter.mp hi).2
          · exact (Finset.mem_inter.mp hi).2)
        rw [Finset.card_union_of_disjoint hdj] at h
        have hS : d - 1 ≤ S.card := cards b hbB bd
        have hT : d - 1 ≤ T.card := cards b' hb' hbD
        omega
      have haA : a ∈ A := (Finset.mem_inter.mp (Finset.mem_inter.mp ha).1).2
      have e : G.Adj a b := ((G.mem_neighborFinset _ _).mp
        (Finset.mem_inter.mp (Finset.mem_inter.mp ha).1).1).symm
      have e' : G.Adj a b' := ((G.mem_neighborFinset _ _).mp
        (Finset.mem_inter.mp (Finset.mem_inter.mp ha).2).1).symm
      have one : (DistanceTwo G a \ A).card ≤ 1 := by
        have he : A.erase a ⊆ DistanceTwo G a := by
          intro w hw
          simp only [DistanceTwo, Finset.mem_filter, Finset.mem_univ, true_and]
          exact two_step hc tf (Finset.ne_of_mem_erase hw).symm
            (mA.mp haA).symm (mA.mp (Finset.mem_of_mem_erase hw))
        have dis : Disjoint (A.erase a) (DistanceTwo G a \ A) := by
          rw [Finset.disjoint_left]
          intro w hw hw'
          exact (Finset.mem_sdiff.mp hw').2 (Finset.mem_of_mem_erase hw)
        have sub := (Finset.union_subset he (Finset.sdiff_subset : DistanceTwo G a \ A ⊆ DistanceTwo G a))
        have hh := (Finset.card_le_card sub).trans (dc a)
        rw [Finset.card_union_of_disjoint dis, Finset.card_erase_of_mem haA] at hh
        omega
      have mm {u w : V} (e : G.Adj a u) (hw : w ∈ G.neighborFinset u \ A) :
          w ∈ DistanceTwo G a \ A := by
        have hwa := (Finset.mem_sdiff.mp hw).2
        refine Finset.mem_sdiff.mpr ⟨?_,hwa⟩
        simp only [DistanceTwo, Finset.mem_filter, Finset.mem_univ, true_and]
        exact two_step hc tf (fun q => hwa (q ▸ haA)) e
          ((G.mem_neighborFinset _ _).mp (Finset.mem_sdiff.mp hw).1)
      exact Finset.card_le_one.mp one y (mm e' hy) z (mm e bzOut)
    have fourth : (Shell G v 4).card ≤ 1 := by
      have h0 : v ∉ B := by simp [B,mem_shell,SimpleGraph.dist_self]
      have dis : Disjoint (insert v B) (Shell G v 4) := by
        rw [Finset.disjoint_left]
        intro y hy hy'
        have hr := mem_shell.mp hy'
        rcases Finset.mem_insert.mp hy with rfl | hy
        · simp [SimpleGraph.dist_self] at hr
        · have := mB.mp hy
          omega
      have sub : insert v B ∪ Shell G v 4 ⊆ EvenFrom G v := by
        intro y hy
        simp only [EvenFrom,Finset.mem_filter,Finset.mem_univ,true_and]
        rcases Finset.mem_union.mp hy with hy | hy
        · rcases Finset.mem_insert.mp hy with rfl | hy
          · simp [SimpleGraph.dist_self]
          · rw [mB.mp hy]; decide
        · rw [mem_shell.mp hy]; decide
      have h := (Finset.card_le_card sub).trans (cap v)
      rw [Finset.card_union_of_disjoint dis,Finset.card_insert_of_not_mem h0] at h
      omega
    have noFifth (y : V) : G.dist v y ≤ 4 := by
      apply Nat.le_of_not_gt
      intro hy
      have := shell_card_of_far hc 2 conn (x:=v) (y:=y) (i:=4) (by omega) hy
      omega
    have onlyThird (w : V) (hw : G.dist v w = 3) : w = z := by
      apply Classical.byContradiction
      intro hn
      obtain ⟨l,hel,hl⟩ := predecessor hc (hw : G.dist v w = 2 + 1)
      have hlB := mB.mpr hl
      have dw (y : V) (hy : G.dist v y = 3) : y ∉ A := by
        intro h
        have hh := (mem_shell.mp h : G.dist v y = 1)
        omega
      have hwl : w ∈ G.neighborFinset l \ A := Finset.mem_sdiff.mpr
        ⟨(G.mem_neighborFinset _ _).mpr hel.symm,dw w hw⟩
      have low : G.degree l < d := Nat.lt_of_not_ge (fun h => hn (sameOut hlB h hwl))
      have allThird (u : V) (hu : G.dist v u = 3) : u = z ∨ u = w := by
        obtain ⟨j,huj,hj⟩ := predecessor hc (hu : G.dist v u = 2 + 1)
        have hjB := mB.mpr hj
        have hOut : u ∈ G.neighborFinset j \ A := Finset.mem_sdiff.mpr
          ⟨(G.mem_neighborFinset _ _).mpr huj.symm,dw u hu⟩
        by_cases eq : j = l
        · subst j
          exact Or.inr (Finset.card_le_one.mp (outOne hlB) u hOut w hwl)
        · exact Or.inl (sameOut hjB ((high j l eq).resolve_right (by omega)) hOut)
      have wz : ¬G.Adj w z := by
        intro e
        have atLeast := hd.trans ((high w l (by intro q; rw [q,hl] at hw; omega)).resolve_right (by omega))
        have sub : (G.neighborFinset w).erase z ⊆ insert l (Shell G v 4) := by
          intro u hu
          have eu := (G.mem_neighborFinset _ _).mp (Finset.mem_of_mem_erase hu)
          have step := one_step hc v eu
          have dist : G.dist v u = 2 ∨ G.dist v u = 3 ∨ G.dist v u = 4 := by omega
          rcases dist with du | du | du
          · apply Finset.mem_insert.mpr
            left
            apply Classical.byContradiction
            intro eq
            have hh := (high u l eq).resolve_right (by omega)
            exact hn (sameOut (mB.mpr du) hh (Finset.mem_sdiff.mpr
              ⟨(G.mem_neighborFinset _ _).mpr eu.symm,dw w hw⟩))
          · rcases allThird u du with eq | eq
            · exact ((Finset.ne_of_mem_erase hu) eq).elim
            · exact (eu.ne eq.symm).elim
          · exact Finset.mem_insert_of_mem (mem_shell.mpr du)
        have card := Finset.card_le_card sub
        rw [Finset.card_erase_of_mem ((G.mem_neighborFinset _ _).mpr e),
          G.card_neighborFinset_eq_degree] at card
        have hh := Finset.card_insert_le l (Shell G v 4)
        have has4 : (Shell G v 4).Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨u,hu⟩ := has4
        have du := mem_shell.mp hu
        have subu : G.neighborFinset u ⊆ {z,w} := by
          intro j hj
          have ej := (G.mem_neighborFinset _ _).mp hj
          have step := one_step hc v ej
          have dj : G.dist v j = 3 := by
            have hh := noFifth j
            apply Classical.byContradiction
            intro d3
            have d4 : G.dist v j = 4 := by omega
            exact ej.ne (Finset.card_le_one.mp fourth u hu j (mem_shell.mpr d4))
          simpa using allThird j dj
        have hwU : G.Adj u w := by
          apply Classical.byContradiction
          intro h
          have s : G.neighborFinset u ⊆ {z} := by
            intro j hj
            have h' := subu hj
            simp only [Finset.mem_insert,Finset.mem_singleton] at h' ⊢
            exact h'.resolve_right (fun eq => h (eq ▸ (G.mem_neighborFinset _ _).mp hj))
          have h' := Finset.card_le_card s
          rw [G.card_neighborFinset_eq_degree,Finset.card_singleton] at h'
          have := mindeg u
          omega
        have hzU : G.Adj u z := by
          apply Classical.byContradiction
          intro h
          have s : G.neighborFinset u ⊆ {w} := by
            intro j hj
            have h' := subu hj
            simp only [Finset.mem_insert,Finset.mem_singleton] at h' ⊢
            exact h'.resolve_left (fun eq => h (eq ▸ (G.mem_neighborFinset _ _).mp hj))
          have h' := Finset.card_le_card s
          rw [G.card_neighborFinset_eq_degree,Finset.card_singleton] at h'
          have := mindeg u
          omega
        exact tf hwU e hzU
      have sub : G.neighborFinset w ⊆ insert l (Shell G v 4) := by
        intro u hu
        have eu := (G.mem_neighborFinset _ _).mp hu
        have step := one_step hc v eu
        have dist : G.dist v u = 2 ∨ G.dist v u = 3 ∨ G.dist v u = 4 := by omega
        rcases dist with du | du | du
        · apply Finset.mem_insert.mpr
          left
          apply Classical.byContradiction
          intro eq
          have hh := (high u l eq).resolve_right (by omega)
          exact hn (sameOut (mB.mpr du) hh (Finset.mem_sdiff.mpr
            ⟨(G.mem_neighborFinset _ _).mpr eu.symm,dw w hw⟩))
        · rcases allThird u du with eq | eq
          · exact (wz (eq ▸ eu)).elim
          · exact (eu.ne eq.symm).elim
        · exact Finset.mem_insert_of_mem (mem_shell.mpr du)
      have card := Finset.card_le_card sub
      rw [G.card_neighborFinset_eq_degree] at card
      have hh := Finset.card_insert_le l (Shell G v 4)
      have ww := (high w l (by intro q; rw [q,hl] at hw; omega)).resolve_right (by omega)
      omega
    have noFourth (y : V) : G.dist v y ≠ 4 := by
      intro hy
      have h := shell_card_of_far hc 2 conn (x:=v) (y:=y) (i:=3) (by omega) (by omega)
      have k : (Shell G v 3).card ≤ 1 := Finset.card_le_one.mpr (by
        intro a ha b hb
        exact (onlyThird a (mem_shell.mp ha)).trans (onlyThird b (mem_shell.mp hb)).symm)
      omega
    have hind (u:V) (uB:u∈B) (w:V) (wB:w∈B) : ¬G.Adj u w := by
      intro e
      have dw := mB.mp wB
      have du := mB.mp uB
      have uout : u ∉ A := fun q => by have e := (mem_shell.mp q : G.dist v u=1); omega
      have wout : w ∉ A := fun q => by have e := (mem_shell.mp q : G.dist v w=1); omega
      rcases high u w e.ne with hu|hw
      · have e' := sameOut uB hu (Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset _ _).mpr e,wout⟩)
        rw [e'] at dw
        omega
      · have e' := sameOut wB hw (Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset _ _).mpr e.symm,uout⟩)
        rw [e'] at du
        omega
    let L := insert z A
    have Lc : L.card=d+1 := by simp [L,card_insert_of_not_mem nzA,acEq]
    have LR : Disjoint L R := by
      apply disjoint_left.mpr
      intro x hx hR
      rcases mem_insert.mp hx with rfl|hx
      · rcases rcase hR with eq|eq <;> omega
      · exact disjoint_left.mp dis hx hR
    have part (x : V) : x∈L ∨ x∈R := by
      have le := noFifth x
      have ne := noFourth x
      by_cases h : G.dist v x=3
      · exact Or.inl (mem_insert.mpr (Or.inl (onlyThird x h)))
      · exact (eq_near (by omega)).imp mem_insert_of_mem id
    have Lnd {x y : V} (hx : x∈L) (hy : y∈L) : ¬G.Adj x y := by
      have hx' : x=z ∨ x∈A := mem_insert.mp hx
      have hy' : y=z ∨ y∈A := mem_insert.mp hy
      rcases hx' with eqx|xA <;> rcases hy' with eqy|yA
      · rw [eqx,eqy]; exact G.loopless _
      · intro e
        have step := one_step hc v e
        have h := (mem_shell.mp yA : G.dist v y=1)
        rw [eqx,hz] at step
        omega
      · intro e
        have step := one_step hc v e
        have h := (mem_shell.mp xA : G.dist v x=1)
        rw [eqy,hz] at step
        omega
      · exact Aind xA yA
    have cross (x y : V) (e : G.Adj x y) : (x∈L∧y∈R) ∨ (x∈R∧y∈L) := by
      rcases part x with hx|hx <;> rcases part y with hy|hy
      · exact (Lnd hx hy e).elim
      · exact Or.inl ⟨hx,hy⟩
      · exact Or.inr ⟨hx,hy⟩
      · exact (Rind hind hx hy e).elim
    exact from_bip L R part LR cross d (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) mindeg high
  · have part (x : V) : x ∈ A ∨ x ∈ R := eq_near (by have e := not_exists.mp far x; omega)
    by_cases noedge : ∀ x∈B, ∀ y∈B, ¬G.Adj x y
    · have cross (x y : V) (e : G.Adj x y) : (x∈A∧y∈R) ∨ (x∈R∧y∈A) := by
        rcases part x with hx|hx <;> rcases part y with hy|hy
        · exact (Aind hx hy e).elim
        · exact Or.inl ⟨hx,hy⟩
        · exact Or.inr ⟨hx,hy⟩
        · exact (Rind noedge hx hy e).elim
      exact from_bip A R part dis cross d (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) mindeg high
    · push_neg at noedge
      obtain ⟨u,uB,w,wB,edge⟩ := noedge
      have wnotA : w ∉ A := fun h => disjoint_left.mp dis h (mem_insert_of_mem wB)
      have uout : w ∈ G.neighborFinset u \ A :=
        mem_sdiff.mpr ⟨(G.mem_neighborFinset _ _).mpr edge,wnotA⟩
      have acEq : A.card=d := by
        have h := outside u uB
        have poss := card_pos.mpr ⟨w,uout⟩
        omega
      have outOne (x : V) (hx : x∈B) : (G.neighborFinset x \ A).card ≤ 1 := by
        have h := outside x hx
        omega
      have degreeInside (x : V) (hx : x∈B) (hxdeg : d≤G.degree x) :
          d-1≤(G.neighborFinset x ∩ A).card := by
        have eq := card_sdiff_add_card_inter (s:=G.neighborFinset x) (t:=A)
        rw [card_neighborFinset_eq_degree] at eq
        have h := outOne x hx
        omega
      have someLow : ∃ z∈B, G.degree z < d := by
        by_cases hd₁ : d ≤ G.degree u
        · by_cases hd₂ : d ≤ G.degree w
          · let X := G.neighborFinset u ∩ A
            let Y := G.neighborFinset w ∩ A
            have Xd : d-1≤X.card := degreeInside u uB hd₁
            have Yd : d-1≤Y.card := degreeInside w wB hd₂
            have dXY : Disjoint X Y := by
              apply disjoint_left.mpr
              intro x hx hy
              have ux := (G.mem_neighborFinset _ _).mp (mem_inter.mp hx).1
              have wx := (G.mem_neighborFinset _ _).mp (mem_inter.mp hy).1
              exact tf ux.symm edge wx.symm
            have sub : X∪Y ⊆ A := union_subset (Finset.inter_subset_right) (Finset.inter_subset_right)
            have h := card_le_card sub
            rw [card_union_of_disjoint dXY] at h
            omega
          · exact ⟨w,wB,by omega⟩
        · exact ⟨u,uB,by omega⟩
      obtain ⟨b₀,hb₀,low⟩ := someLow
      have adeg (x : V) (hx : x ∈ A) : d ≤ G.degree x := by
        have xb : x ≠ b₀ := fun eq => disjoint_left.mp dis (eq ▸ hx) (mem_insert_of_mem hb₀)
        exact (high x b₀ xb).resolve_right (by omega)
      have onlyAB {x y : V} (xA : x∈A) (e : G.Adj x y) : y∈R := by
        rcases part y with ya|yr
        · exact (Aind xA ya e).elim
        · exact yr
      have bsize : B.card=d := by
        by_contra! q
        have Rsz : R.card≤d := by omega
        have sub : G.neighborFinset a ⊆ R :=
          fun y hy => onlyAB ha ((G.mem_neighborFinset _ _).mp hy)
        have little := card_le_card sub
        rw [card_neighborFinset_eq_degree] at little
        have eqN : G.neighborFinset a = R := eq_of_subset_of_card_le sub (by
          rw [card_neighborFinset_eq_degree]; omega)
        have ea : G.Adj a u := (G.mem_neighborFinset _ _).mp (eqN.symm ▸ mem_insert_of_mem uB)
        have eb : G.Adj a w := (G.mem_neighborFinset _ _).mp (eqN.symm ▸ mem_insert_of_mem wB)
        exact tf ea edge eb
      let H : SimpleGraph V :=
        { Adj := fun x y => G.Adj x y ∧ ((x∈A∧y∈R) ∨ (x∈R∧y∈A))
          symm := by
            intro x y e
            exact ⟨e.1.symm,e.2.elim (fun h => Or.inr h.symm) (fun h => Or.inl h.symm)⟩
          loopless := fun x e => G.loopless x e.1 }
      letI : DecidableRel H.Adj := fun x y => by
        change Decidable (G.Adj x y ∧ ((x∈A∧y∈R) ∨ (x∈R∧y∈A)))
        infer_instance
      have subH : H ≤ G := fun _ _ e => e.1
      have higher (x : V) (hx : x∈A) : d≤H.degree x := by
        have eq : H.neighborFinset x = G.neighborFinset x := by
          ext y
          rw [H.mem_neighborFinset,G.mem_neighborFinset]
          exact ⟨fun h => h.1,fun h => ⟨h,Or.inl ⟨hx,onlyAB hx h⟩⟩⟩
        rw [← card_neighborFinset_eq_degree,eq,card_neighborFinset_eq_degree]
        exact adeg x hx
      have rpos (x : V) (hx : x∈R) : 1≤H.degree x := by
        have lost : (G.neighborFinset x \ A).card ≤ 1 := by
          rcases mem_insert.mp hx with eq|b
          · have eqR : x=v := eq
            subst x
            have sub : G.neighborFinset v ⊆ A := fun y h =>
              mA.mpr ((G.mem_neighborFinset _ _).mp h)
            simp [Finset.sdiff_eq_empty_iff_subset.mpr sub]
          · exact outOne x b
        have inc : G.neighborFinset x ∩ A ⊆ H.neighborFinset x := by
          intro y hy
          obtain ⟨xy,yA⟩ := mem_inter.mp hy
          exact (H.mem_neighborFinset _ _).mpr ⟨(G.mem_neighborFinset _ _).mp xy,Or.inr ⟨hx,yA⟩⟩
        have card := card_le_card inc
        have eq := card_sdiff_add_card_inter (s:=G.neighborFinset x) (t:=A)
        rw [G.card_neighborFinset_eq_degree] at eq
        rw [H.card_neighborFinset_eq_degree] at card
        have min := mindeg x
        omega
      apply from_ordered H subH R A (fun v => (part v).symm) dis.symm
        (fun u v e => e.2.symm) (by omega) (by omega) (by omega)
      intro x hx y hy _
      have h1 := rpos x hx
      have h2 := higher y hy
      omega

/-- A 2-connected graph with at least three vertices has minimum degree two. -/
private theorem min_degree_two_of_two_connected {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 3 ≤ Fintype.card V)
    (conn : ∀ S : Finset V, S.card < 2 → (G.induce ((↑S : Set V)ᶜ)).Connected) :
    ∀ x, 2 ≤ G.degree x := by
  classical
  intro x
  by_cases hh : 2 ≤ G.degree x
  · exact hh
  exfalso
  let S := G.neighborFinset x
  have hx : x ∉ S := by simp [S]
  have hs : S.card < 2 := by
    rw [G.card_neighborFinset_eq_degree]
    omega
  have hlt : (insert x S).card < Fintype.card V := by
    rw [Finset.card_insert_of_not_mem hx]
    omega
  have hex : ∃ y : V, y ∉ insert x S := by
    by_contra h
    push_neg at h
    have he : insert x S = Finset.univ := Finset.eq_univ_iff_forall.mpr h
    rw [he,Finset.card_univ] at hlt
    omega
  obtain ⟨y,hy⟩ := hex
  have hxy : x ≠ y := by
    intro e; subst y
    exact hy (Finset.mem_insert_self _ _)
  let W := ((↑S : Set V)ᶜ)
  let u : W := ⟨x,hx⟩
  let v : W := ⟨y,fun h => hy (Finset.mem_insert_of_mem h)⟩
  have hhC := conn S hs
  obtain ⟨p,hp⟩ := hhC.exists_walk_length_eq_dist u v
  have huv : u ≠ v := fun h => hxy (congrArg (fun z : W => z.val) h)
  have hp' : 0 < p.length := hp ▸ hhC.pos_dist_of_ne huv
  have e := p.adj_getVert_succ (i:=0) hp'
  have hE : G.Adj x (p.getVert 1).val := by simpa [u] using e
  exact (p.getVert 1).prop ((G.mem_neighborFinset _ _).mpr hE)

theorem triangle_free_near_ore
    (hc : G.Connected)
    (conn : ∀ S : Finset V, S.card < 2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (tf : ∀ ⦃x y z : V⦄, G.Adj x y → G.Adj y z → ¬G.Adj x z)
    {d : ℕ} (hd : 3 ≤ d)
    (cap : ∀ x, (EvenFrom G x).card ≤ d + 1)
    (high : ∀ u v : V, u ≠ v → d ≤ G.degree u ∨ d ≤ G.degree v)
    (hn : 3 ≤ Fintype.card V) : Nonempty (NearOre G) := by
  classical
  have c : 1 < (Finset.univ : Finset V).card := by rw [Finset.card_univ]; omega
  obtain ⟨a,_,b,_,hne⟩ := Finset.one_lt_card.mp c
  have mindeg := min_degree_two_of_two_connected G hn conn
  rcases high a b hne with ha | hb
  · exact ore_at_high_root hc conn tf hd cap high mindeg a ha
  · exact ore_at_high_root hc conn tf hd cap high mindeg b hb

#print axioms triangle_free_near_ore
end Graffiti189TriangleOre
