/- Lean 4.19.0 / Mathlib v4.19.0: run lake env lean Exact235.lean. -/

import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lean.Elab.Tactic.Omega
set_option warningAsError true
set_option linter.unusedSectionVars false
open Finset
namespace Graffiti235
variable {V : Type*} [Fintype V] [Nonempty V]
variable (G : SimpleGraph V)

def TotalDominates (D : Finset V) : Prop :=
  ∀ v, ∃ w ∈ D, G.Adj v w

noncomputable def totalDomination : Nat :=
  sInf {k | ∃ D : Finset V, TotalDominates G D ∧ D.card = k}

def Bicoloring (G : SimpleGraph V) (p : V → Bool) : Prop :=
  ∀ u v, G.Adj u v → p u ≠ p v

def Bipartite (G : SimpleGraph V) : Prop := ∃ p, Bicoloring G p

noncomputable def ecc (v : V) : Nat := Finset.univ.sup (G.dist v)
noncomputable def diameter : Nat := Finset.univ.sup (ecc G)
noncomputable def periphery : Finset V := by
  classical exact Finset.univ.filter (fun v => ecc G v = diameter G)

theorem ecc_le_diam (v : V) : ecc G v ≤ diameter G := Finset.le_sup (Finset.mem_univ _)
theorem dist_le_ecc (u v : V) : G.dist u v ≤ ecc G u := Finset.le_sup (Finset.mem_univ _)

theorem diameterPair : ∃ a b, a ∈ periphery G ∧ b ∈ periphery G ∧
    G.dist a b = diameter G := by
  classical
  obtain ⟨a,_,ha⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty (ecc G)
  obtain ⟨b,_,hb⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty (G.dist a)
  have he := hb.symm.trans ha.symm
  have hbe := dist_le_ecc G b a
  rw [SimpleGraph.dist_comm,he] at hbe
  exact ⟨a,b,by simpa [periphery] using ha.symm,
    by simpa [periphery] using Nat.le_antisymm (ecc_le_diam G b) hbe,he⟩

theorem periphery_nonempty : (periphery G).Nonempty := by
  obtain ⟨a,_,ha,_,_⟩ := diameterPair G
  exact ⟨a,ha⟩

noncomputable def dPeriphery (x : V) : Nat :=
  (periphery G).inf' (periphery_nonempty G) (G.dist x)

noncomputable def eccPeriphery : Nat := Finset.univ.sup (dPeriphery G)

theorem dPeriphery_le (x b : V) (h : b ∈ periphery G) :
    dPeriphery G x ≤ G.dist x b :=
  Finset.inf'_le _ h

theorem dPeriphery_attains : ∃ x, dPeriphery G x = eccPeriphery G := by
  obtain ⟨x,_,hx⟩ :=
    Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty (dPeriphery G)
  exact ⟨x,hx.symm⟩

theorem dPeriphery_eq_zero {x : V} (h : x ∈ periphery G) : dPeriphery G x = 0 := by
  have hm := dPeriphery_le G x x h
  simpa [SimpleGraph.dist_self] using hm

noncomputable def tri (a b c : V) : Nat := G.dist a b + G.dist b c + G.dist c a

theorem close_rep (D : Finset V) (h : TotalDominates G D) :
    ∃ f : V → V, (∀ v, f v ∈ D) ∧ (∀ v, G.dist v (f v) ≤ 1) ∧
      ∀ v, v ∈ D → f v = v := by
  classical
  let f : V → V := fun v => if v ∈ D then v else Classical.choose (h v)
  refine ⟨f,?_,?_,?_⟩
  · intro v
    by_cases he : v ∈ D
    · simp [f,he]
    · simpa [f,he] using (Classical.choose_spec (h v)).1
  · intro v
    by_cases he : v ∈ D
    · simp [f,he,SimpleGraph.dist_self]
    · have ad := (Classical.choose_spec (h v)).2
      have eq := SimpleGraph.dist_eq_one_iff_adj.mpr ad
      simp [f,he,eq]
  · intro v hv
    simp [f,hv]

theorem walk_cross (S : V → Prop) {a b : V} (p : G.Walk a b)
    (aIn : S a) (bOut : ¬ S b) :
    ∃ x y, S x ∧ ¬ S y ∧ G.Adj x y := by
  classical
  induction p with
  | nil => exact False.elim (bOut aIn)
  | @cons _ y _ h _ ih =>
    by_cases hy : S y
    · exact ih hy bOut
    · exact ⟨_,_,aIn,hy,h⟩

theorem distVia (hc : G.Connected) (a x y b : V) :
    G.dist a b ≤ G.dist a x + G.dist x y + G.dist y b := by
  have h₁ := hc.dist_triangle (u := a) (v := y) (w := b)
  have h₂ := hc.dist_triangle (u := a) (v := x) (w := y)
  omega

theorem distTriReplace (hc : G.Connected) (a b c a' b' c' : V) :
    tri G a b c ≤ tri G a' b' c' +
      2*(G.dist a a' + G.dist b b' + G.dist c c') := by
  have h₁ := distVia G hc a a' b' b
  have h₂ := distVia G hc b b' c' c
  have h₃ := distVia G hc c c' a' a
  rw [SimpleGraph.dist_comm (u := b') (v := b)] at h₁
  rw [SimpleGraph.dist_comm (u := c') (v := c)] at h₂
  rw [SimpleGraph.dist_comm (u := a') (v := a)] at h₃
  unfold tri
  omega

theorem triInsert (hc : G.Connected) {S : Finset V} {v w : V}
    [DecidableEq V] (hw : w ∈ S) (hD : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, tri G a b c ≤ k) :
    ∀ a ∈ insert v S, ∀ b ∈ insert v S, ∀ c ∈ insert v S,
      tri G a b c ≤ k + 2*G.dist v w := by
  intro a ha b hb c hc'
  rw [Finset.mem_insert] at ha hb hc'
  rcases ha with ha|ha <;> rcases hb with hb|hb <;> rcases hc' with hc'|hc'
  all_goals try subst a
  all_goals try subst b
  all_goals try subst c
  · simp [tri,SimpleGraph.dist_self]
  · have hp := hD w hw w hw c hc'
    have h := hc.dist_triangle (u := v) (v := w) (w := c)
    unfold tri
    rw [SimpleGraph.dist_comm (u := c) (v := v), SimpleGraph.dist_self] 
    have h' : G.dist c w = G.dist w c := SimpleGraph.dist_comm
    simp [tri,h',SimpleGraph.dist_self] at hp
    omega
  · have hp := hD w hw b hb w hw
    have h := hc.dist_triangle (u := v) (v := w) (w := b)
    unfold tri
    rw [SimpleGraph.dist_comm (u := b) (v := v), SimpleGraph.dist_self]
    have h' : G.dist b w = G.dist w b := SimpleGraph.dist_comm
    simp [tri,h',SimpleGraph.dist_self] at hp
    omega
  · have hp := hD w hw b hb c hc'
    have h := distTriReplace G hc v b c w b c
    simp [SimpleGraph.dist_self] at h
    omega
  · have hp := hD a ha w hw w hw
    have h := hc.dist_triangle (u := v) (v := w) (w := a)
    unfold tri
    rw [SimpleGraph.dist_comm (u := a) (v := v), SimpleGraph.dist_self]
    have h' : G.dist a w = G.dist w a := SimpleGraph.dist_comm
    simp [tri,h',SimpleGraph.dist_self] at hp
    omega
  · have hp := hD a ha w hw c hc'
    have h := distTriReplace G hc a v c a w c
    simp [SimpleGraph.dist_self] at h
    omega
  · have hp := hD a ha b hb w hw
    have h := distTriReplace G hc a b v a b w
    simp [SimpleGraph.dist_self] at h
    omega
  · have := hD a ha b hb c hc'
    omega

theorem tripleFromDom (hc : G.Connected) (D : Finset V) (hD : TotalDominates G D) :
    2 ≤ D.card ∧ ∀ a b c, tri G a b c ≤ 4*D.card := by
  classical
  obtain ⟨f,fD,fMetric,fFix⟩ := close_rep G D hD
  let d0 := f (Classical.choice (inferInstance : Nonempty V))
  have hd0 : d0 ∈ D := fD _
  obtain ⟨d1,hd1,he⟩ := hD d0
  let S0 : Finset V := {d0,d1}
  have S0D : S0 ⊆ D := by
    intro v hv
    rcases (Finset.mem_insert.mp hv) with hv|hv
    · simpa [hv] using hd0
    · have hv' := Finset.mem_singleton.mp hv
      simpa [hv'] using hd1
  have S0card : S0.card = 2 := Finset.card_pair he.ne
  have hcard : 2 ≤ D.card := S0card ▸ Finset.card_le_card S0D
  refine ⟨hcard,?_⟩
  have grow (j : Nat) : ∀ (S : Finset V),
      S ⊆ D → 2 ≤ S.card →
      (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, tri G a b c ≤ 4*S.card-6) →
      D.card-S.card=j → ∀ a ∈ D, ∀ b ∈ D, ∀ c ∈ D, tri G a b c ≤ 4*D.card-6 := by
    induction j using Nat.strongRecOn with
    | ind j ih =>
      intro S hSD hScard htri hj
      by_cases hs : S = D
      · subst S; exact htri
      by_cases hEdge : ∃ w ∈ S, ∃ v ∈ D, v ∉ S ∧ G.Adj v w
      · obtain ⟨w,hw,v,hv,hnv,had⟩ := hEdge
        let Q := insert v S
        have hQ : Q ⊆ D := Finset.insert_subset_iff.mpr ⟨hv,hSD⟩
        have hQc : Q.card = S.card+1 := Finset.card_insert_of_not_mem hnv
        have hsub : D.card-Q.card < j := by
          have hcd := Finset.card_le_card hQ
          omega
        refine ih _ hsub Q hQ (by omega) ?_ rfl
        intro a ha b hb c hc'
        have hh := triInsert G hc hw htri a ha b hb c hc'
        have h₁ := SimpleGraph.dist_eq_one_iff_adj.mpr had
        omega
      · have hne : ∃ v ∈ D, v ∉ S := by
          by_contra! h
          exact hs (Finset.Subset.antisymm hSD h)
        obtain ⟨v,hv,hnv⟩ := hne
        have h0 : S.Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨w,hw⟩ := h0
        obtain ⟨p,_⟩ := hc.exists_walk_length_eq_dist w v
        have hws : f w ∈ S := by simpa [fFix w (hSD hw)] using hw
        have hvs : f v ∉ S := by simpa [fFix v hv] using hnv
        obtain ⟨x,y,hx,hy,had⟩ := walk_cross G (fun x => f x ∈ S) p hws hvs
        let a := f x
        let b := f y
        have haS : a ∈ S := hx
        have hbS : b ∉ S := hy
        have hbD : b ∈ D := fD _
        have hdist : G.dist b a ≤ 3 := by
          have hxy := SimpleGraph.dist_eq_one_iff_adj.mpr had.symm
          have huu := fMetric y
          have hvv := fMetric x
          have h₀ := distVia G hc b y x a
          rw [SimpleGraph.dist_comm (u := b) (v := y)] at h₀
          change G.dist y b ≤ 1 at huu
          change G.dist x a ≤ 1 at hvv
          omega
        obtain ⟨z,hz,hez⟩ := hD b
        have hnz : z ∉ S := fun zz => hEdge ⟨z,zz,b,hbD,hbS,hez⟩
        have nzb : z ≠ b := hez.ne.symm
        let Q := insert b S
        let R := insert z Q
        have hQ : Q ⊆ D := Finset.insert_subset_iff.mpr ⟨hbD,hSD⟩
        have hR : R ⊆ D := Finset.insert_subset_iff.mpr ⟨hz,hQ⟩
        have hQc : Q.card = S.card+1 := Finset.card_insert_of_not_mem hbS
        have hzQ : z ∉ Q := by simp [Q,nzb,hnz]
        have hRc : R.card = Q.card+1 := Finset.card_insert_of_not_mem hzQ
        have hsub : D.card-R.card < j := by
          have hcd := Finset.card_le_card hR
          omega
        have hq : ∀ a' ∈ Q, ∀ b' ∈ Q, ∀ c' ∈ Q, tri G a' b' c' ≤ (4*S.card-6)+6 := by
          intro a' h₁ b' h₂ c' h₃
          have inequ := triInsert G hc haS htri a' h₁ b' h₂ c' h₃
          omega
        refine ih _ hsub R hR (by omega) ?_ rfl
        intro a' h₁ b' h₂ c' h₃
        have hh := triInsert G hc (Finset.mem_insert_self _ _) hq a' h₁ b' h₂ c' h₃
        have h₁' := SimpleGraph.dist_eq_one_iff_adj.mpr hez.symm
        omega
  have start : ∀ a ∈ S0, ∀ b ∈ S0, ∀ c ∈ S0, tri G a b c ≤ 4*S0.card-6 := by
    intro a ha b hb c hc'
    have e01 := SimpleGraph.dist_eq_one_iff_adj.mpr he
    have e10 := SimpleGraph.dist_eq_one_iff_adj.mpr he.symm
    simp only [S0, Finset.mem_insert, Finset.mem_singleton] at ha hb hc'
    rcases ha with ha|ha <;> rcases hb with hb|hb <;> rcases hc' with hc'|hc' <;>
      simp [tri,ha,hb,hc',S0card,e01,e10,SimpleGraph.dist_self]
  intro a b c
  have hout := grow _ S0 S0D (by omega) start rfl (f a) (fD _) (f b) (fD _) (f c) (fD _)
  have h1 := fMetric a
  have h2 := fMetric b
  have h3 := fMetric c
  have hh := distTriReplace G hc a b c (f a) (f b) (f c)
  omega

theorem sixDomOfFar (hc : G.Connected) (D : Finset V) (hD : TotalDominates G D)
    (a b c : V)
    (ab : 3 ≤ G.dist a b) (bc : 3 ≤ G.dist b c) (ca : 3 ≤ G.dist c a)
    (ha : a ∈ D) (hb : b ∈ D) (hc' : c ∈ D) : 6 ≤ D.card := by
  classical
  obtain ⟨a',ha',ea⟩ := hD a
  obtain ⟨b',hb',eb⟩ := hD b
  obtain ⟨c',hc'',ec⟩ := hD c
  have nearNot {x y z : V} (d : 3 ≤ G.dist x y) (h : G.Adj x z) : z ≠ y := by
    intro e
    subst z
    have h' := SimpleGraph.dist_eq_one_iff_adj.mpr h
    omega
  have farNe {x y : V} (d : 3 ≤ G.dist x y) : x ≠ y := by
    intro e
    simp [e,SimpleGraph.dist_self] at d
  have nearDiff {x y u v : V} (d : 3 ≤ G.dist x y) (hx : G.Adj x u) (hy : G.Adj y v) :
      u ≠ v := by
    intro e
    subst v
    have h₁ := hc.dist_triangle (u := x) (v := u) (w := y)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hx,SimpleGraph.dist_eq_one_iff_adj.mpr hy.symm] at h₁
    omega
  have ba : 3 ≤ G.dist b a := by rwa [SimpleGraph.dist_comm]
  have cb : 3 ≤ G.dist c b := by rwa [SimpleGraph.dist_comm]
  have ac : 3 ≤ G.dist a c := by rwa [SimpleGraph.dist_comm]
  have hcard : (insert a (insert b (insert c (insert a' ({b',c'} : Finset V))))).card = 6 := by
    have h1 : a ∉ (insert b (insert c (insert a' ({b',c'} : Finset V)))) := by
      simp [farNe ab,farNe ac,ea.ne,(nearNot ba eb).symm,(nearNot ca ec).symm]
    have h2 : b ∉ (insert c (insert a' ({b',c'} : Finset V))) := by
      simp [farNe bc,(nearNot ab ea).symm,eb.ne,(nearNot cb ec).symm]
    have h3 : c ∉ (insert a' ({b',c'} : Finset V)) := by
      simp [(nearNot ac ea).symm,(nearNot bc eb).symm,ec.ne]
    have h4 : a' ∉ ({b',c'} : Finset V) := by
      simp [nearDiff ab ea eb,nearDiff ac ea ec]
    rw [Finset.card_insert_of_not_mem h1,Finset.card_insert_of_not_mem h2,
      Finset.card_insert_of_not_mem h3, Finset.card_insert_of_not_mem h4,
      Finset.card_pair (nearDiff bc eb ec)]
  have hsubset : (insert a (insert b (insert c (insert a' ({b',c'} : Finset V))))) ⊆ D := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨ha,hb,hc',ha',hb',hc''⟩
  exact hcard ▸ Finset.card_le_card hsubset


theorem peripheryLower (hc : G.Connected) (D : Finset V) (hD : TotalDominates G D) :
    2 ≤ D.card ∧
    (0 < eccPeriphery G → 3*eccPeriphery G+1 ≤ 4*D.card) ∧
    (5 ≤ eccPeriphery G → 6 ≤ D.card) := by
  classical
  obtain ⟨ht,htri⟩ := tripleFromDom G hc D hD
  refine ⟨ht,?_⟩
  obtain ⟨a,b,ha,hb,ab⟩ := diameterPair G
  obtain ⟨z,hz⟩ := dPeriphery_attains G
  have za : eccPeriphery G ≤ G.dist z a := hz ▸ dPeriphery_le G z a ha
  have zb : eccPeriphery G ≤ G.dist z b := hz ▸ dPeriphery_le G z b hb
  have az : eccPeriphery G ≤ G.dist a z := by rwa [SimpleGraph.dist_comm]
  have bz : eccPeriphery G ≤ G.dist b z := by rwa [SimpleGraph.dist_comm]
  have abpos (h : 0 < eccPeriphery G) : eccPeriphery G < G.dist a b := by
    have hn : z ∉ periphery G := by
      intro hzB
      have he := dPeriphery_eq_zero G hzB
      omega
    have hneq : ecc G z ≠ diameter G := by
      intro he
      exact hn (by simp [periphery,he])
    have hzle := ecc_le_diam G z
    have hzal := dist_le_ecc G z a
    omega
  constructor
  · intro he
    have tt := htri a b z
    have hab := abpos he
    unfold tri at tt
    omega
  · intro he
    obtain ⟨f,fD,fMetric,_⟩ := close_rep G D hD
    have fromNear (x y : V) (far : eccPeriphery G ≤ G.dist x y) :
        3 ≤ G.dist (f x) (f y) := by
      have h₀ := distVia G hc x (f x) (f y) y
      rw [SimpleGraph.dist_comm (u := f y) (v := y)] at h₀
      have h₁ := fMetric x
      have h₂ := fMetric y
      omega
    have hab : eccPeriphery G ≤ G.dist a b := Nat.le_of_lt (abpos (by omega))
    exact sixDomOfFar G hc D hD (f a) (f b) (f z)
      (fromNear a b hab) (fromNear b z bz) (fromNear z a za) (fD _) (fD _) (fD _)

/-- An elementary numeric consequence of the graph-theoretic lemmas. -/
theorem arith (t e : Nat) (ht : 2 ≤ t)
    (htb : 0 < e → 3*e+1 ≤ 4*t)
    (hs : 5 ≤ e → 6 ≤ t) (her : t = 2 → e ≤ 1) : 2*e+3 ≤ 3*t := by
  by_cases hp : e = 0
  · omega
  have hb := htb (by omega)
  by_cases he : 5 ≤ e
  · have hs' := hs he
    omega
  by_cases h : t = 2
  · have hh := her h
    omega
  by_cases ht4 : 4 ≤ t
  · omega
  · have ht3 : t=3 := by omega
    omega

/-- Compile-time interface to the small bipartite case, discharged separately. -/
def PeripheralNearAll (G : SimpleGraph V) : Prop :=
  ∀ z : V, ∃ b : V, G.dist z b ≤ 1 ∧
    ∃ w : V, ∀ u v : V, G.dist u v ≤ G.dist b w

theorem nearbyPeriphery (h : PeripheralNearAll G) : eccPeriphery G ≤ 1 := by
  obtain ⟨z,hz⟩ := dPeriphery_attains G
  obtain ⟨b,hzb,w,hmax⟩ := h z
  have hwd := dist_le_ecc G b w
  have hbd : diameter G ≤ G.dist b w := by
    apply Finset.sup_le
    intro u _
    apply Finset.sup_le
    intro v _
    exact hmax u v
  have hh := ecc_le_diam G b
  have hb : b ∈ periphery G := by
    classical
    have he : ecc G b = diameter G := by omega
    simp [periphery,he]
  have hbell := dPeriphery_le G z b hb
  omega

theorem dominationAttained (hc : G.Connected) (hn : 1 < Fintype.card V) :
    ∃ D : Finset V, TotalDominates G D ∧ D.card = totalDomination G := by
  classical
  have hD : TotalDominates G Finset.univ := by
    intro v
    obtain ⟨w,hw⟩ := Fintype.exists_ne_of_one_lt_card hn v
    obtain ⟨p,_⟩ := hc.exists_walk_length_eq_dist v w
    cases p with
    | nil => exact False.elim (hw rfl)
    | @cons _ x _ he _ => exact ⟨x,Finset.mem_univ _,he⟩
  have hne : ({k : Nat | ∃ D : Finset V, TotalDominates G D ∧ D.card = k}).Nonempty :=
    ⟨_,_,hD,rfl⟩
  exact Nat.sInf_mem hne

noncomputable def bipBonus : Nat := by
  classical exact if Bipartite G then 1 else 0

theorem main_of_small (hc : G.Connected) (hn : 1 < Fintype.card V)
    (hSmall : ∀ (x y : V), x ≠ y → (∀ v, G.Adj v x ∨ G.Adj v y) →
      ∀ p : V → Bool, Bicoloring G p → PeripheralNearAll G) :
    2*eccPeriphery G + 3*bipBonus G ≤ 3*totalDomination G := by
  classical
  obtain ⟨D,hD,hDeq⟩ := dominationAttained G hc hn
  rw [← hDeq]
  obtain ⟨ht,hlarge,hSix⟩ := peripheryLower G hc D hD
  unfold bipBonus
  split
  next hb =>
    obtain ⟨p,hp⟩ := hb
    simp only [Nat.mul_one]
    apply arith _ _ ht hlarge hSix
    intro hd2
    obtain ⟨x,y,hxy,hpair⟩ := Finset.card_eq_two.mp hd2
    have hDN (z : V) : G.Adj z x ∨ G.Adj z y := by
      obtain ⟨w,hw,e⟩ := hD z
      rw [hpair,Finset.mem_insert,Finset.mem_singleton] at hw
      rcases hw with eq|eq
      · exact Or.inl (eq ▸ e)
      · exact Or.inr (eq ▸ e)
    exact nearbyPeriphery G (hSmall x y hxy hDN p hp)
  next _ =>
    have h : 2*eccPeriphery G ≤ 3*D.card := by
      by_cases e : eccPeriphery G = 0
      · omega
      · have hp := hlarge (by omega)
        omega
    simpa using h

theorem bipartiteTwo (G : SimpleGraph V) (hc : G.Connected) (x y : V)
    (_hxy : x ≠ y) (hd : ∀ v, G.Adj v x ∨ G.Adj v y) (p : V → Bool)
    (hp : ∀ u v, G.Adj u v → p u ≠ p v) :
    ∀ z, ∃ b : V, G.dist z b ≤ 1 ∧ ∃ w : V, ∀ u v : V, G.dist u v ≤ G.dist b w := by
  classical
  have edge : G.Adj x y := (hd x).resolve_left (G.loopless _)
  have colors : p x ≠ p y := hp _ _ edge
  have different (u v : V) (h : p u ≠ p v) : u ≠ v := fun e => h (congrArg p e)
  have hubY (v : V) (h : p v = p x) : G.Adj v y :=
    (hd v).resolve_left (fun e => hp _ _ e h)
  have hubX (v : V) (h : p v ≠ p x) : G.Adj v x := by
    apply (hd v).resolve_right
    intro he
    have h1 := hp _ _ he
    cases h1v : p v <;> cases hx : p x <;> cases hy : p y <;> simp_all
  have weakSame (u v : V) (h : p u = p v) : G.dist u v ≤ 2 := by
    by_cases hu : p u = p x
    · have h1 := SimpleGraph.dist_eq_one_iff_adj.mpr (hubY u hu)
      have h2 := SimpleGraph.dist_eq_one_iff_adj.mpr (hubY v (h.symm.trans hu)).symm
      have he := hc.dist_triangle (u:=u) (v:=y) (w:=v)
      omega
    · have hv : p v ≠ p x := fun he => hu (h.trans he)
      have h1 := SimpleGraph.dist_eq_one_iff_adj.mpr (hubX u hu)
      have h2 := SimpleGraph.dist_eq_one_iff_adj.mpr (hubX v hv).symm
      have he := hc.dist_triangle (u:=u) (v:=x) (w:=v)
      omega
  have strongSame (u v : V) (h : p u = p v) (hne : u ≠ v) : G.dist u v = 2 := by
    have hlo := hc.one_lt_dist_of_ne_of_not_adj hne (fun e => hp _ _ e h)
    have hhi := weakSame u v h
    omega
  have weakAll (u v : V) : G.dist u v ≤ 3 := by
    by_cases he : p u = p v
    · have := weakSame u v he
      omega
    · by_cases hu : p u = p x
      · have hv : p v ≠ p x := fun hh => he (hu.trans hh.symm)
        have h1 := SimpleGraph.dist_eq_one_iff_adj.mpr (hubY u hu)
        have h2 := SimpleGraph.dist_eq_one_iff_adj.mpr edge.symm
        have h3 := SimpleGraph.dist_eq_one_iff_adj.mpr (hubX v hv).symm
        have ha := hc.dist_triangle (u:=u) (v:=y) (w:=v)
        have hb := hc.dist_triangle (u:=y) (v:=x) (w:=v)
        omega
      · have hv : p v = p x := by
          cases ex : p x <;> cases eu : p u <;> cases ev : p v <;> simp_all
        have h1 := SimpleGraph.dist_eq_one_iff_adj.mpr (hubX u hu)
        have h2 := SimpleGraph.dist_eq_one_iff_adj.mpr edge
        have h3 := SimpleGraph.dist_eq_one_iff_adj.mpr (hubY v hv).symm
        have ha := hc.dist_triangle (u:=u) (v:=x) (w:=v)
        have hb := hc.dist_triangle (u:=x) (v:=y) (w:=v)
        omega
  have pathEven2 : ∀ {u v}, (w : G.Walk u v) → w.length = 2 → p u = p v := by
    intro u v w hw
    cases w with
    | nil => simp at hw
    | @cons u mid v em r =>
      cases r with
      | nil => simp at hw
      | @cons mid mid' v em' r' =>
        cases r' with
        | nil =>
          have h1 := hp _ _ em
          have h2 := hp _ _ em'
          cases e1 : p u <;> cases e2 : p mid <;> cases e3 : p v <;> simp_all
        | cons e tail =>
          simp only [SimpleGraph.Walk.length_cons] at hw
          omega
  have missing (u v : V) (he : p u ≠ p v) (hn : ¬ G.Adj u v) : G.dist u v = 3 := by
    have l := hc.one_lt_dist_of_ne_of_not_adj (different u v he) hn
    have h := weakAll u v
    by_cases h2 : G.dist u v = 2
    · obtain ⟨w,hw⟩ := hc.exists_walk_length_eq_dist u v
      exact (he (pathEven2 w (hw.trans h2))).elim
    · omega
  intro z
  by_cases hnon : ∃ a b, p a ≠ p b ∧ ¬ G.Adj a b
  · obtain ⟨a,b,hab,hn⟩ := hnon
    by_cases hz : ∃ w, p z ≠ p w ∧ ¬ G.Adj z w
    · obtain ⟨w,hw,hnw⟩ := hz
      refine ⟨z,by rw [SimpleGraph.dist_self]; decide,w,?_⟩
      rw [missing z w hw hnw]
      exact weakAll
    · have hz' (u : V) (hu : p z ≠ p u) : G.Adj z u := by
        exact Classical.byContradiction (fun h => hz ⟨u,hu,h⟩)
      by_cases ha : p z = p a
      · have hzb : G.Adj z b := hz' b (fun h => hab (ha.symm.trans h))
        refine ⟨b,by rw [SimpleGraph.dist_eq_one_iff_adj.mpr hzb],a,?_⟩
        rw [SimpleGraph.dist_comm (G:=G) (u:=b) (v:=a),missing a b hab hn]
        exact weakAll
      · have hza := hz' a ha
        refine ⟨a,by rw [SimpleGraph.dist_eq_one_iff_adj.mpr hza],b,?_⟩
        rw [missing a b hab hn]
        exact weakAll
  · have adjCross (u v : V) (h : p u ≠ p v) : G.Adj u v :=
      Classical.byContradiction (fun e => hnon ⟨u,v,h,e⟩)
    have upper2 (u v : V) : G.dist u v ≤ 2 := by
      by_cases he : p u = p v
      · exact weakSame u v he
      · rw [SimpleGraph.dist_eq_one_iff_adj.mpr (adjCross u v he)]
        decide
    by_cases hz : ∃ w, p z = p w ∧ z ≠ w
    · obtain ⟨w,hw,hnw⟩ := hz
      refine ⟨z,by rw [SimpleGraph.dist_self]; decide,w,?_⟩
      rw [strongSame z w hw hnw]
      exact upper2
    · have opp : ∃ a, p z ≠ p a := by
        by_cases hh : p z = p x
        · exact ⟨y,fun e => colors (hh.symm.trans e)⟩
        · exact ⟨x,hh⟩
      obtain ⟨a,hza⟩ := opp
      have eza := adjCross z a hza
      by_cases ha : ∃ w, p a = p w ∧ a ≠ w
      · obtain ⟨w,hw,hnw⟩ := ha
        refine ⟨a,by rw [SimpleGraph.dist_eq_one_iff_adj.mpr eza],w,?_⟩
        rw [strongSame a w hw hnw]
        exact upper2
      · refine ⟨z,by rw [SimpleGraph.dist_self]; decide,a,?_⟩
        rw [SimpleGraph.dist_eq_one_iff_adj.mpr eza]
        intro u v
        by_cases he : p u = p v
        · by_cases hz' : p z = p u
          · have h1 : z = u := Classical.byContradiction (fun e => hz ⟨u,hz',e⟩)
            have h2 : z = v := Classical.byContradiction (fun e => hz ⟨v,hz'.trans he,e⟩)
            rw [← h1,← h2,SimpleGraph.dist_self]
            decide
          · have hh : p a = p u := by
              cases pz : p z <;> cases pa : p a <;> cases pu : p u <;> simp_all
            have h1 : a = u := Classical.byContradiction (fun e => ha ⟨u,hh,e⟩)
            have h2 : a = v := Classical.byContradiction (fun e => ha ⟨v,hh.trans he,e⟩)
            rw [← h1,← h2,SimpleGraph.dist_self]
            decide
        · rw [SimpleGraph.dist_eq_one_iff_adj.mpr (adjCross u v he)]


/-- The exact Graffiti.pc #235, with denominators cleared. -/
theorem conjecture235 (hc : G.Connected) (hn : 1 < Fintype.card V) :
    2*eccPeriphery G + 3*bipBonus G ≤ 3*totalDomination G :=
  main_of_small G hc hn (fun x y hxy hd p hp => bipartiteTwo G hc x y hxy hd p hp)

#print axioms conjecture235
end Graffiti235
