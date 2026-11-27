import Reduction183
import OrderBridge

namespace Graffiti183.Exceptional
open SimpleGraph Finset

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

def ClawFree (G : SimpleGraph V) : Prop :=
  ∀ {c x y z : V}, G.Adj c x → G.Adj c y → G.Adj c z →
    x ≠ y → x ≠ z → y ≠ z → ¬ G.Adj x y → ¬ G.Adj x z → G.Adj y z

omit [Fintype V] in
private lemma adj_dist_le {x y : V} (h : G.Adj x y) : G.dist x y ≤ 1 := by
  simpa [SimpleGraph.Adj.toWalk] using G.dist_le h.toWalk

omit [Fintype V] in
private lemma two_step_le {x y z : V} (h : G.Adj x y) (g : G.Adj y z) :
    G.dist x z ≤ 2 :=
  (G.dist_le (SimpleGraph.Walk.cons h g.toWalk)).trans (by rfl)

omit [Fintype V] in
private lemma path_two (hc : G.Connected) {x y : V} (hd : G.dist x y = 2) :
    ∃ a, G.Adj x a ∧ G.Adj a y := by
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist x y
  rw [hd] at hp
  cases p with
  | nil => simp at hp
  | @cons _ a _ e p =>
    cases p with
    | nil => simp at hp
    | cons f p =>
      cases p with
      | nil => exact ⟨a,e,f⟩
      | cons _ _ => simp only [Walk.length_cons] at hp; omega

omit [Fintype V] in
private lemma path_three (hc : G.Connected) {x y : V} (hd : G.dist x y = 3) :
    ∃ a q, G.Adj x a ∧ G.Adj a q ∧ G.Adj q y := by
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist x y
  rw [hd] at hp
  cases p with
  | nil => simp at hp
  | @cons _ a _ e p =>
    cases p with
    | nil => simp at hp
    | @cons _ q _ f p =>
      cases p with
      | nil => simp at hp
      | cons g p =>
        cases p with
        | nil => exact ⟨a,q,e,f,g⟩
        | cons _ _ => simp only [Walk.length_cons] at hp; omega

lemma exists_distance_three_of_radius (hr : 3 ≤ radius G) (x : V) :
    ∃ p, 2 < G.dist x p := by
  have H : radius G ≤ eccentricity G x := csInf_le (OrderBot.bddBelow _) ⟨x,rfl⟩
  obtain ⟨p,_,hp⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset V) ⟨x,mem_univ x⟩ (G.dist x)
  change eccentricity G x = G.dist x p at hp
  exact ⟨p,by omega⟩

/-- The six distinguished vertices are distinct. The displayed consecutive edges form
an induced six-vertex path, with the only additional possible edge joining its ends. -/
structure SixPattern (G : SimpleGraph V) (v w : V) where
  a : V
  q : V
  b : V
  p : V
  dist_vp : G.dist v p = 2
  far_ap : 2 < G.dist a p
  apart_vw : v ≠ w
  e_va : G.Adj v a
  e_aq : G.Adj a q
  e_qw : G.Adj q w
  e_vb : G.Adj v b
  e_bp : G.Adj b p
  n_vq : ¬G.Adj v q
  n_vp : ¬G.Adj v p
  n_vw : ¬G.Adj v w
  n_aw : ¬G.Adj a w
  n_ab : ¬G.Adj a b
  n_ap : ¬G.Adj a p
  n_qb : ¬G.Adj q b
  n_qp : ¬G.Adj q p
  n_wb : ¬G.Adj w b
  all_distinct : [w,q,a,v,b,p].Nodup

theorem exists_six_pattern (hc : G.Connected) (hclaw : ClawFree G)
    (hr : 3 ≤ radius G) {v w : V} (hd : G.dist v w = 3)
    (hunique : ∀ z, 2 < G.dist v z ↔ z = w) :
    Nonempty (SixPattern G v w) := by
  obtain ⟨a,q,hva,haq,hqw⟩ := path_three hc hd
  obtain ⟨p,hap⟩ := exists_distance_three_of_radius hr a
  have hwp : w ≠ p := by
    intro e
    subst p
    have ht := two_step_le haq hqw
    omega
  have hvp : v ≠ p := by
    intro e
    subst p
    have h := adj_dist_le hva.symm
    omega
  have hp2 : G.dist v p = 2 := by
    have hu : G.dist v p ≤ 2 := by
      by_contra! h
      exact hwp ((hunique p).mp h).symm
    have hn : G.dist v p ≠ 0 := fun h => hvp (hc.dist_eq_zero_iff.mp h)
    have hn1 : G.dist v p ≠ 1 := by
      intro h
      have he := dist_eq_one_iff_adj.mp h
      have ht := two_step_le hva.symm he
      omega
    omega
  obtain ⟨b,hvb,hbp⟩ := path_two hc hp2
  have hvw : v ≠ w := by intro e; subst w; simp [SimpleGraph.dist_self] at hd
  have hvq' : ¬G.Adj v q := by
    intro e
    have hh := two_step_le e hqw
    omega
  have hvw' : ¬G.Adj v w := by intro e; have hh := adj_dist_le e; omega
  have hvp' : ¬G.Adj v p := by intro e; have hh := adj_dist_le e; omega
  have haw' : ¬G.Adj a w := by
    intro e
    have hh := two_step_le hva e
    omega
  have hab' : ¬G.Adj a b := by
    intro e
    have hh := two_step_le e hbp
    omega
  have hap' : ¬G.Adj a p := by intro e; have hh := adj_dist_le e; omega
  have hqp' : ¬G.Adj q p := by
    intro e
    have hh := two_step_le haq e
    omega
  have hwb' : ¬G.Adj w b := by
    intro e
    have hh := two_step_le hvb e.symm
    omega
  have hab : a ≠ b := by
    intro e
    subst b
    exact hap' hbp
  have haw : a ≠ w := by
    intro e
    subst w
    exact hvw' hva
  have hbw : b ≠ w := by
    intro e
    subst w
    exact hvw' hvb
  have hqb' : ¬G.Adj q b := by
    intro e
    exact hwb' (hclaw haq.symm e hqw hab haw hbw hab' haw').symm
  have hvq : v ≠ q := by
    intro e
    subst q
    exact hvw' hqw
  have hpa : p ≠ a := by
    intro e
    subst p
    simp [SimpleGraph.dist_self] at hap
  have hpq : p ≠ q := by
    intro e
    subst p
    exact hap' haq
  have hqb : q ≠ b := by
    intro e
    subst b
    exact hvq' hvb
  refine ⟨⟨a,q,b,p,hp2,hap,hvw,hva,haq,hqw,hvb,hbp,
    hvq',hvp',hvw',haw',hab',hap',hqb',hqp',hwb',?_⟩⟩
  simp [List.nodup_cons,hvw.symm,hwp,hqw.ne.symm,haw.symm,hbw.symm,
    haq.ne.symm,hvq.symm,hqb,hpq.symm,hva.ne.symm,hab,hpa.symm,hvb.ne,hvp,hbp.ne]

#print axioms exists_six_pattern
end Graffiti183.Exceptional
