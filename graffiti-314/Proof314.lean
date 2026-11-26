import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Nat.Lattice
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

/-!
Written on the Wall II #314. The catalogue credits the earlier proof by
Charlie Chitty and Ciarann Landers. This verification uses the absence
of an induced two-edge matching and the structure around a 5-cycle.
-/

namespace Graffiti314
open Finset SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

def TotalDominates (D : Finset V) : Prop := ∀ v, ∃ w ∈ D, G.Adj v w

def MinimalTotalDominates (D : Finset V) : Prop :=
  TotalDominates G D ∧ ∀ E : Finset V, E ⊂ D → ¬TotalDominates G E

def WellTotalDominated : Prop :=
  ∀ D, MinimalTotalDominates G D → ∀ E, TotalDominates G E → D.card ≤ E.card

def TriangleFree : Prop := ∀ {a b c : V}, G.Adj a b → G.Adj b c → ¬G.Adj a c

def P5Free : Prop :=
  ∀ {a b c d e : V}, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d e →
    ¬G.Adj a c → ¬G.Adj a d → ¬G.Adj a e →
    ¬G.Adj b d → ¬G.Adj b e → ¬G.Adj c e → False

def NoTwoDisjointEdges : Prop :=
  ∀ {a b c d : V}, G.Adj a b → G.Adj c d →
    ¬G.Adj a c → ¬G.Adj a d → ¬G.Adj b c → ¬G.Adj b d → False

private def Consecutive {n : ℕ} (i j : Fin n) : Prop :=
  i.val+1 = j.val ∨ j.val+1 = i.val

private instance {n : ℕ} (i j : Fin n) : Decidable (Consecutive i j) := by
  unfold Consecutive
  infer_instance

/-- An induced path on `n` vertices, listed in its path order. -/
def InducedPath (n : ℕ) : Prop :=
  ∃ f : Fin n ↪ V, ∀ i j, G.Adj (f i) (f j) ↔ Consecutive i j

/-- Catalogue definition 35, including the count of vertices rather than edges. -/
noncomputable def pathNumber : ℕ := sSup {n : ℕ | InducedPath G n}

private theorem pathFive_of_pattern {a b c d e : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hde : G.Adj d e)
    (hac : ¬G.Adj a c) (had : ¬G.Adj a d) (hae : ¬G.Adj a e)
    (hbd : ¬G.Adj b d) (hbe : ¬G.Adj b e) (hce : ¬G.Adj c e) :
    InducedPath G 5 := by
  let f : Fin 5 → V := ![a,b,c,d,e]
  have hba := hab.symm
  have hcb := hbc.symm
  have hdc := hcd.symm
  have hed := hde.symm
  have hca : ¬G.Adj c a := fun h => hac h.symm
  have hda : ¬G.Adj d a := fun h => had h.symm
  have hea : ¬G.Adj e a := fun h => hae h.symm
  have hdb : ¬G.Adj d b := fun h => hbd h.symm
  have heb : ¬G.Adj e b := fun h => hbe h.symm
  have hec : ¬G.Adj e c := fun h => hce h.symm
  have hrel (i j : Fin 5) : G.Adj (f i) (f j) ↔ Consecutive i j := by
    fin_cases i <;> fin_cases j <;> simp [f, Consecutive, *]
  have distinctRows : ∀ i j : Fin 5, i ≠ j →
      ∃ k, ¬(Consecutive i k ↔ Consecutive j k) := by decide +kernel
  have hf : Function.Injective f := by
    intro i j he
    by_contra hn
    obtain ⟨k,hk⟩ := distinctRows i j hn
    exact hk ((hrel i k).symm.trans (he ▸ hrel j k))
  exact ⟨⟨f,hf⟩,hrel⟩

theorem pathNumber_le_four_iff [Fintype V] : pathNumber G ≤ 4 ↔ P5Free G := by
  constructor
  · intro h a b c d e hab hbc hcd hde hac had hae hbd hbe hce
    have hp := pathFive_of_pattern G hab hbc hcd hde hac had hae hbd hbe hce
    have hBound : BddAbove {n : ℕ | InducedPath G n} := by
      refine ⟨Fintype.card V,?_⟩
      rintro n ⟨f,_⟩
      simpa using Fintype.card_le_of_injective f f.injective
    have hle : 5 ≤ pathNumber G := le_csSup hBound hp
    omega
  · intro h
    apply csSup_le'
    intro n hn
    by_contra! hlt
    obtain ⟨f,hf⟩ := (show InducedPath G n from hn)
    let e : Fin 5 → Fin n := fun i => Fin.castLE (by omega) i
    have hrel (i j : Fin 5) : G.Adj (f (e i)) (f (e j)) ↔ Consecutive i j :=
      hf (e i) (e j)
    exact h ((hrel 0 1).mpr (by decide)) ((hrel 1 2).mpr (by decide))
      ((hrel 2 3).mpr (by decide)) ((hrel 3 4).mpr (by decide))
      (fun he => (by decide : ¬Consecutive (0 : Fin 5) 2) ((hrel 0 2).mp he))
      (fun he => (by decide : ¬Consecutive (0 : Fin 5) 3) ((hrel 0 3).mp he))
      (fun he => (by decide : ¬Consecutive (0 : Fin 5) 4) ((hrel 0 4).mp he))
      (fun he => (by decide : ¬Consecutive (1 : Fin 5) 3) ((hrel 1 3).mp he))
      (fun he => (by decide : ¬Consecutive (1 : Fin 5) 4) ((hrel 1 4).mp he))
      (fun he => (by decide : ¬Consecutive (2 : Fin 5) 4) ((hrel 2 4).mp he))

private theorem length_take {u v : V} (p : G.Walk u v) (i : ℕ) :
    (p.take i).length = min i p.length := by
  induction p generalizing i with
  | nil => simp [Walk.take]
  | cons h p ih =>
    cases i with
    | zero => simp [Walk.take]
    | succ i =>
      change (p.take i).length + 1 = min (i+1) (p.length+1)
      rw [ih]
      omega

private theorem length_drop {u v : V} (p : G.Walk u v) (i : ℕ) :
    (p.drop i).length = p.length-i := by
  induction p generalizing i with
  | nil => simp [Walk.drop]
  | cons h p ih =>
    cases i with
    | zero => simp [Walk.drop]
    | succ i =>
      change (p.drop i).length = p.length+1-(i+1)
      rw [ih]
      omega

private theorem span_le_dist {u v : V} (hc : G.Connected)
    (p : G.Walk u v) (hp : p.length = G.dist u v) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ p.length) :
    j-i ≤ G.dist (p.getVert i) (p.getVert j) := by
  obtain ⟨q,hq⟩ := hc.exists_walk_length_eq_dist (p.getVert i) (p.getVert j)
  have h := G.dist_le ((p.take i).append (q.append (p.drop j)))
  rw [Walk.length_append,Walk.length_append,length_take,length_drop,hq,← hp] at h
  omega

private theorem no_geodesic_chord {u v : V} (hc : G.Connected)
    (p : G.Walk u v) (hp : p.length = G.dist u v) {i j : ℕ}
    (hij : i+2 ≤ j) (hj : j ≤ p.length) :
    ¬G.Adj (p.getVert i) (p.getVert j) := by
  intro h
  have hd := span_le_dist G hc p hp (by omega : i ≤ j) hj
  rw [dist_eq_one_iff_adj.mpr h] at hd
  omega

private theorem dist_le_three (hc : G.Connected) (hP : P5Free G) (u v : V) :
    G.dist u v ≤ 3 := by
  by_contra! h
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist u v
  have chord (i j : ℕ) (hij : i+2 ≤ j) (hj : j ≤ 4) :
      ¬G.Adj (p.getVert i) (p.getVert j) :=
    no_geodesic_chord G hc p hp hij (by omega)
  exact hP (p.adj_getVert_succ (i := 0) (by omega)) (p.adj_getVert_succ (i := 1) (by omega))
    (p.adj_getVert_succ (i := 2) (by omega)) (p.adj_getVert_succ (i := 3) (by omega))
    (chord 0 2 (by decide) (by decide)) (chord 0 3 (by decide) (by decide))
    (chord 0 4 (by decide) (by decide)) (chord 1 3 (by decide) (by decide))
    (chord 1 4 (by decide) (by decide)) (chord 2 4 (by decide) (by decide))

private theorem no_two_edges_closest (hc : G.Connected) (hP : P5Free G) (hT : TriangleFree G)
    {a b c d : V} (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : ¬G.Adj a c) (had : ¬G.Adj a d) (hbc : ¬G.Adj b c) (hbd : ¬G.Adj b d)
    (hclosest : G.dist a c ≤ G.dist b c) : False := by
  have hne : a ≠ c := fun he => had (he.symm ▸ hcd)
  have hlo := hc.one_lt_dist_of_ne_of_not_adj hne hac
  have hhi := dist_le_three G hc hP a c
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist a c
  have ha₁ : G.Adj a (p.getVert 1) := by
    simpa using p.adj_getVert_succ (i := 0) (by omega)
  have hb₁ : ¬G.Adj b (p.getVert 1) := hT hab.symm ha₁
  by_cases h₂ : p.length = 2
  · have hend := p.getVert_of_length_le (i := 2) h₂.le
    have h₁c : G.Adj (p.getVert 1) c := by
      simpa only [hend] using p.adj_getVert_succ (i := 1) (by omega)
    exact hP hab.symm ha₁ h₁c hcd hb₁ hbc hbd hac had (hT h₁c hcd)
  · have h₃ : p.length = 3 := by omega
    have hend := p.getVert_of_length_le (i := 3) h₃.le
    have h12 := p.adj_getVert_succ (i := 1) (by omega)
    have h₂c : G.Adj (p.getVert 2) c := by
      simpa only [hend] using p.adj_getVert_succ (i := 2) (by omega)
    have hb₂ : ¬G.Adj b (p.getVert 2) := by
      intro h
      have hlen := G.dist_le ((p.drop 2).cons h)
      rw [Walk.length_cons,length_drop] at hlen
      omega
    have ha₂ : ¬G.Adj a (p.getVert 2) := hT ha₁ h12
    exact hP hab.symm ha₁ h12 h₂c hb₁ hb₂ hbc ha₂ hac (hT h12 h₂c)

theorem no_two_edges (hc : G.Connected) (hP : P5Free G) (hT : TriangleFree G) :
    NoTwoDisjointEdges G := by
  intro a b c d hab hcd hac had hbc hbd
  rcases le_total (G.dist a c) (G.dist b c) with h | h
  · exact no_two_edges_closest G hc hP hT hab hcd hac had hbc hbd h
  · exact no_two_edges_closest G hc hP hT hab.symm hcd hbc hbd hac had h

#print axioms pathNumber_le_four_iff
#print axioms no_two_edges


private def CycleAdjacent (i j : Fin 5) : Prop :=
  (i.val+1)%5 = j.val ∨ (j.val+1)%5 = i.val

private instance (i j : Fin 5) : Decidable (CycleAdjacent i j) := by
  unfold CycleAdjacent
  infer_instance

def cycleFive : SimpleGraph (Fin 5) where
  Adj := CycleAdjacent
  symm := fun _ _ h => h.symm
  loopless := by change ∀ i : Fin 5, ¬CycleAdjacent i i; decide +kernel

private instance : DecidableRel cycleFive.Adj := fun i j =>
  inferInstanceAs (Decidable (CycleAdjacent i j))

private theorem opposite_edge :
    ∀ i : Fin 5, ∃ j k, cycleFive.Adj j k ∧ ¬cycleFive.Adj i j ∧ ¬cycleFive.Adj i k := by
  decide +kernel

private theorem cycle_neighbor :
    ∀ i : Fin 5, ∃ j, cycleFive.Adj i j := by decide +kernel

private theorem neighbor_types :
    ∀ S : Finset (Fin 5), 2 ≤ S.card →
      (∀ i j : Fin 5, i ∈ S → j ∈ S → ¬cycleFive.Adj i j) →
      ∃ k : Fin 5, ∀ j : Fin 5, j ∈ S ↔ cycleFive.Adj k j := by
  decide +kernel

private theorem common_cycle_neighbor :
    ∀ i j : Fin 5, ¬cycleFive.Adj i j →
      ∃ k, cycleFive.Adj i k ∧ cycleFive.Adj j k := by
  decide +kernel

private theorem separated_cycle_neighbors :
    ∀ i j : Fin 5, cycleFive.Adj i j →
      ∃ p q, cycleFive.Adj i p ∧ cycleFive.Adj j q ∧
        ¬cycleFive.Adj i q ∧ ¬cycleFive.Adj j p ∧ ¬cycleFive.Adj p q := by
  decide +kernel

private theorem cycle_types_injective :
    ∀ i j : Fin 5, (∀ k : Fin 5, cycleFive.Adj i k ↔ cycleFive.Adj j k) → i = j := by
  decide +kernel

def HasInducedCycleFive : Prop :=
  ∃ c : Fin 5 → V, ∀ i j, G.Adj (c i) (c j) ↔ cycleFive.Adj i j

private theorem walk_closed {u v : V} (P : V → Prop)
    (h : ∀ x y, P x → G.Adj x y → P y) (p : G.Walk u v) :
    P u → P v := by
  induction p with
  | nil => exact id
  | cons ha _ ih => exact fun hu => ih (h _ _ hu ha)

theorem cycle_decomposition (hc : G.Connected) (hT : TriangleFree G)
    (hM : NoTwoDisjointEdges G) (hC : HasInducedCycleFive G) :
    ∃ f : V → Fin 5, Function.Surjective f ∧
      ∀ x y, G.Adj x y ↔ cycleFive.Adj (f x) (f y) := by
  classical
  obtain ⟨c,he⟩ := hC
  let HasNeighbor (x : V) := ∃ i, G.Adj x (c i)
  let HasType (x : V) := ∃ i, ∀ j, G.Adj x (c j) ↔ cycleFive.Adj i j
  have hType (x : V) (hx : HasNeighbor x) : HasType x := by
    let N := (univ : Finset (Fin 5)).filter (fun i => G.Adj x (c i))
    have hN (i : Fin 5) : i ∈ N ↔ G.Adj x (c i) := by simp [N]
    obtain ⟨i,hi⟩ := hx
    obtain ⟨j,k,hjk,hij,hik⟩ := opposite_edge i
    have hAlt : G.Adj x (c j) ∨ G.Adj x (c k) := by
      by_contra! hh
      exact hM hi ((he j k).mpr hjk) hh.1 hh.2
        (fun h => hij ((he i j).mp h)) (fun h => hik ((he i k).mp h))
    have hSize : 2 ≤ N.card := by
      apply Nat.succ_le_of_lt
      refine one_lt_card.mpr ⟨i,(hN i).mpr hi,?_⟩
      rcases hAlt with hj | hk
      · exact ⟨j,(hN j).mpr hj,fun h => hik (h.symm ▸ hjk)⟩
      · exact ⟨k,(hN k).mpr hk,fun h => hij (h.symm ▸ hjk.symm)⟩
    obtain ⟨t,ht⟩ := neighbor_types N hSize (by
      intro a b ha hb hab
      exact hT ((hN a).mp ha).symm ((hN b).mp hb) ((he a b).mpr hab))
    exact ⟨t,fun j => (hN j).symm.trans (ht j)⟩
  have hClosed (x y : V) (hx : HasNeighbor x) (hxy : G.Adj x y) : HasNeighbor y := by
    obtain ⟨i,hi⟩ := hType x hx
    obtain ⟨j,k,hjk,hij,hik⟩ := opposite_edge i
    apply Classical.byContradiction
    intro hn
    exact hM hxy ((he j k).mpr hjk) (fun h => hij ((hi _).mp h))
      (fun h => hik ((hi _).mp h)) (fun h => hn ⟨j,h⟩) (fun h => hn ⟨k,h⟩)
  have hAll (v : V) : HasType v := by
    have hzero : HasNeighbor (c 0) := ⟨1,(he 0 1).mpr (by decide)⟩
    obtain ⟨p⟩ := hc (c 0) v
    exact hType v (walk_closed G HasNeighbor hClosed p hzero)
  choose f hf using hAll
  refine ⟨f,?_,?_⟩
  · intro i
    exact ⟨c i, cycle_types_injective _ _ (fun j => ((hf (c i) j).symm.trans (he i j)))⟩
  · intro x y
    constructor
    · intro hxy
      apply Classical.byContradiction
      intro hn
      obtain ⟨j,hx,hy⟩ := common_cycle_neighbor _ _ hn
      exact hT hxy ((hf y j).mpr hy) ((hf x j).mpr hx)
    · intro hxy
      apply Classical.byContradiction
      intro hn
      obtain ⟨p,q,hxp,hyq,hxq,hyp,hpq⟩ := separated_cycle_neighbors _ _ hxy
      exact hM ((hf x p).mpr hxp) ((hf y q).mpr hyq) hn
        (fun h => hxq ((hf x q).mp h)) (fun h => hyp ((hf y p).mp h.symm))
        (fun h => hpq ((he p q).mp h))

private instance {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (S : Finset W) : Decidable (TotalDominates H S) := by
  unfold TotalDominates
  infer_instance

private theorem cycle_five_lower :
    ∀ S : Finset (Fin 5), TotalDominates cycleFive S → 3 ≤ S.card := by
  decide +kernel

private theorem cycle_five_sub :
    ∀ S : Finset (Fin 5), TotalDominates cycleFive S → 4 ≤ S.card →
      ∃ T : Finset (Fin 5), T ⊂ S ∧ TotalDominates cycleFive T := by
  decide +kernel

private theorem cycle_five_good : WellTotalDominated cycleFive := by
  intro D hD E hE
  have hl := cycle_five_lower E hE
  by_contra! h
  obtain ⟨T,ht,hT⟩ := cycle_five_sub D hD.1 (by omega)
  exact hD.2 T ht hT

private theorem wtd_of_surjection {W : Type*} (H : SimpleGraph W) (f : V → W)
    (hf : Function.Surjective f) (hrel : ∀ x y, G.Adj x y ↔ H.Adj (f x) (f y))
    (hW : WellTotalDominated H) : WellTotalDominated G := by
  classical
  have transfer (D : Finset V) : TotalDominates H (D.image f) ↔ TotalDominates G D := by
    constructor
    · intro h x
      obtain ⟨y,hy,ha⟩ := h (f x)
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hy
      exact ⟨z,hz,(hrel x z).mpr ha⟩
    · intro h y
      obtain ⟨x,rfl⟩ := hf y
      obtain ⟨z,hz,ha⟩ := h x
      exact ⟨f z,mem_image_of_mem _ hz,(hrel x z).mp ha⟩
  intro D hD E hE
  have hDmin : MinimalTotalDominates H (D.image f) := by
    refine ⟨(transfer D).mpr hD.1,?_⟩
    intro B hB hBD
    let A := D.filter fun a => f a ∈ B
    have hEq : A.image f = B := by
      ext b
      constructor
      · rintro hb
        obtain ⟨a,ha,rfl⟩ := mem_image.mp hb
        exact (mem_filter.mp ha).2
      · intro hb
        obtain ⟨a,ha,rfl⟩ := mem_image.mp (hB.subset hb)
        exact mem_image_of_mem _ (mem_filter.mpr ⟨ha,hb⟩)
    have hss : A ⊂ D := ssubset_of_subset_of_ne (filter_subset _ _) (fun he =>
      hB.ne (by rw [← hEq,he]))
    exact hD.2 A hss ((transfer A).mp (hEq.symm ▸ hBD))
  have hcard : (D.image f).card = D.card := by
    apply card_image_of_injOn
    intro a ha b hb hab
    by_contra hne
    have he : (D.erase a).image f = D.image f := by
      ext w
      constructor
      · intro hw
        obtain ⟨z,hz,rfl⟩ := mem_image.mp hw
        exact mem_image_of_mem _ (mem_of_mem_erase hz)
      · intro hw
        obtain ⟨z,hz,rfl⟩ := mem_image.mp hw
        by_cases h : z=a
        · subst z
          exact mem_image.mpr ⟨b,mem_erase.mpr ⟨Ne.symm hne,hb⟩,hab.symm⟩
        · exact mem_image_of_mem _ (mem_erase.mpr ⟨h,hz⟩)
    exact hD.2 _ (erase_ssubset ha) ((transfer _).mp (he.symm ▸ (transfer D).mpr hD.1))
  have hi := hW _ hDmin _ ((transfer E).mpr hE)
  rw [hcard] at hi
  exact hi.trans card_image_le

private theorem private_neighbor {S : Finset V} (hS : MinimalTotalDominates G S)
    {x : V} (hx : x ∈ S) : ∃ p, G.Adj p x ∧ ∀ y ∈ S, G.Adj p y → y = x := by
  classical
  have hn := hS.2 _ (erase_ssubset hx)
  unfold TotalDominates at hn
  push_neg at hn
  obtain ⟨p,hp⟩ := hn
  have only_x (y : V) (hy : y ∈ S) (hpy : G.Adj p y) : y = x :=
    Classical.byContradiction fun h => hp y (mem_erase.mpr ⟨h,hy⟩) hpy
  obtain ⟨y,hy,hpy⟩ := hS.1 p
  exact ⟨p,only_x y hy hpy ▸ hpy,only_x⟩

private theorem induced_cycle_of_triple {S : Finset V} (hS : MinimalTotalDominates G S)
    (hP : P5Free G) (hT : TriangleFree G)
    {a b c : V} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hac : a ≠ c) (hab : G.Adj a b) (hbc : G.Adj b c) :
    HasInducedCycleFive G := by
  classical
  obtain ⟨p,hpa,hp⟩ := private_neighbor G hS ha
  obtain ⟨q,hqc,hq⟩ := private_neighbor G hS hc
  have hpb : ¬G.Adj p b := fun h => hab.ne (hp b hb h).symm
  have hpc : ¬G.Adj p c := fun h => hac (hp c hc h).symm
  have hqa : ¬G.Adj q a := fun h => hac (hq a ha h)
  have hqb : ¬G.Adj q b := fun h => hbc.ne (hq b hb h)
  have haq : ¬G.Adj a q := fun h => hqa h.symm
  have hbq : ¬G.Adj b q := fun h => hqb h.symm
  have hnac : ¬G.Adj a c := hT hab hbc
  have hpq : G.Adj p q := Classical.byContradiction fun h =>
    hP hpa hab hbc hqc.symm hpb hpc h hnac haq hbq
  let f : Fin 5 → V := ![p,a,b,c,q]
  have hap := hpa.symm
  have hba := hab.symm
  have hcb := hbc.symm
  have hcq := hqc.symm
  have hqp := hpq.symm
  have hbp : ¬ G.Adj b p := fun h => hpb h.symm
  have hcp : ¬ G.Adj c p := fun h => hpc h.symm
  have hca : ¬ G.Adj c a := fun h => hnac h.symm
  refine ⟨f,?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;> simp [f, cycleFive, CycleAdjacent, *] <;> decide

private theorem min_size_without_cycle [Nonempty V] {S : Finset V}
    (hS : MinimalTotalDominates G S) (hP : P5Free G) (hT : TriangleFree G)
    (hM : NoTwoDisjointEdges G) (hC : ¬HasInducedCycleFive G) : S.card ≤ 2 := by
  classical
  obtain ⟨v⟩ := (inferInstance : Nonempty V)
  obtain ⟨a,ha,_⟩ := hS.1 v
  obtain ⟨b,hb,hab⟩ := hS.1 a
  have forbid {x y z : V} (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S)
      (hne : x ≠ z) (hxy : G.Adj x y) (hyz : G.Adj y z) : False :=
    hC (induced_cycle_of_triple G hS hP hT hx hy hz hne hxy hyz)
  have hsub : S ⊆ {a,b} := by
    intro c hc
    by_cases hca : c = a
    · simp [hca]
    by_cases hcb : c = b
    · simp [hcb]
    exfalso
    have hnca : ¬G.Adj c a := fun h => forbid hc ha hb hcb h hab
    have hncb : ¬G.Adj c b := fun h => forbid hc hb ha hca h hab.symm
    obtain ⟨d,hd,hcd⟩ := hS.1 c
    have hnda : ¬G.Adj d a := fun h => forbid hc hd ha hca hcd h
    have hndb : ¬G.Adj d b := fun h => forbid hc hd hb hcb hcd h
    exact hM hab hcd (fun h => hnca h.symm) (fun h => hnda h.symm)
      (fun h => hncb h.symm) (fun h => hndb h.symm)
  simpa [hab.ne] using card_le_card hsub

/-- The exact catalogue statement, with the induced-path number measured in vertices. -/
theorem conjecture314 [Fintype V] (hc : G.Connected) (_hn : 1 < Fintype.card V)
    (hT : TriangleFree G) (hPath : pathNumber G ≤ 4) : WellTotalDominated G := by
  classical
  haveI := hc.nonempty
  have hP : P5Free G := (pathNumber_le_four_iff G).mp hPath
  have hM : NoTwoDisjointEdges G := no_two_edges G hc hP hT
  by_cases hC : HasInducedCycleFive G
  · obtain ⟨f,hf,ha⟩ := cycle_decomposition G hc hT hM hC
    exact wtd_of_surjection G cycleFive f hf ha cycle_five_good
  · intro D hD E hE
    have hl := min_size_without_cycle G hD hP hT hM hC
    obtain ⟨v⟩ := hc.nonempty
    obtain ⟨a,ha,_⟩ := hE v
    obtain ⟨b,hb,hab⟩ := hE a
    exact hl.trans (one_lt_card.mpr ⟨a,ha,b,hb,hab.ne⟩)

#print axioms conjecture314
#print axioms cycle_decomposition

end Graffiti314
