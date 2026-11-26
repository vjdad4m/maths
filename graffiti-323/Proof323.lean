import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! Written on the Wall II #323. The proof is structural at every order.
The common-neighbor reformulation is due to Claude Opus 5 at AI Village,
graffiti-verification README §7fj. -/

namespace Graffiti323
open Finset SimpleGraph
open scoped Sym2
noncomputable section
variable {V : Type*} [Fintype V]
local instance : DecidableEq V := Classical.decEq V
local instance (H : SimpleGraph V) : DecidableRel H.Adj := Classical.decRel H.Adj

def edgeNeighborhood (H : SimpleGraph V) (u v : V) : Finset V :=
  H.neighborFinset u ∪ H.neighborFinset v

def maxEdgeNeighborhood (H : SimpleGraph V) : ℕ :=
  univ.sup (fun u => (univ.filter (H.Adj u)).sup fun v => (edgeNeighborhood H u v).card)

theorem edgeNeighborhood_le_max (H : SimpleGraph V) {u v : V} (h : H.Adj u v) :
    (edgeNeighborhood H u v).card ≤ maxEdgeNeighborhood H :=
  (le_sup (f := fun v => (edgeNeighborhood H u v).card) (mem_filter.mpr ⟨mem_univ _,h⟩)).trans
    (le_sup (f := fun u => (univ.filter (H.Adj u)).sup fun v => (edgeNeighborhood H u v).card) (mem_univ u))

private theorem edgeNeighborhood_spec {H : SimpleGraph V} {u v w : V} :
    w ∈ edgeNeighborhood H u v ↔ H.Adj u w ∨ H.Adj v w := by
  simp [edgeNeighborhood]

private theorem compl_edge_neighborhood_complement {G : SimpleGraph V}
    {u v : V} (h : Gᶜ.Adj u v) :
    (univ : Finset V) \ edgeNeighborhood Gᶜ u v = G.neighborFinset u ∩ G.neighborFinset v := by
  ext w
  simp only [mem_sdiff,mem_univ,true_and,edgeNeighborhood_spec,mem_inter,mem_neighborFinset]
  constructor
  · intro hw
    have hwu : u ≠ w := fun e => hw (Or.inr (e ▸ h.symm))
    have hwv : v ≠ w := fun e => hw (Or.inl (e ▸ h))
    exact ⟨Classical.byContradiction (fun e => hw (Or.inl ⟨hwu,e⟩)),
      Classical.byContradiction (fun e => hw (Or.inr ⟨hwv,e⟩))⟩
  · rintro ⟨ha,hb⟩ (h₁ | h₂)
    · exact h₁.2 ha
    · exact h₂.2 hb

private theorem at_least_two {H : SimpleGraph V} {u v : V} (h : H.Adj u v) :
    2 ≤ maxEdgeNeighborhood H := by
  have hS : ({u,v} : Finset V) ⊆ edgeNeighborhood H u v := by
    intro w hw
    simp only [mem_insert,mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact edgeNeighborhood_spec.mpr (Or.inr h.symm)
    · exact edgeNeighborhood_spec.mpr (Or.inl h)
  have hcard := (card_le_card hS).trans (edgeNeighborhood_le_max H h)
  simpa [h.ne] using hcard

theorem max_attained (H : SimpleGraph V) (he : ∃ u v, H.Adj u v) :
    ∃ u v, H.Adj u v ∧ (edgeNeighborhood H u v).card = maxEdgeNeighborhood H := by
  obtain ⟨a,b,hab⟩ := he
  haveI : Nonempty V := ⟨a⟩
  have hpos := at_least_two hab
  obtain ⟨u,_,hu⟩ := exists_mem_eq_sup (univ : Finset V) univ_nonempty
    (fun u => (univ.filter (H.Adj u)).sup fun v => (edgeNeighborhood H u v).card)
  change maxEdgeNeighborhood H = _ at hu
  have hun : (univ.filter (H.Adj u)).Nonempty := by
    by_contra! hn
    rw [not_nonempty_iff_eq_empty.mp hn, Finset.sup_empty] at hu
    change maxEdgeNeighborhood H = 0 at hu
    omega
  obtain ⟨v,hv,hd⟩ := exists_mem_eq_sup (univ.filter (H.Adj u)) hun
    (fun v => (edgeNeighborhood H u v).card)
  exact ⟨u,v,(mem_filter.mp hv).2,(hu.trans hd).symm⟩

theorem empty_edge_max (H : SimpleGraph V) (he : ¬ ∃ u v, H.Adj u v) :
    maxEdgeNeighborhood H = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply Finset.sup_le_iff.mpr
  intro u _
  apply Finset.sup_le_iff.mpr
  intro v hv
  exact (he ⟨u,v,(mem_filter.mp hv).2⟩).elim



variable (G : SimpleGraph V)

def TotalDominates (D : Finset V) : Prop := ∀ v, ∃ w ∈ D, G.Adj v w

def WellTotalDominated : Prop :=
  ∀ D, TotalDominates G D → (∀ E, E ⊂ D → ¬TotalDominates G E) →
    ∀ E, TotalDominates G E → D.card ≤ E.card

omit [Fintype V] in
private theorem dominates_two {D : Finset V} (hD : TotalDominates G D) (v : V) :
    ∃ a ∈ D, ∃ b ∈ D, G.Adj a b := by
  obtain ⟨a,ha,_⟩ := hD v
  obtain ⟨b,hb,hab⟩ := hD a
  exact ⟨a,ha,b,hb,hab⟩

omit [Fintype V] in
private theorem wtd_of_pairs (v : V)
    (hpair : ∀ D, TotalDominates G D →
      ∃ a b, G.Adj a b ∧ ({a,b} : Finset V) ⊆ D ∧ TotalDominates G {a,b}) :
    WellTotalDominated G := by
  intro D hD hmin E hE
  obtain ⟨a,b,hab,hsub,hdom⟩ := hpair D hD
  obtain ⟨x,hx,y,hy,hxy⟩ := dominates_two G hE v
  have he : D = {a,b} := by
    by_contra hne
    exact hmin _ (ssubset_of_subset_of_ne hsub (Ne.symm hne)) hdom
  have hle : ({x,y} : Finset V).card ≤ E.card := card_le_card (insert_subset hx (singleton_subset_iff.mpr hy))
  simpa [he,hab.ne,hxy.ne] using hle

omit [Fintype V] in
private theorem no_edge_cross_walk {G : SimpleGraph V} {A : Finset V}
    (h : ∀ x ∈ A, ∀ y, G.Adj x y → y ∈ A) {u v : V} (p : G.Walk u v) :
    u ∈ A → v ∈ A := by
  induction p with
  | nil => exact id
  | cons ha _ ih => exact fun hu => ih (h _ hu _ ha)


def oddVertices (r : V) : Finset V := univ.filter (fun v => G.dist r v % 2 = 1)

omit [Fintype V] in
private theorem sameOddLevel_symm (r : V) :
    Symmetric (fun u v : V => G.dist r u = G.dist r v ∧ G.dist r u % 2 = 1) := by
  intro u v h
  exact ⟨h.1.symm,h.1 ▸ h.2⟩

def oddHorizontal (r : V) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => e ∈ Sym2.fromRel (sameOddLevel_symm G r))

def signedScore (r : V) : ℤ := ((oddVertices G r).card : ℤ) - (oddHorizontal G r).card

def maxSignedScore (hne : Nonempty V) : ℤ :=
  univ.sup' (by letI := hne; exact univ_nonempty) (signedScore G)

def edgesWithin (A : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ A)

private theorem edgeWithin_spec (A : Finset V) (a b : V) :
    s(a,b) ∈ edgesWithin G A ↔ G.Adj a b ∧ a ∈ A ∧ b ∈ A := by
  simp only [edgesWithin,mem_filter,mem_edgeFinset,mem_edgeSet]
  constructor
  · rintro ⟨hab,h⟩
    exact ⟨hab,h a (Sym2.mem_mk_left _ _),h b (Sym2.mem_mk_right _ _)⟩
  · rintro ⟨hab,ha,hb⟩
    refine ⟨hab,?_⟩
    intro v hv
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact ha
    · exact hb

omit [Fintype V] in
private theorem symPair_injective (a : V) :
    Function.Injective (fun b : V => (s(a,b) : Sym2 V)) := by
  intro b c h
  rcases Sym2.mk_eq_mk_iff.mp h with h | h
  · exact congrArg Prod.snd h
  · exact (congrArg Prod.snd h).trans (congrArg Prod.fst h)

private theorem incidence_subset (A C : Finset V) {a : V} (ha : a ∈ A)
    (hC : C ⊆ A) (hAdj : ∀ c ∈ C, G.Adj a c) :
    C.image (fun c => s(a,c)) ⊆ edgesWithin G A := by
  intro e he
  obtain ⟨c,hc,rfl⟩ := mem_image.mp he
  exact (edgeWithin_spec G A a c).mpr ⟨hAdj c hc,ha,hC hc⟩

private theorem odd_subset_erase (r : V) : oddVertices G r ⊆ univ.erase r := by
  intro w hw
  have ho := (mem_filter.mp hw).2
  refine mem_erase.mpr ⟨?_,mem_univ _⟩
  intro h
  subst w
  change G.dist r r % 2 = 1 at ho
  simp [dist_self] at ho

private theorem common_bound_of_score {r u v : V}
    (hs : (maxEdgeNeighborhood Gᶜ : ℤ) ≤ 1 + signedScore G r)
    (h : Gᶜ.Adj u v) :
    Fintype.card V + (oddHorizontal G r).card ≤
      1 + (oddVertices G r).card + (G.neighborFinset u ∩ G.neighborFinset v).card := by
  have h₁ := edgeNeighborhood_le_max Gᶜ h
  have h₂ := card_sdiff (t := (univ : Finset V)) (subset_univ (edgeNeighborhood Gᶜ u v))
  rw [compl_edge_neighborhood_complement h,card_univ] at h₂
  have h₃ := card_le_card (subset_univ (edgeNeighborhood Gᶜ u v))
  rw [card_univ] at h₃
  unfold signedScore at hs
  omega

omit [Fintype V] in
private theorem dist_le_two_of_adj_adj {u v w : V} (hc : G.Connected)
    (hu : G.Adj u w) (hv : G.Adj w v) : G.dist u v ≤ 2 := by
  have h := hc.dist_triangle (u := u) (v := w) (w := v)
  rw [dist_eq_one_iff_adj.mpr hu,dist_eq_one_iff_adj.mpr hv] at h
  exact h

private theorem diam_le_two {r : V} (hc : G.Connected)
    (hs : (maxEdgeNeighborhood Gᶜ : ℤ) ≤ 1 + signedScore G r) :
    ∀ u v, G.dist u v ≤ 2 := by
  classical
  by_contra! hh
  obtain ⟨u,v,hd⟩ := hh
  have hne : u ≠ v := by
    intro h
    subst v
    rw [dist_self] at hd
    omega
  have hcomp : Gᶜ.Adj u v := ⟨hne,fun h => by
    have h' := dist_eq_one_iff_adj.mpr h
    omega⟩
  have hc₀ : G.neighborFinset u ∩ G.neighborFinset v = ∅ := by
    ext w
    simp only [mem_inter, mem_neighborFinset, not_mem_empty, iff_false, not_and]
    intro hu hv
    exact (not_le_of_gt hd) (dist_le_two_of_adj_adj G hc hu hv.symm)
  have hbound := common_bound_of_score G hs hcomp
  rw [hc₀,card_empty] at hbound
  have hsub := odd_subset_erase G r
  have hcard : (univ.erase r : Finset V).card = Fintype.card V-1 := by
    rw [card_erase_of_mem (mem_univ _),card_univ]
  have hp : 0 < Fintype.card V := Fintype.card_pos_iff.mpr hc.nonempty
  have heq := eq_of_subset_of_card_le hsub (by omega)
  let A := insert r (G.neighborFinset r)
  have hClosed (x : V) (hx : x ∈ A) (y : V) (hxy : G.Adj x y) : y ∈ A := by
    rw [show A = insert r (G.neighborFinset r) from rfl] at hx
    rcases mem_insert.mp hx with rfl | hx
    · exact mem_insert_of_mem ((G.mem_neighborFinset _ _).mpr hxy)
    · apply Classical.byContradiction
      intro hy
      have hyr : y ≠ r := fun e => hy (e ▸ (mem_insert_self r (G.neighborFinset r)))
      have hyr' : ¬G.Adj r y := fun h => hy (mem_insert_of_mem ((G.mem_neighborFinset _ _).mpr h))
      have hd₂ := dist_le_two_of_adj_adj G hc ((G.mem_neighborFinset _ _).mp hx) hxy
      have hd₁ := hc.one_lt_dist_of_ne_of_not_adj hyr.symm hyr'
      have hdEq : G.dist r y = 2 := by omega
      have ho : y ∈ oddVertices G r := heq.symm ▸ mem_erase.mpr ⟨hyr, mem_univ _⟩
      have hh := (mem_filter.mp ho).2
      change G.dist r y % 2 = 1 at hh
      rw [hdEq] at hh
      omega
  have hIn (x : V) : x ∈ A := by
    obtain ⟨p⟩ := hc r x
    exact no_edge_cross_walk hClosed p (mem_insert_self _ _)
  by_cases hu : u = r
  · subst u
    have hvn : v ∈ G.neighborFinset r := by
      rcases mem_insert.mp (hIn v) with hv | hv
      · exact (hne hv.symm).elim
      · exact hv
    exact hcomp.2 ((G.mem_neighborFinset _ _).mp hvn)
  by_cases hv : v = r
  · subst v
    have hun : u ∈ G.neighborFinset r := by
      rcases mem_insert.mp (hIn u) with h | h
      · exact (hu h).elim
      · exact h
    exact hcomp.2 ((G.mem_neighborFinset _ _).mp hun).symm
  have hun := (G.mem_neighborFinset _ _).mp ((mem_insert.mp (hIn u)).resolve_left hu)
  have hvn := (G.mem_neighborFinset _ _).mp ((mem_insert.mp (hIn v)).resolve_left hv)
  exact (not_le_of_gt hd) (dist_le_two_of_adj_adj G hc hun.symm hvn)


omit [Fintype V] in
private theorem odd_iff_adj_of_diam_le_two {r w : V}
    (hd : ∀ u v, G.dist u v ≤ 2) :
    G.dist r w % 2 = 1 ↔ G.Adj r w := by
  rw [← dist_eq_one_iff_adj]
  have h := hd r w
  omega

private theorem odd_eq_neighbors (r : V) (hd : ∀ u v, G.dist u v ≤ 2) :
    oddVertices G r = G.neighborFinset r := by
  ext v
  simpa only [oddVertices,mem_filter,mem_univ,true_and,mem_neighborFinset] using
    (odd_iff_adj_of_diam_le_two G (r := r) (w := v) hd)

private theorem horizontal_eq_internal (r : V) (hd : ∀ u v, G.dist u v ≤ 2) :
    oddHorizontal G r = edgesWithin G (G.neighborFinset r) := by
  ext e
  induction e using Sym2.inductionOn with
  | _ a b =>
    rw [edgeWithin_spec G (G.neighborFinset r)]
    simp only [oddHorizontal, mem_filter, mem_edgeFinset, mem_edgeSet, Sym2.fromRel_prop,
      mem_neighborFinset]
    constructor
    · rintro ⟨hab,he,hodd⟩
      exact ⟨hab,(odd_iff_adj_of_diam_le_two G hd).mp hodd,
        (odd_iff_adj_of_diam_le_two G hd).mp (he ▸ hodd)⟩
    · rintro ⟨hab,ha,hb⟩
      exact ⟨hab,(dist_eq_one_iff_adj.mpr ha).trans (dist_eq_one_iff_adj.mpr hb).symm,
        (odd_iff_adj_of_diam_le_two G hd).mpr ha⟩

private theorem internal_pair_dominates (A : Finset V)
    (hNeighbor : ∀ w ∈ A, ∃ z ∈ A, G.Adj w z)
    (hCommon : ∀ ⦃w x⦄, w ∈ A → x ∈ A → Gᶜ.Adj w x →
      (edgesWithin G A).card ≤
        1 + ((G.neighborFinset w ∩ G.neighborFinset x) ∩ A).card)
    {x y : V} (hx : x ∈ A) (hy : y ∈ A) (hxy : G.Adj x y) :
    ∀ w ∈ A, G.Adj w x ∨ G.Adj w y := by
  classical
  intro w hw
  by_contra! h
  obtain ⟨hnx,hny⟩ := h
  have hneX : w ≠ x := fun h => hny (h ▸ hxy)
  have hneY : w ≠ y := fun h => hnx (h ▸ hxy.symm)
  let H := edgesWithin G A
  have hxyH : s(x,y) ∈ H := (edgeWithin_spec G A x y).mpr ⟨hxy,hx,hy⟩
  obtain ⟨z,hz,hwz⟩ := hNeighbor w hw
  have hwzH : s(w,z) ∈ H := (edgeWithin_spec G A w z).mpr ⟨hwz,hw,hz⟩
  have hnotXY : w ∉ (s(x,y) : Sym2 V) := fun he => (Sym2.mem_iff.mp he).elim hneX hneY
  have hne : (s(x,y) : Sym2 V) ≠ s(w,z) := fun e =>
    hnotXY (e.symm ▸ Sym2.mem_mk_left w z)
  have hh₂ : 2 ≤ H.card := by
    have hu := card_le_card (show ({s(x,y),s(w,z)} : Finset (Sym2 V)) ⊆ H from
      insert_subset hxyH (singleton_subset_iff.mpr hwzH))
    simpa [hne] using hu
  let C := (G.neighborFinset w ∩ G.neighborFinset x) ∩ A
  have hh := hCommon hw hx ⟨hneX,hnx⟩
  change H.card ≤ 1 + C.card at hh
  obtain ⟨t,ht⟩ := card_pos.mp (show 0 < C.card by omega)
  have hwt := (G.mem_neighborFinset _ _).mp (mem_inter.mp (mem_inter.mp ht).1).1
  have hxt := (G.mem_neighborFinset _ _).mp (mem_inter.mp (mem_inter.mp ht).1).2
  have htA := (mem_inter.mp ht).2
  have hxtH : s(x,t) ∈ H := (edgeWithin_spec G A x t).mpr ⟨hxt,hx,htA⟩
  let W := C.image (fun u => s(w,u))
  have hW : W ⊆ H := incidence_subset G A C hw inter_subset_right
    (fun u hu => (G.mem_neighborFinset _ _).mp (mem_inter.mp (mem_inter.mp hu).1).1)
  have hNoMem {e : Sym2 V} (he : w ∉ e) : e ∉ W := by
    intro h
    obtain ⟨u,_,rfl⟩ := mem_image.mp h
    exact he (Sym2.mem_mk_left _ _)
  have hnotXT : w ∉ (s(x,t) : Sym2 V) := fun he =>
    (Sym2.mem_iff.mp he).elim hneX hwt.ne
  have hne' : (s(x,y) : Sym2 V) ≠ s(x,t) := fun e =>
    hny ((symPair_injective x e).symm ▸ hwt)
  have hcards : W.card = C.card := card_image_of_injective _ (symPair_injective w)
  have hbig := card_le_card (insert_subset hxyH (insert_subset hxtH hW))
  rw [card_insert_of_not_mem (by simp [hne',hNoMem hnotXY]),
    card_insert_of_not_mem (hNoMem hnotXT),hcards] at hbig
  omega

set_option maxHeartbeats 800000 in
private theorem structural (r : V) (hc : G.Connected)
    (hs : (maxEdgeNeighborhood Gᶜ : ℤ) ≤ 1 + signedScore G r) :
    WellTotalDominated G := by
  classical
  have hd := diam_le_two G hc hs
  let A := G.neighborFinset r
  let L := (univ.erase r : Finset V) \ A
  let H := edgesWithin G A
  have hASub : A ⊆ univ.erase r := by
    intro a ha
    exact mem_erase.mpr ⟨((G.mem_neighborFinset _ _).mp ha).ne.symm,mem_univ _⟩
  have hL (l : V) : l ∈ L ↔ l ≠ r ∧ l ∉ A := by simp [L]
  have hSize : Fintype.card V = 1 + A.card + L.card := by
    have hn : 0 < Fintype.card V := Fintype.card_pos_iff.mpr hc.nonempty
    have hdiff := card_sdiff hASub
    rw [card_erase_of_mem (mem_univ _),card_univ] at hdiff
    have hle := card_le_card hASub
    rw [card_erase_of_mem (mem_univ _),card_univ] at hle
    change L.card = _ at hdiff
    omega
  have hBound {u v : V} (h : Gᶜ.Adj u v) :
      L.card + H.card ≤ (G.neighborFinset u ∩ G.neighborFinset v).card := by
    have h₀ := common_bound_of_score G hs h
    rw [odd_eq_neighbors G r hd,horizontal_eq_internal G r hd] at h₀
    change Fintype.card V + H.card ≤ 1 + A.card + _ at h₀
    omega
  have hCross {a l : V} (ha : a ∈ A) (hl : l ∈ L) : G.Adj a l := by
    apply Classical.byContradiction
    intro hno
    have hal : a ≠ l := fun h => ((hL l).mp hl).2 (h ▸ ha)
    let C := G.neighborFinset a ∩ G.neighborFinset l
    have hb := hBound (u := a) (v := l) ⟨hal,hno⟩
    have hC : C \ A ⊆ L.erase l := by
      intro v hv
      have hvL := (mem_sdiff.mp hv).2
      have hlv : G.Adj l v := (G.mem_neighborFinset _ _).mp (mem_inter.mp (mem_sdiff.mp hv).1).2
      have hvr : v ≠ r := by
        intro e
        subst v
        exact ((hL l).mp hl).2 ((G.mem_neighborFinset _ _).mpr hlv.symm)
      exact mem_erase.mpr ⟨hlv.ne.symm,(hL v).mpr ⟨hvr,hvL⟩⟩
    have ht := card_le_card hC
    rw [card_erase_of_mem hl] at ht
    have hS := card_le_card (incidence_subset G A (C ∩ A) ha inter_subset_right
      (fun v hv => (G.mem_neighborFinset _ _).mp (mem_inter.mp (mem_inter.mp hv).1).1))
    rw [card_image_of_injective _ (symPair_injective a)] at hS
    have hsum := card_inter_add_card_sdiff C A
    have hLpos := card_pos.mpr ⟨l,hl⟩
    change L.card + H.card ≤ C.card at hb
    change (C ∩ A).card ≤ H.card at hS
    omega
  have hOut (a : V) (ha : a ∈ A) (v : V) (hv : v ∉ A) : G.Adj a v := by
    by_cases h : v = r
    · subst v
      exact ((G.mem_neighborFinset _ _).mp ha).symm
    · exact hCross ha ((hL v).mpr ⟨h,hv⟩)
  have hInside {w x : V} (h : Gᶜ.Adj w x) :
      H.card ≤ 1 + ((G.neighborFinset w ∩ G.neighborFinset x) ∩ A).card := by
    let C := G.neighborFinset w ∩ G.neighborFinset x
    have hC : C \ A ⊆ insert r L := by
      intro v hv
      by_cases he : v = r
      · subst v
        exact mem_insert_self _ _
      · exact mem_insert_of_mem ((hL v).mpr ⟨he,(mem_sdiff.mp hv).2⟩)
    have hsum := card_inter_add_card_sdiff C A
    have hcard := (card_le_card hC).trans (card_insert_le r L)
    have h := hBound h
    change L.card + H.card ≤ C.card at h
    change H.card ≤ 1 + (C ∩ A).card
    omega
  apply wtd_of_pairs G r
  intro D hD
  by_cases hdOut : ∃ b ∈ D, b ∉ A
  · obtain ⟨a,haD,hra⟩ := hD r
    have haA : a ∈ A := (G.mem_neighborFinset _ _).mpr hra
    obtain ⟨b,hbD,hbA⟩ := hdOut
    refine ⟨a,b,hOut a haA b hbA,insert_subset haD (singleton_subset_iff.mpr hbD),?_⟩
    intro v
    by_cases hv : v ∈ A
    · exact ⟨b,by simp,hOut v hv b hbA⟩
    · exact ⟨a,by simp,(hOut a haA v hv).symm⟩
  · have hDA : D ⊆ A := fun v hv => Classical.byContradiction fun hn => hdOut ⟨v,hv,hn⟩
    have hNeighbor (w : V) (_ : w ∈ A) : ∃ z ∈ A, G.Adj w z := by
      obtain ⟨z,hz,hadj⟩ := hD w
      exact ⟨z,hDA hz,hadj⟩
    obtain ⟨a,ha,b,hb,hab⟩ := dominates_two G hD r
    refine ⟨a,b,hab,insert_subset ha (singleton_subset_iff.mpr hb),?_⟩
    intro v
    by_cases hv : v ∈ A
    · rcases internal_pair_dominates G A hNeighbor (by intro _ _ _ _ h; exact hInside h)
          (hDA ha) (hDA hb) hab v hv with hva | hvb
      · exact ⟨a,by simp,hva⟩
      · exact ⟨b,by simp,hvb⟩
    · exact ⟨a,by simp,(hOut a (hDA ha) v hv).symm⟩

/-- The exact signed bound, with the edge-neighborhood maximum assigned zero
on an empty complement. The complete-graph conclusion also holds independently. -/
theorem conjecture323 (hc : G.Connected) (_hn : 1 < Fintype.card V)
    (h : (maxEdgeNeighborhood Gᶜ : ℤ) ≤ 1 + maxSignedScore G hc.nonempty) :
    WellTotalDominated G := by
  haveI := hc.nonempty
  obtain ⟨r,_,hr⟩ := exists_mem_eq_sup' (univ_nonempty : (univ : Finset V).Nonempty) (signedScore G)
  change maxSignedScore G hc.nonempty = signedScore G r at hr
  exact structural G r hc (hr ▸ h)

omit [Fintype V] in
/-- The separate complete-graph case, for the convention where the
catalogue maximum is undefined on an empty complement. -/
theorem complete_wellTotalDominated (hc : G.Connected)
    (he : ¬ ∃ u v, Gᶜ.Adj u v) : WellTotalDominated G := by
  obtain ⟨v⟩ := hc.nonempty
  apply wtd_of_pairs G v
  intro D hD
  obtain ⟨a,ha,b,hb,hab⟩ := dominates_two G hD v
  refine ⟨a,b,hab,insert_subset ha (singleton_subset_iff.mpr hb),?_⟩
  intro x
  by_cases h : x = a
  · subst x
    exact ⟨b,by simp,hab⟩
  · have hxa : G.Adj x a := Classical.byContradiction fun hn => he ⟨x,a,h,hn⟩
    exact ⟨a,by simp,hxa⟩

#print axioms conjecture323
#print axioms complete_wellTotalDominated
#print axioms max_attained
end
end Graffiti323
