import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite
import Lean.Elab.Tactic.Omega

/-!
# Written on the Wall II, conjecture 325

For a connected simple graph of order greater than one, compare the
minimum neighborhood size of a complement edge with one plus the
number of components induced by the closed neighborhood of degree-two
vertices. The exact bound implies well total domination.

This is an independent formalization of a result previously established
by Claude Opus 5 at AI Village (graffiti-verification README, section 7fk).
The Lean proof also handles the order-four exception directly and proves
the conclusion for complete graphs, even if the empty minimum is set to zero.

Catalogue: https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf
Checked with Lean 4.19.0 and Mathlib v4.19.0.
-/

namespace Graffiti325
open Finset SimpleGraph
noncomputable section
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
local instance : DecidableEq V := Classical.decEq V
local instance (H : SimpleGraph V) : DecidableRel H.Adj := Classical.decRel H.Adj

def S (v : V) : Prop := (G.neighborFinset v).card = 2

def closedDegreeTwo : Finset V := by
  classical
  exact
  univ.filter fun v => S G v ∨ ∃ s, S G s ∧ G.Adj v s

private theorem mem_closed (v : V) :
    v ∈ closedDegreeTwo G ↔ S G v ∨ ∃ s, S G s ∧ G.Adj v s := by
  classical
  simp [closedDegreeTwo]

def induced : SimpleGraph ↑(closedDegreeTwo G : Set V) :=
  G.induce (closedDegreeTwo G : Set V)

instance : Finite (induced G).ConnectedComponent :=
  Finite.of_surjective (induced G).connectedComponentMk (fun c => c.exists_rep)

noncomputable instance : Fintype (induced G).ConnectedComponent := Fintype.ofFinite _

def componentCount : ℕ := Fintype.card (induced G).ConnectedComponent

def edgeNeighborhood (u v : V) : Finset V :=
  Gᶜ.neighborFinset u ∪ Gᶜ.neighborFinset v

private theorem endpoints_mem {u v : V} (h : Gᶜ.Adj u v) :
    u ∈ edgeNeighborhood G u v ∧ v ∈ edgeNeighborhood G u v := by
  exact ⟨mem_union_right _ ((Gᶜ.mem_neighborFinset v u).mpr h.symm),
    mem_union_left _ ((Gᶜ.mem_neighborFinset u v).mpr h)⟩

private theorem adj_of_not_mem {u v w : V} (h : Gᶜ.Adj u v)
    (hw : w ∉ edgeNeighborhood G u v) : G.Adj u w ∧ G.Adj v w := by
  have he := endpoints_mem G h
  have hwu : w ≠ u := fun e => hw (e ▸ he.1)
  have hwv : w ≠ v := fun e => hw (e ▸ he.2)
  constructor
  · by_contra hn
    exact hw (mem_union_left _ ((Gᶜ.mem_neighborFinset u w).mpr ⟨hwu.symm,hn⟩))
  · by_contra hn
    exact hw (mem_union_right _ ((Gᶜ.mem_neighborFinset v w).mpr ⟨hwv.symm,hn⟩))

private theorem component_rep (c : (induced G).ConnectedComponent) :
    ∃ s : ↑(closedDegreeTwo G : Set V), S G s.1 ∧ (induced G).connectedComponentMk s = c := by
  obtain ⟨x,hx⟩ := c.exists_rep
  rcases (mem_closed G x.1).mp x.2 with h | ⟨s,hs,had⟩
  · exact ⟨x,h,hx⟩
  · let s' : ↑(closedDegreeTwo G : Set V) := ⟨s,(mem_closed G s).mpr (Or.inl hs)⟩
    have hxs : (induced G).Adj x s' := had
    exact ⟨s',hs,(ConnectedComponent.connectedComponentMk_eq_of_adj hxs).symm.trans hx⟩

private theorem neighbors_of_rep {s x : V} (hs : S G s) (hx : G.Adj s x) :
    x ∈ closedDegreeTwo G :=
  (mem_closed G x).mpr (Or.inr ⟨s,hs,hx.symm⟩)

private theorem rep_triple (c : (induced G).ConnectedComponent) :
    ∃ a b d : ↑(closedDegreeTwo G : Set V), a.1 ≠ b.1 ∧ a.1 ≠ d.1 ∧ b.1 ≠ d.1 ∧
      (induced G).connectedComponentMk a = c ∧
      (induced G).connectedComponentMk b = c ∧
      (induced G).connectedComponentMk d = c := by
  obtain ⟨s,hs,hsc⟩ := component_rep G c
  obtain ⟨x,y,hxy,hpair⟩ := card_eq_two.mp hs
  have hx : G.Adj s.1 x := (G.mem_neighborFinset s.1 x).mp (by rw [hpair]; simp)
  have hy : G.Adj s.1 y := (G.mem_neighborFinset s.1 y).mp (by rw [hpair]; simp)
  let x' : ↑(closedDegreeTwo G : Set V) := ⟨x,neighbors_of_rep G hs hx⟩
  let y' : ↑(closedDegreeTwo G : Set V) := ⟨y,neighbors_of_rep G hs hy⟩
  have hx' : (induced G).Adj s x' := hx
  have hy' : (induced G).Adj s y' := hy
  exact ⟨s,x',y',hx.ne,hy.ne,hxy,hsc,
    (ConnectedComponent.connectedComponentMk_eq_of_adj hx').symm.trans hsc,
    (ConnectedComponent.connectedComponentMk_eq_of_adj hy').symm.trans hsc⟩

private theorem reps_injective (f : (induced G).ConnectedComponent →
    ↑(closedDegreeTwo G : Set V))
    (hf : ∀ c, (induced G).connectedComponentMk (f c) = c) :
    Function.Injective (fun c => (f c).1) := by
  intro a b h
  have he : f a = f b := Subtype.ext h
  rw [← hf a, ← hf b, he]

private theorem one_component {u v : V} (h : Gᶜ.Adj u v)
    (hbound : (edgeNeighborhood G u v).card ≤ componentCount G + 1) :
    componentCount G = 1 := by
  classical
  let X := closedDegreeTwo G
  let H := induced G
  let B := edgeNeighborhood G u v
  have hB := endpoints_mem G h
  choose s hs hsC using component_rep G
  have hi := reps_injective G s hsC
  have at_endpoint (w : V) (hw : w ∈ X)
      (hall : ∀ x : V, x ∉ B → G.Adj w x)
      (hwB : w ∈ B) : componentCount G = 1 := by
    let w' : ↑(X : Set V) := ⟨w,hw⟩
    let cw := H.connectedComponentMk w'
    have hnot (x : ↑(X : Set V)) (hx : H.connectedComponentMk x ≠ cw) : x.1 ∈ B := by
      by_contra hmem
      have had : H.Adj w' x := hall x.1 hmem
      exact hx (ConnectedComponent.connectedComponentMk_eq_of_adj had.symm)
    let f (c : H.ConnectedComponent) := if c = cw then w' else s c
    have hf (c : H.ConnectedComponent) : H.connectedComponentMk (f c) = c := by
      by_cases he : c = cw
      · simp [f, he, cw]
      · simpa [f, he] using hsC c
    let R : Finset V := univ.image (fun c => (f c).1)
    have hR : R.card = componentCount G := by
      unfold R componentCount
      rw [card_image_of_injective _ (reps_injective G f hf), card_univ]
    have hRB : R ⊆ B := by
      intro x hx
      obtain ⟨c,_,rfl⟩ := mem_image.mp hx
      by_cases he : c = cw
      · simpa [f, he] using hwB
      · exact hnot _ (fun hb => he ((hf c).symm.trans hb))
    by_contra hne
    have hother : ∃ c : H.ConnectedComponent, c ≠ cw := by
      by_contra hn
      push_neg at hn
      letI : Unique H.ConnectedComponent := ⟨⟨cw⟩,hn⟩
      exact hne (Fintype.card_unique)
    obtain ⟨c,hc⟩ := hother
    obtain ⟨a,b,d,hab,had,hbd,ha,hb,hd⟩ := rep_triple G c
    have htwo : ∃ y z : ↑(X : Set V), y.1 ≠ z.1 ∧
        H.connectedComponentMk y = c ∧ H.connectedComponentMk z = c ∧
        y.1 ≠ (f c).1 ∧ z.1 ≠ (f c).1 := by
      by_cases hfa : a.1 = (f c).1
      · exact ⟨b,d,hbd,hb,hd,by rwa [← hfa,ne_comm],by rwa [← hfa,ne_comm]⟩
      by_cases hfb : b.1 = (f c).1
      · exact ⟨a,d,had,ha,hd,hfa,by rwa [← hfb,ne_comm]⟩
      · exact ⟨a,b,hab,ha,hb,hfa,hfb⟩
    obtain ⟨y,z,hyz,hy,hz,hyf,hzf⟩ := htwo
    have outside (x : ↑(X : Set V)) (hx : H.connectedComponentMk x = c)
        (hn : x.1 ≠ (f c).1) : x.1 ∉ R := by
      intro hm
      obtain ⟨k,_,hk⟩ := mem_image.mp hm
      have he : f k = x := Subtype.ext hk
      have hk' : k = c := by rw [← hf k, he, hx]
      exact hn (by simpa [hk'] using hk.symm)
    have hyR := outside y hy hyf
    have hzR := outside z hz hzf
    have hsub : insert y.1 (insert z.1 R) ⊆ B :=
      insert_subset (hnot _ (hy ▸ hc)) (insert_subset (hnot _ (hz ▸ hc)) hRB)
    have hc' := card_le_card hsub
    rw [card_insert_of_not_mem (by simp [hyz,hyR]), card_insert_of_not_mem hzR, hR] at hc'
    change B.card ≤ componentCount G + 1 at hbound
    omega
  by_cases hu : u ∈ X
  · exact at_endpoint u hu (fun x hx => (adj_of_not_mem G h hx).1) hB.1
  by_cases hv : v ∈ X
  · exact at_endpoint v hv (fun x hx => (adj_of_not_mem G h hx).2) hB.2
  let R := univ.image (fun c => (s c).1)
  have hR : R.card = componentCount G := by
    unfold R componentCount
    rw [card_image_of_injective _ hi, card_univ]
  have hRB : R ⊆ B := by
    intro x hx
    obtain ⟨c,_,rfl⟩ := mem_image.mp hx
    exact Classical.byContradiction fun hmem =>
      hu (neighbors_of_rep G (hs c) (adj_of_not_mem G h hmem).1.symm)
  have hout (x : V) (hx : x ∉ X) : x ∉ R := by
    intro hm
    obtain ⟨c,_,rfl⟩ := mem_image.mp hm
    exact hx (s c).2
  have sub : insert u (insert v R) ⊆ B :=
    insert_subset hB.1 (insert_subset hB.2 hRB)
  have hcard := card_le_card sub
  rw [card_insert_of_not_mem (by simp [h.ne,hout u hu]),
    card_insert_of_not_mem (hout v hv), hR] at hcard
  change B.card ≤ componentCount G + 1 at hbound
  omega

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
private theorem pair_dom {u v a : V} (h : Gᶜ.Adj u v)
    (hall : ∀ x, x ≠ u → x ≠ v → G.Adj u x ∧ G.Adj v x)
    (hau : a ≠ u) (hav : a ≠ v) : TotalDominates G {u,a} := by
  intro x
  rcases eq_or_ne x u with rfl | hxu
  · exact ⟨a,by simp,(hall a hau hav).1⟩
  rcases eq_or_ne x v with rfl | hxv
  · exact ⟨a,by simp,(hall a hau hav).2⟩
  exact ⟨u,by simp,(hall x hxu hxv).1.symm⟩

private theorem fixed_edge {u v : V} (h : Gᶜ.Adj u v)
    (hbound : (edgeNeighborhood G u v).card ≤ componentCount G + 1) :
    WellTotalDominated G := by
  classical
  have hcount := one_component G h hbound
  have hvu := endpoints_mem G h
  have hsub : ({u,v} : Finset V) ⊆ edgeNeighborhood G u v :=
    insert_subset hvu.1 (singleton_subset_iff.mpr hvu.2)
  have hEq : edgeNeighborhood G u v = {u,v} := by
    apply (eq_of_subset_of_card_le hsub ?_).symm
    simpa [h.ne,hcount] using hbound
  have hall (x : V) (hu : x ≠ u) (hv : x ≠ v) : G.Adj u x ∧ G.Adj v x :=
    adj_of_not_mem G h (by simp [hEq,hu,hv])
  have hmem : Nonempty (induced G).ConnectedComponent :=
    Fintype.card_pos_iff.mp (by change 0 < componentCount G; omega)
  obtain ⟨c⟩ := hmem
  obtain ⟨s,hs,_⟩ := component_rep G c
  apply wtd_of_pairs G u
  intro D hD
  have using_endpoint {w z : V} (hwz : Gᶜ.Adj w z)
      (hall' : ∀ x, x ≠ w → x ≠ z → G.Adj w x ∧ G.Adj z x)
      (hm : w ∈ D) : ∃ a b, G.Adj a b ∧ ({a,b} : Finset V) ⊆ D ∧ TotalDominates G {a,b} := by
    obtain ⟨a,ha,hwa⟩ := hD w
    exact ⟨w,a,hwa,insert_subset hm (singleton_subset_iff.mpr ha),
      pair_dom G hwz hall' hwa.ne.symm (fun e => hwz.2 (e ▸ hwa))⟩
  by_cases hu : u ∈ D
  · exact using_endpoint h hall hu
  by_cases hv : v ∈ D
  · exact using_endpoint h.symm (fun x hxv hxu => ⟨(hall x hxu hxv).2,(hall x hxu hxv).1⟩) hv
  have hDne (x : V) (hx : x ∈ D) : x ≠ u ∧ x ≠ v :=
    ⟨fun e => hu (e ▸ hx),fun e => hv (e ▸ hx)⟩
  have hnot (x : V) (hx : S G x) (hxu : x ≠ u) (hxv : x ≠ v) : False := by
    have hin : ({u,v} : Finset V) ⊆ G.neighborFinset x :=
      insert_subset ((G.mem_neighborFinset _ _).mpr (hall x hxu hxv).1.symm)
        (singleton_subset_iff.mpr ((G.mem_neighborFinset _ _).mpr (hall x hxu hxv).2.symm))
    have he : ({u,v} : Finset V) = G.neighborFinset x :=
      eq_of_subset_of_card_le hin (by simpa [h.ne] using hx.le)
    obtain ⟨y,hy,hxy⟩ := hD x
    have hyt := (G.mem_neighborFinset _ _).mpr hxy
    rw [← he] at hyt
    simp [(hDne y hy).1,(hDne y hy).2] at hyt
  obtain ⟨a,ha,b,hb,hab⟩ := dominates_two G hD u
  have hallS : s.1 = u ∨ s.1 = v := by
    rcases eq_or_ne s.1 u with hu' | hu'
    · exact Or.inl hu'
    rcases eq_or_ne s.1 v with hv' | hv'
    · exact Or.inr hv'
    exact (hnot _ hs hu' hv').elim
  have hxwide (w : V) (hw : S G w) (hwu : w = u ∨ w = v) :
      G.neighborFinset w = {a,b} := by
    have hadj (x : V) (hx : x ∈ D) : G.Adj w x := by
      rcases hwu with rfl | rfl
      · exact (hall x (hDne x hx).1 (hDne x hx).2).1
      · exact (hall x (hDne x hx).1 (hDne x hx).2).2
    apply (eq_of_subset_of_card_le (insert_subset ((G.mem_neighborFinset _ _).mpr (hadj a ha))
      (singleton_subset_iff.mpr ((G.mem_neighborFinset _ _).mpr (hadj b hb)))) ?_).symm
    simpa [hab.ne] using hw.le
  have hsAB := hxwide s.1 hs hallS
  have hdom : TotalDominates G {a,b} := by
    intro x
    by_cases hxu : x = u
    · subst x
      exact ⟨a,by simp,(hall a (hDne a ha).1 (hDne a ha).2).1⟩
    by_cases hxv : x = v
    · subst x
      exact ⟨a,by simp,(hall a (hDne a ha).1 (hDne a ha).2).2⟩
    have haS : G.Adj s.1 x := by
      rcases hallS with he | he
      · rw [he]; exact (hall x hxu hxv).1
      · rw [he]; exact (hall x hxu hxv).2
    have hxAB := (G.mem_neighborFinset _ _).mpr haS
    rw [hsAB] at hxAB
    rcases (mem_insert.mp hxAB) with rfl | hlast
    · exact ⟨b,by simp,hab⟩
    · have he := mem_singleton.mp hlast
      exact ⟨a,by simp,he.symm ▸ hab.symm⟩
  exact ⟨a,b,hab,insert_subset ha (singleton_subset_iff.mpr hb),hdom⟩

def minEdgeNeighborhood : ℕ :=
  sInf (Set.range fun e : {p : V × V // Gᶜ.Adj p.1 p.2} =>
    (edgeNeighborhood G e.1.1 e.1.2).card)

/-- Exact WOW II #325 for the domain where the minimum exists.
The empty-complement (complete graph) case holds as well under a zero default. -/
theorem conjecture325 (hc : G.Connected) (_hn : 1 < Fintype.card V)
    (hbound : minEdgeNeighborhood G ≤ 1 + componentCount G) : WellTotalDominated G := by
  classical
  by_cases hex : Nonempty {p : V × V // Gᶜ.Adj p.1 p.2}
  · letI := hex
    obtain ⟨e,he⟩ := Nat.sInf_mem
      (Set.range_nonempty (f := fun e : {p : V × V // Gᶜ.Adj p.1 p.2} =>
        (edgeNeighborhood G e.1.1 e.1.2).card))
    apply fixed_edge G e.2
    change (edgeNeighborhood G e.1.1 e.1.2).card = minEdgeNeighborhood G at he
    rw [he,Nat.add_comm]
    exact hbound
  · obtain ⟨v⟩ := hc.nonempty
    apply wtd_of_pairs G v
    have hcomplete (a b : V) (hab : a ≠ b) : G.Adj a b := by
      exact Classical.byContradiction fun hna => hex ⟨⟨(a,b),hab,hna⟩⟩
    intro D hD
    obtain ⟨a,ha,b,hb,hab⟩ := dominates_two G hD v
    refine ⟨a,b,hab,insert_subset ha (singleton_subset_iff.mpr hb),?_⟩
    intro x
    rcases eq_or_ne x a with rfl | hxa
    · exact ⟨b,by simp,hab⟩
    · exact ⟨a,by simp,hcomplete x a hxa⟩

#print axioms conjecture325

end
end Graffiti325
