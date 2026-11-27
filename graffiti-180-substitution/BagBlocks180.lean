import Inflate180

set_option warningAsError true
namespace Minimal180.Substitution
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
open Classical
variable {V B : Type*} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]
variable {H : SimpleGraph V} {G : SimpleGraph B} {f : V→B}

omit [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B] in
theorem Bags.preDown (h : Bags H G f) (pre : H.Preconnected) : G.Preconnected := by
  have proj {u v : V} (w : H.Walk u v) : G.Reachable (f u) (f v) := by
    induction w with
    | nil => exact .refl _
    | @cons u x _ e _ ih =>
      by_cases eq : f u=f x
      · exact eq ▸ ih
      · exact ((h.across eq).mp e).reachable.trans ih
  intro i j
  obtain ⟨x,rfl⟩ := h.onto i
  obtain ⟨y,rfl⟩ := h.onto j
  obtain ⟨w⟩ := pre x y
  exact proj w

omit [Fintype V] [DecidableEq V] [DecidableEq B] in
/-- A vertex is a cut vertex of a substitution exactly when its bag is
a singleton and its image is a cut vertex of the base. The base has
order at least three, and every bag is an arbitrary nonempty graph. -/
theorem Bags.delete_pre_iff (h : Bags H G f) (gc : G.Connected) (hn : 2<Fintype.card B) (v : V) :
    (H.induce ({v}ᶜ : Set V)).Preconnected ↔
      (∃ w,w≠v ∧ f w=f v) ∨ (G.induce ({f v}ᶜ : Set B)).Preconnected := by
  classical
  let H' := H.induce ({v}ᶜ : Set V)
  let J := G.induce ({f v}ᶜ : Set B)
  by_cases other : ∃ w,w≠v ∧ f w=f v
  · refine ⟨fun _ => Or.inl other,fun _ => ?_⟩
    obtain ⟨w,wv,eq⟩ := other
    let q (x : ({v}ᶜ : Set V)) := f x.val
    have sub : Bags H' G q := by
      refine ⟨fun i => ?_,fun {x y} ne => h.across ne⟩
      obtain ⟨z,fz⟩ := h.onto i
      by_cases same : z=v
      · exact ⟨⟨w,wv⟩,eq.trans (same ▸ fz)⟩
      · exact ⟨⟨z,same⟩,fz⟩
    exact (sub.connected gc (by omega)).preconnected
  · have off (x : ({v}ᶜ : Set V)) : f x.val≠f v := fun eq => other ⟨x.val,x.property,eq⟩
    let q (x : ({v}ᶜ : Set V)) : ({f v}ᶜ : Set B) := ⟨f x.val,off x⟩
    have sub : Bags H' J q := by
      refine ⟨fun i => ?_,fun {x y} ne => h.across (fun eq => ne (Subtype.ext eq))⟩
      obtain ⟨z,fz⟩ := h.onto i.val
      have zv : z≠v := fun e => i.property (show i.val=f v from fz.symm.trans (congrArg f e))
      exact ⟨⟨z,zv⟩,Subtype.ext fz⟩
    have card : Fintype.card ↥({f v}ᶜ : Set B)=(univ.erase (f v)).card :=
      Fintype.card_of_subtype _ (fun x => by simp)
    rw [card_erase_of_mem (mem_univ _),card_univ] at card
    have enough : 1<Fintype.card ↥({f v}ᶜ : Set B) := by omega
    constructor
    · exact fun pre => Or.inr (sub.preDown pre)
    · intro choice
      have jc : J.Connected := J.connected_iff.mpr ⟨choice.resolve_left other,Fintype.card_pos_iff.mp (by omega)⟩
      exact (sub.connected jc enough).preconnected

omit [Fintype V] [DecidableEq V] [DecidableEq B] in
theorem Bags.noCut (h : Bags H G f) (gc : G.Connected) (hn : 2<Fintype.card B) (nc : NoCut G) : NoCut H :=
  fun v => (h.delete_pre_iff gc hn v).mpr (Or.inr (nc (f v)))

/-- Biconnected bipartite bases yield certified biconnected examples of
every prescribed bipartization deficit, with all old distances and all
old degrees outside the closed neighborhood of the expanded vertex preserved. -/
theorem grow_blocks (G : SimpleGraph B) (gc : G.Connected) (hn : 2<Fintype.card B) (nc : NoCut G)
    (bi : TwoColor G univ) (c : B) (k : ℕ) :
    let H := growClique G c k
    H.Connected ∧ NoCut H ∧ Fintype.card (B⊕Fin k)-bipartiteNum H=k ∧
      (∀ x y,H.dist (.inl x) (.inl y)=G.dist x y) ∧
      (∀ x,x≠c → ¬G.Adj x c → H.degree (.inl x)=G.degree x) ∧
      (∀ r p,localBound H r (parity H r p)) ∧
      1+independence H+Graffiti318.maxEven H≤maxLeaves H+bipartiteNum H := by
  intro H
  obtain ⟨con,rank,rooted,ordinary⟩ := grow_certified G gc (by omega) bi c k
  exact ⟨con,(grow_bags G c k).noCut gc hn nc,rank,grow_dist G gc c k,grow_degree G c k,rooted,ordinary⟩

#print axioms Bags.preDown
#print axioms Bags.delete_pre_iff
#print axioms Bags.noCut
#print axioms grow_blocks
end Minimal180.Substitution
