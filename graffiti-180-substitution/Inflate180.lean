import OneClique180

set_option warningAsError true
namespace Minimal180.Substitution
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
open Classical
variable {B : Type*} [Fintype B] [DecidableEq B] (G : SimpleGraph B)

noncomputable def foldCopies (c : B) (k : ℕ) : B⊕Fin k→B := Sum.elim id (fun _ => c)

/-- Add k true twins of c. The bag consisting of c and the copies is
a clique of order k+1. -/
noncomputable def growClique (c : B) (k : ℕ) : SimpleGraph (B⊕Fin k) where
  Adj x y := G.Adj (foldCopies c k x) (foldCopies c k y) ∨
    (foldCopies c k x=foldCopies c k y ∧ x≠y)
  symm := fun _ _ e => e.imp (fun h => h.symm) (fun h => ⟨h.1.symm,h.2.symm⟩)
  loopless := fun _ e => e.elim (G.loopless _) (fun h => h.2 rfl)

omit [Fintype B] [DecidableEq B] in
theorem grow_bags (c : B) (k : ℕ) : Bags (growClique G c k) G (foldCopies c k) := by
  refine ⟨fun i => ⟨.inl i,rfl⟩,fun {x y} ne => ?_⟩
  exact ⟨fun e => e.elim id (fun eq => (ne eq.1).elim),Or.inl⟩

omit [Fintype B] [DecidableEq B] in
/-- Distances between all original vertices survive exactly. -/
theorem grow_dist (gc : G.Connected) (c : B) (k : ℕ) (a b : B) :
    (growClique G c k).dist (.inl a) (.inl b)=G.dist a b :=
  (grow_bags G c k).repDist gc Sum.inl (fun _ => rfl) a b

/-- Every old vertex outside the closed neighborhood of c keeps its
degree, in particular all degree-two vertices there. -/
theorem grow_degree (c : B) (k : ℕ) (x : B) (xc : x≠c) (no : ¬G.Adj x c) :
    (growClique G c k).degree (.inl x)=G.degree x := by
  classical
  have nb : (growClique G c k).neighborFinset (.inl x)=(G.neighborFinset x).image Sum.inl := by
    ext z
    cases z with
    | inl y =>
      simp only [mem_neighborFinset,mem_image]
      change (G.Adj x y ∨ (x=y ∧ (Sum.inl x:B⊕Fin k)≠.inl y)) ↔ _
      constructor
      · rintro (edge|⟨eq,ne⟩)
        · exact ⟨y,edge,rfl⟩
        · exact (ne (congrArg Sum.inl eq)).elim
      · rintro ⟨w,edge,eq⟩
        exact Or.inl (Sum.inl.inj eq ▸ edge)
    | inr j =>
      simp only [mem_neighborFinset,mem_image]
      change (G.Adj x c ∨ (x=c ∧ _)) ↔ _
      simp [no,xc]
  rw [←card_neighborFinset_eq_degree,nb,card_image_of_injective _ Sum.inl_injective,card_neighborFinset_eq_degree]

/-- Over any connected nontrivial bipartite base, the k-copy graph has
deficit exactly k and satisfies every rooted inequality and ordinary
Graffiti.pc 180. There is no upper bound on k. -/
theorem grow_certified (gc : G.Connected) (hn : 1<Fintype.card B) (bi : TwoColor G univ)
    (c : B) (k : ℕ) :
    let H := growClique G c k
    H.Connected ∧ Fintype.card (B⊕Fin k)-bipartiteNum H=k ∧
      (∀ r p,localBound H r (parity H r p)) ∧
      1+independence H+Graffiti318.maxEven H≤maxLeaves H+bipartiteNum H := by
  intro H
  have bags := grow_bags G c k
  have cl (x y : B⊕Fin k) (fx : foldCopies c k x=c) (fy : foldCopies c k y=c) (ne : x≠y) :
      H.Adj x y := Or.inr ⟨fx.trans fy.symm,ne⟩
  have single (x y : B⊕Fin k) (eq : foldCopies c k x=foldCopies c k y) (off : foldCopies c k x≠c) : x=y := by
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl eq
      | inr _ => exact (off eq).elim
    | inr _ => exact (off rfl).elim
  have ⟨rank,rooted,ordinary⟩ := bags.oneCliqueDeficit gc hn bi c cl single
  exact ⟨bags.connected gc hn,by simpa only [Fintype.card_sum,Fintype.card_fin,Nat.add_sub_cancel_left] using rank,rooted,ordinary⟩

#print axioms grow_dist
#print axioms grow_degree
#print axioms grow_certified
end Minimal180.Substitution
