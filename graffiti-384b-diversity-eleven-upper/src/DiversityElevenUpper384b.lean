import DiversityElevenProfile384b
import FixedCubics
import UpperClique

namespace Graffiti384b.DiversityEleven
open Finset SimpleGraph OddStars OddStars.LeafCritical
open private OddStars.LeafCritical.balance_max from LeafCritical
open private OddStars.ShoreCounts.in_high from ShoreCounts
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The upper, ten-nonleaf residual needs only the ten high vertices;
all its transported structural conditions also hold for disconnected
ambient graphs, including isolated zero-score witnesses. -/
theorem upper_ten (t : (types G).card=11) (bad : bound G<gamma G)
    (ten : (high (patch G ∅)).card=10) :
    let J := patch G ∅
    let H := high J
    nonleaves J=H ∧ Set.InjOn (trianglesAt J) (H : Set V) ∧
      (∀ x∈H, 2≤trianglesAt J x) ∧ (∀ C,¬J.IsNClique 5 C) ∧
      ∃ u v : V, u≠v ∧ trianglesAt J u=2 ∧ trianglesAt J v=3 ∧ ¬J.Adj u v ∧
        (∀ x,J.degree x=3 ↔ x=u ∨ x=v) ∧
        ∀ A : Finset V, Maximum J A → critical J A={u,v} ∧ (H∩A).card=5 := by
  let J := patch G ∅
  let H := high J
  have size : H.card+1=(types G).card := by change H.card=10 at ten; omega
  have nonempty : H.Nonempty := card_pos.mp (by change H.card=10 at ten; omega)
  have profile := PendantAudit.upper_branch G bad size
  have inside : nonleaves J=H := by
    apply Finset.Subset.antisymm
    · intro x hx
      have deg : 2≤J.degree x := (mem_filter.mp hx).2
      obtain ⟨y,xy⟩ := (J.degree_pos_iff_exists_adj x).mp (by omega)
      have lo := skeleton_degree_bound G x
      change J.degree x≤_ at lo
      exact profile.1 x (by omega)
    · intro x hx
      have deg : 3≤J.degree x := (mem_filter.mp hx).2
      exact mem_filter.mpr ⟨mem_univ _,by omega⟩
  have pos (x : V) (xh : x∈H) : 2≤trianglesAt J x := by
    have dg : 3≤J.degree x := (mem_filter.mp xh).2
    have lo := skeleton_degree_bound G x
    change J.degree x≤_ at lo
    rw [patch_scores]
    omega
  have scores : Set.InjOn (trianglesAt J) (H : Set V) := by
    intro x hx y hy eq
    have p := pos x hx
    have q := pos y hy
    rw [patch_scores,patch_scores] at eq
    rw [patch_scores] at p q
    exact profile.2.1 (by simpa only [Set.mem_setOf_eq] using (show 0<trianglesAt G x by omega))
      (by simpa only [Set.mem_setOf_eq] using (show 0<trianglesAt G y by omega)) eq
  have sub : J≤G := fun _ _ e=>e.1
  have noFive (C : Finset V) (cl : J.IsNClique 5 C) : False :=
    UpperClique.no_five G bad size C (cl.mono sub)
  obtain ⟨u,v,uv,us,vs,no,pair,crit⟩ := FixedCubics.fixed_pair G bad size nonempty
  refine ⟨inside,scores,pos,noFive,u,v,uv,by simpa [J,patch_scores] using us,
    by simpa [J,patch_scores] using vs,no,pair,?_⟩
  intro A h
  have eq := OddStars.LeafCritical.balance_max G bad size h
  change 2*(H∩A).card=H.card at eq
  change H.card=10 at ten
  refine ⟨crit A h,?_⟩
  change (H∩A).card=5
  omega

#print axioms upper_ten
end Graffiti384b.DiversityEleven
