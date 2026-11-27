import CutTorsoBudget
import MinimumContraction

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

universe u
variable {V : Type u} {G : SimpleGraph V} {D : Finset V} {B : Set V}

private theorem card_kept_gt [Fintype (Bᶜ : Set V)]
    (ports : ∀ d ∈ D, d ∉ B) (witness : ∃ x ∉ B, x ∉ D) :
    D.card < Fintype.card (Bᶜ : Set V) := by
  classical
  obtain ⟨x,xB,xD⟩ := witness
  let S := insert x D
  let f : S → (Bᶜ : Set V) := fun y =>
    ⟨y.val,(Finset.mem_insert.mp y.property).elim (fun h => h.symm ▸ xB) (ports y.val)⟩
  have injective : Function.Injective f := fun _ _ e => Subtype.ext (congrArg (fun x : (Bᶜ : Set V) => x.val) e)
  have le := Fintype.card_le_of_injective f injective
  rw [Fintype.card_coe,show S.card = D.card+1 by exact Finset.card_insert_of_not_mem xD] at le
  omega

/-- A smaller completed shore already has a spanning path. No global
surviving-edge crossing premise is used. -/
theorem traceable_cutTorso_of_smaller [Fintype V] [Fintype (Bᶜ : Set V)]
    (smaller : SmallerAtThree.{u} (Fintype.card V))
    (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5)
    (size : D.card = 3) (ports : ∀ d ∈ D, d ∉ B) (boundary : ShoreBoundary G D B)
    (discarded : (G.induce B).Connected) (kept : ∃ x ∉ B, x ∉ D) :
    Traceable (cutTorso G D B) := by
  classical
  obtain ⟨b⟩ := discarded.nonempty
  have bB : b.val ∈ B := b.property
  have less : Fintype.card (Bᶜ : Set V) < Fintype.card V :=
    Fintype.card_subtype_lt (p := fun x : V => x ∈ Bᶜ) (x := b.val) (not_not_intro bB)
  exact smaller _ _ less
    (cutTorso_connectivity conn size.ge (size ▸ card_kept_gt ports kept) ports boundary)
    ((cutTorso_treeNumber_le boundary discarded.preconnected
      (fun _ hd => contact_of_shore conn size.le ports boundary ⟨b.val,bB⟩ hd)).trans budget)

/-- A three-cut into two connected shores gives two smaller traceable
graphs after completing the separator. -/
theorem traceable_both_cutTorsos_of_smaller [Fintype V] {A : Set V}
    [Fintype (Aᶜ : Set V)] [Fintype (Bᶜ : Set V)]
    (smaller : SmallerAtThree.{u} (Fintype.card V))
    (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5)
    (size : D.card = 3)
    (portsA : ∀ d ∈ D, d ∉ A) (portsB : ∀ d ∈ D, d ∉ B)
    (separate : Disjoint A B)
    (crossA : ShoreBoundary G D A) (crossB : ShoreBoundary G D B)
    (connA : (G.induce A).Connected) (connB : (G.induce B).Connected) :
    Traceable (cutTorso G D A) ∧ Traceable (cutTorso G D B) := by
  obtain ⟨a⟩ := connA.nonempty
  obtain ⟨b⟩ := connB.nonempty
  have apart := Set.disjoint_left.mp separate
  exact ⟨traceable_cutTorso_of_smaller smaller conn budget size portsA crossA connA
      ⟨b.val,fun ha => apart ha b.property,fun hd => portsB _ hd b.property⟩,
    traceable_cutTorso_of_smaller smaller conn budget size portsB crossB connB
      ⟨a.val,apart a.property,fun hd => portsA _ hd a.property⟩⟩

#print axioms traceable_cutTorso_of_smaller
#print axioms traceable_both_cutTorsos_of_smaller

end Graffiti199Depleted.Catalogue
