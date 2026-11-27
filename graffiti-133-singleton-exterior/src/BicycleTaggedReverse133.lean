import BicycleTaggedChannels133

namespace Graffiti133Bicycle
open SimpleGraph Graffiti133 Graffiti133Camby
set_option linter.unusedSectionVars false
variable {V : Type*} {G : SimpleGraph V} {B S : Finset V} {a : V}

def TaggedChannel.reverse (P : TaggedChannel G B S a) (aB : a∈B) :
    TaggedChannel G B S P.b where
  n := P.n
  pos := P.pos
  f := P.f ∘ Fin.rev
  path := by classical exact reverse_path P.path
  spans := P.spans.comp Fin.rev_involutive.surjective
  b := a
  bIn := aB
  singletonNe := fun e => (P.singletonNe e).symm
  attached := by
    intro i z zB
    change G.Adj z (P.f (Fin.rev i)).val ↔ _
    rw [P.attached _ z zB]
    have ij : (Fin.rev i).val = P.n-1-i.val := by rw [Fin.val_rev]; omega
    rw [ij]
    have ib := i.isLt
    constructor
    · rintro (⟨h,e⟩|⟨h,e⟩)
      · exact Or.inr ⟨by omega,e⟩
      · exact Or.inl ⟨by omega,e⟩
    · rintro (⟨h,e⟩|⟨h,e⟩)
      · exact Or.inr ⟨by omega,e⟩
      · exact Or.inl ⟨by omega,e⟩

#print axioms TaggedChannel.reverse
end Graffiti133Bicycle
