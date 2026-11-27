import BicycleTwoBranchPartition133
import BicycleTaggedReverse133

namespace Graffiti133Bicycle
open SimpleGraph Graffiti133 Finset
open scoped Classical
set_option linter.unusedSectionVars false
variable {V : Type*} {G : SimpleGraph V}

structure Relay (G : SimpleGraph V) (B : Finset V) (a b : V) where
  n : Nat
  f : Fin n → V
  path : InducedPath G f
  off : ∀ i, f i∉B
  attached : ∀ i z, z∈B → (G.Adj z (f i) ↔ (i.val=0 ∧ z=a) ∨ (i.val+1=n ∧ z=b))

def Relay.empty (G : SimpleGraph V) (B : Finset V) (a b : V) : Relay G B a b :=
  ⟨0,Fin.elim0,⟨fun i => i.elim0,fun i => i.elim0⟩,fun i => i.elim0,fun i => i.elim0⟩

def Relay.Separated {B : Finset V} {a b c d : V}
    (P : Relay G B a b) (Q : Relay G B c d) : Prop :=
  ∀ i j, P.f i≠Q.f j ∧ ¬G.Adj (P.f i) (Q.f j)

theorem Relay.Separated.symm {B : Finset V} {a b c d : V}
    {P : Relay G B a b} {Q : Relay G B c d} (h : P.Separated Q) : Q.Separated P := by
  intro i j
  exact ⟨(h j i).1.symm,fun e => (h j i).2 e.symm⟩

private def TaggedChannel.relay {B S : Finset V} {a : V}
    (P : TaggedChannel G B S a) (sep : Disjoint S B) :
    Relay G B a P.b :=
  ⟨P.n,Subtype.val ∘ P.f,⟨Subtype.val_injective.comp P.path.1,P.path.2⟩,
    fun i h=>Finset.disjoint_left.mp sep (P.f i).property h,P.attached⟩

structure OwnedRelay (G : SimpleGraph V) (B S : Finset V) (a b : V) where
  relay : Relay G B a b
  pos : 0<relay.n
  owned : ∀ i, relay.f i∈S

def OwnedRelay.retag {B S : Finset V} {a b a' b' : V}
    (P : OwnedRelay G B S a b) (ha : a=a') (hb : b=b') : OwnedRelay G B S a' b' := by
  cases ha
  cases hb
  exact P

@[simp] theorem OwnedRelay.retag_n {B S : Finset V} {a b a' b' : V}
    (P : OwnedRelay G B S a b) (ha : a=a') (hb : b=b') :
    (P.retag ha hb).relay.n=P.relay.n := by cases ha; cases hb; rfl

private def TaggedChannel.ownedRelay {B S : Finset V} {a : V}
    (P : TaggedChannel G B S a) (sep : Disjoint S B) : OwnedRelay G B S a P.b :=
  ⟨P.relay sep,P.pos,fun i => (P.f i).property⟩

noncomputable def TaggedFamily.loopRelay {B : Finset V} (F : TaggedFamily G B)
    (z : V) (S : {S // S∈F.sets}) (h : S∈F.loopsAt z) :
    OwnedRelay G B S.val z z := by
  classical
  have eq : F.head S=z ∧ (F.channel S).b=z := (Finset.mem_filter.mp h).2
  exact ((F.channel S).ownedRelay (F.avoid _ S.property)).retag eq.1 eq.2

theorem TaggedFamily.loopRelay_long {B : Finset V} (F : TaggedFamily G B)
    (z : V) (S : {S // S∈F.sets}) (h : S∈F.loopsAt z) :
    2≤ (F.loopRelay z S h).relay.n := by
  classical
  have eq : F.head S=z ∧ (F.channel S).b=z := (Finset.mem_filter.mp h).2
  have npos := (F.channel S).pos
  have neq : (F.channel S).n≠1 := fun e => (F.channel S).singletonNe e (eq.2.trans eq.1.symm)
  unfold TaggedFamily.loopRelay
  rw [OwnedRelay.retag_n]
  change 2≤(F.channel S).n
  omega

noncomputable def TaggedFamily.crossRelay {u v : V}
    (F : TaggedFamily G ({u,v} : Finset V)) (S : {S // S∈F.sets}) (h : S∈F.crosses) :
    OwnedRelay G ({u,v} : Finset V) S.val u v := by
  classical
  let P := F.channel S
  have nea : F.head S≠P.b := (Finset.mem_filter.mp h).2
  have al : F.head S=u ∨ F.head S=v := by simpa using F.head_mem S
  have bl : P.b=u ∨ P.b=v := by simpa using P.bIn
  by_cases aa : F.head S=u
  · have bb : P.b=v := by
      rcases bl with b|b
      · exact (nea (aa.trans b.symm)).elim
      · exact b
    have eq : OwnedRelay G ({u,v} : Finset V) S.val (F.head S) P.b = OwnedRelay G ({u,v} : Finset V) S.val u v := congrArg₂ (fun x y => OwnedRelay G ({u,v} : Finset V) S.val x y) aa bb
    exact cast eq (P.ownedRelay (F.avoid _ S.property))
  · have ab : F.head S=v := al.resolve_left aa
    have ba : P.b=u := by
      rcases bl with b|b
      · exact b
      · exact (nea (ab.trans b.symm)).elim
    let Q := P.reverse (F.head_mem S)
    have bq : Q.b=v := ab
    have eq : OwnedRelay G ({u,v} : Finset V) S.val P.b Q.b = OwnedRelay G ({u,v} : Finset V) S.val u v := congrArg₂ (fun x y => OwnedRelay G ({u,v} : Finset V) S.val x y) ba bq
    exact cast eq (Q.ownedRelay (F.avoid _ S.property))

theorem TaggedFamily.relays_separate {B : Finset V} (F : TaggedFamily G B)
    {S T : {S // S∈F.sets}} (ne : S≠T) {a b c d : V}
    (P : OwnedRelay G B S.val a b) (Q : OwnedRelay G B T.val c d) :
    P.relay.Separated Q.relay := by
  intro i j
  have diff : S.val≠T.val := fun e => ne (Subtype.ext e)
  refine ⟨fun e=>?_,F.noEdges _ S.property _ T.property diff _ (P.owned i) _ (Q.owned j)⟩
  exact Finset.disjoint_left.mp (F.separate _ S.property _ T.property diff)
    (e ▸ P.owned i) (Q.owned j)

#print axioms TaggedFamily.crossRelay
#print axioms TaggedFamily.relays_separate
end Graffiti133Bicycle
