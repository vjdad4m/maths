import SimplicialCredit30
import EarMixtureRows
namespace Graffiti384b.EarMix
open Finset SimpleGraph Thin28 HighSquare28
open private Repair.nbr_add Repair.triangles_le_choose from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
structure Layout where
  H : Finset V
  W : Finset V
  A : Finset V
  B : Finset V
  C : Finset V
  e : V
  f : V
  g : V
  full : (univ : Finset V)=insert e (insert f (insert g H))
  part : H=W∪(A∪(B∪C))
  ws : W.card=21
  asz : A.card=2
  bsz : B.card=2
  csz : C.card=2
  ew : e∉H
  fw : f∉H
  gw : g∉H
  ef : e≠f
  fg : f≠g
  ge : g≠e
  wa : Disjoint W A
  wb : Disjoint W B
  wc : Disjoint W C
  ab : Disjoint A B
  bc : Disjoint B C
  ca : Disjoint C A
  ea : G.neighborFinset e=A
  fb : G.neighborFinset f=B
  gc : G.neighborFinset g=C
  inj : Set.InjOn (trianglesAt G) (H:Set V)
  rich : ∀v∈H,2≤trianglesAt G v

namespace Layout
variable {G} (M : Layout G)
def rot : Layout G where
  H:=M.H; W:=M.W; A:=M.B; B:=M.C; C:=M.A; e:=M.f; f:=M.g; g:=M.e
  full:=M.full.trans (by simp only [insert_comm])
  part:=M.part.trans (by ac_rfl)
  ws:=M.ws; asz:=M.bsz; bsz:=M.csz; csz:=M.asz
  ew:=M.fw; fw:=M.gw; gw:=M.ew; ef:=M.fg; fg:=M.ge; ge:=M.ef
  wa:=M.wb; wb:=M.wc; wc:=M.wa; ab:=M.bc; bc:=M.ca; ca:=M.ab
  ea:=M.fb; fb:=M.gc; gc:=M.ea; inj:=M.inj; rich:=M.rich

def P := M.A∪{M.f,M.g}
def Q := (M.B∪M.C)∪{M.e}
def trial (F : Finset V→ℕ→V→ℕ) (k l : ℕ) (v : V) := 2*F M.P k v+5*F M.Q l v
def total (F : Finset V→ℕ→V→ℕ) (k l : ℕ) (v : V) :=
  M.trial F k l v+M.rot.trial F k l v+M.rot.rot.trial F k l v
theorem rotate (F : Finset V→ℕ→V→ℕ) (k l : ℕ) (v : V) : M.total F k l v=M.rot.total F k l v := by
  change _=M.rot.trial F k l v+M.rot.rot.trial F k l v+M.trial F k l v
  unfold total; omega

theorem wh : M.W⊆M.H := M.part ▸ subset_union_left
theorem ah : M.A⊆M.H := M.part ▸ (subset_union_left.trans subset_union_right)
theorem size : M.H.card=27 := by
  rw [M.part,card_union_of_disjoint (disjoint_union_right.mpr ⟨M.wa,disjoint_union_right.mpr ⟨M.wb,M.wc⟩⟩),
    card_union_of_disjoint (disjoint_union_right.mpr ⟨M.ab,M.ca.symm⟩),card_union_of_disjoint M.bc,M.ws,M.asz,M.bsz,M.csz]
theorem across : Disjoint M.P M.W ∧ Disjoint M.Q M.W := by
  have out {x : V} (h : x∉M.H) : x∉M.W := fun m => h (M.wh m)
  exact ⟨disjoint_union_left.mpr ⟨M.wa.symm,disjoint_insert_left.mpr ⟨out M.fw,disjoint_singleton_left.mpr (out M.gw)⟩⟩,
    disjoint_union_left.mpr ⟨disjoint_union_left.mpr ⟨M.wb.symm,M.wc.symm⟩,disjoint_singleton_left.mpr (out M.ew)⟩⟩
theorem whigh (v : V) : nbr G v M.H=nbr G v M.W+(nbr G v M.A+nbr G v M.B+nbr G v M.C) := by
  rw [M.part,Repair.nbr_add G v (disjoint_union_right.mpr ⟨M.wa,disjoint_union_right.mpr ⟨M.wb,M.wc⟩⟩),
    Repair.nbr_add G v (disjoint_union_right.mpr ⟨M.ab,M.ca.symm⟩),Repair.nbr_add G v M.bc]; omega
theorem nowhere {w : V} (wm : w∈M.W) : ¬G.Adj w M.e := fun h => disjoint_left.mp M.wa wm
  (M.ea ▸ (G.mem_neighborFinset ..).mpr h.symm)
theorem edge_facts {w : V} (wa : w∈M.A) : G.Adj w M.e ∧ ¬G.Adj w M.f ∧ ¬G.Adj w M.g := by
  exact ⟨((G.mem_neighborFinset ..).mp (M.ea.symm ▸ wa)).symm,
    fun h => disjoint_left.mp M.ab wa (M.fb ▸ (G.mem_neighborFinset ..).mpr h.symm),
    fun h => disjoint_left.mp M.ca.symm wa (M.gc ▸ (G.mem_neighborFinset ..).mpr h.symm)⟩
theorem exterior_degree {w : V} (wm : w∈M.W) : G.degree w=nbr G w M.H := by
  have eq : G.neighborFinset w=M.H.filter (G.Adj w) := by
    ext z; simp only [mem_neighborFinset,mem_filter]
    constructor
    · intro edge
      have m := mem_univ z; rw [M.full] at m
      rcases mem_insert.mp m with rfl|m
      · exact (M.nowhere wm edge).elim
      rcases mem_insert.mp m with rfl|m
      · exact (M.rot.nowhere wm edge).elim
      rcases mem_insert.mp m with rfl|m
      · exact (M.rot.rot.nowhere wm edge).elim
      exact ⟨m,edge⟩
    · exact And.right
  simpa only [card_neighborFinset_eq_degree,nbr] using congrArg card eq

theorem side_score {w : V} (wa : w∈M.A) : trianglesAt G w≤(nbr G w M.H).choose 2+1 := by
  classical
  obtain ⟨we,wf,wg⟩ := M.edge_facts wa
  let D := M.H.filter (G.Adj w)
  have ne : M.e∉D := fun m => M.ew (mem_filter.mp m).1
  have eq : G.neighborFinset w=insert M.e D := by
    ext z; simp only [mem_neighborFinset,mem_insert,mem_filter,D]
    constructor
    · intro edge
      have m := mem_univ z; rw [M.full] at m
      rcases mem_insert.mp m with he|m
      · exact Or.inl he
      rcases mem_insert.mp m with rfl|m
      · exact (wf edge).elim
      rcases mem_insert.mp m with rfl|m
      · exact (wg edge).elim
      exact Or.inr ⟨m,edge⟩
    · rintro (rfl|⟨_,edge⟩)
      · exact we
      · exact edge
  have cut : D.filter (G.Adj M.e)⊆M.A.erase w := by
    intro x xm; obtain ⟨xd,ex⟩ := mem_filter.mp xm
    exact mem_erase.mpr ⟨(mem_filter.mp xd).2.ne.symm,M.ea ▸ (G.mem_neighborFinset ..).mpr ex⟩
  have small := card_le_card cut; rw [card_erase_of_mem wa,M.asz] at small
  have cap := card_le_card (show HighEar.pairs G D ⊆D.powersetCard 2 from filter_subset ..)
  rw [card_powersetCard] at cap
  change (HighEar.pairs G (G.neighborFinset w)).card≤D.card.choose 2+1
  rw [eq,HighEar.pairs_insert G ne]
  change nbr G M.e D≤2-1 at small
  omega
end Layout
end Graffiti384b.EarMix
#print axioms Graffiti384b.EarMix.Layout.exterior_degree
#print axioms Graffiti384b.EarMix.Layout.side_score
