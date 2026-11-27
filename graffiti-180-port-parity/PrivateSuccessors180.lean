import RankThreeBypass180

set_option warningAsError true
namespace Minimal180.PortParity
open Finset SimpleGraph Graffiti177 Graffiti318 Graffiti180 Rooted180 Converse180 Assembly180 HigherRank
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Any independent set of even representatives disjoint from A and from
the neighbors of the odd vertices outside A falls short of replacing
all odd vertices of a maximum independent A at a borderline failure. -/
theorem companion_shortage (G : SimpleGraph V) [DecidableRel G.Adj] (gc : G.Connected)
    (hn : 1<Fintype.card V) (r : V)
    (rk : Fintype.card V≤bipartiteNum G+secondDegree G+1)
    (bad : maxLeaves G+bipartiteNum G<1+independence G+evenCount G r)
    (A X : Finset V) (ai : Indep G A) (am : A.card=independence G)
    (xi : Indep G X) (xa : Disjoint X A) (xe : Disjoint X (oddSet G r))
    (off : ∀ x∈X,∀ y∈oddSet G r\A,¬G.Adj x y) :
    X.card<(oddSet G r∩A).card := by
  classical
  let Q := oddSet G r
  have ⟨rank,alpha,_,oi⟩ := saturated_counts G gc hn r rk bad
  have col : Indep G ((Q\A)∪X) := by
    intro u hu v hv uv e
    rcases mem_union.mp hu with uq|ux <;> rcases mem_union.mp hv with vq|vx
    · exact oi u (mem_sdiff.mp uq).1 v (mem_sdiff.mp vq).1 uv e
    · exact off v vx u uq e.symm
    · exact off u ux v vq e
    · exact xi u ux v vx uv e
  have dis : Disjoint A ((Q\A)∪X) := disjoint_left.mpr (by
    intro v va h
    rcases mem_union.mp h with l|x
    · exact (mem_sdiff.mp l).2 va
    · exact disjoint_left.mp xa x va)
  have size := bip_bound G ai col dis
  rw [card_union_of_disjoint (xe.symm.mono_left sdiff_subset)] at size
  change A.card+((Q\A).card+X.card)≤bipartiteNum G at size
  have part := odd_partition G r
  have split := card_sdiff_add_card_inter Q A
  change evenCount G r+Q.card=Fintype.card V at part
  change X.card<(Q∩A).card
  omega

/-- For every choice of a private successor of each odd vertex in A,
two successors must be adjacent or some successor must itself have a
deeper odd neighbor outside A. All quantifiers refer to the same root
and the same maximum independent set. -/
theorem private_conflict (G : SimpleGraph V) [DecidableRel G.Adj] (gc : G.Connected)
    (hn : 1<Fintype.card V) (r : V)
    (rk : Fintype.card V≤bipartiteNum G+secondDegree G+1)
    (bad : maxLeaves G+bipartiteNum G<1+independence G+evenCount G r)
    (A : Finset V) (ai : Indep G A) (am : A.card=independence G)
    (f : V→V) (privateChild : ∀ q∈oddSet G r∩A,Arc G r q (f q)) :
    let M := oddSet G r∩A
    (∃ q∈M,∃ t∈M,G.Adj (f q) (f t)) ∨
      ∃ q∈M,∃ z∈oddSet G r\A,G.Adj (f q) z ∧ G.dist z r=G.dist (f q) r+1 := by
  classical
  intro M
  by_contra! no
  obtain ⟨noPair,noStep⟩ := no
  let X := M.image f
  have inj : Set.InjOn f (M : Set V) := by
    intro u um v vm eq
    have a := privateChild u um
    have b := privateChild v vm
    rw [←eq] at b
    exact (a.2.2 v b.1 b.2.1).symm
  have same : X.card=M.card := card_image_of_injOn inj
  have noA : Disjoint X A := disjoint_left.mpr (by
    intro x xm xa
    obtain ⟨q,qm,rfl⟩ := mem_image.mp xm
    have e := (privateChild q qm).1
    exact ai q (mem_inter.mp qm).2 _ xa e.ne e)
  have even (q : V) (qm : q∈M) : G.dist (f q) r%2=0 := by
    have h := (privateChild q qm).2.1
    have odd : q∈oddSet G r := (mem_inter.mp qm).1
    simp only [oddSet,mem_filter,mem_univ,true_and] at odd
    omega
  have noQ : Disjoint X (oddSet G r) := disjoint_left.mpr (by
    intro x xm xo; obtain ⟨q,qm,rfl⟩ := mem_image.mp xm
    exact (mem_filter.mp xo).2 (even q qm))
  have independent : Indep G X := by
    intro x xm y ym _ edge
    obtain ⟨q,qm,rfl⟩ := mem_image.mp xm
    obtain ⟨t,tm,rfl⟩ := mem_image.mp ym
    exact noPair q qm t tm edge
  have off (x : V) (xm : x∈X) (z : V) (zm : z∈oddSet G r\A) (edge : G.Adj x z) : False := by
    obtain ⟨q,qm,rfl⟩ := mem_image.mp xm
    have prior := privateChild q qm
    have ze : G.dist z r%2≠0 := (mem_filter.mp (mem_sdiff.mp zm).1).2
    have ev := even q qm
    have l := gc.dist_triangle (u:=f q) (v:=z) (w:=r)
    have h := gc.dist_triangle (u:=z) (v:=f q) (w:=r)
    rw [dist_eq_one_iff_adj.mpr edge] at l
    rw [dist_eq_one_iff_adj.mpr edge.symm] at h
    by_cases up : G.dist z r=G.dist (f q) r+1
    · exact noStep q qm z zm edge up
    have eq := prior.2.2 z edge.symm (by omega)
    exact (mem_sdiff.mp zm).2 (eq ▸ (mem_inter.mp qm).2)
  have low := companion_shortage G gc hn r rk bad A X ai am independent noA noQ off
  change X.card<M.card at low
  omega

#print axioms companion_shortage
#print axioms private_conflict
end Minimal180.PortParity
