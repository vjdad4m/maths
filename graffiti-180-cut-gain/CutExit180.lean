import CutEscape180

set_option warningAsError true
namespace Minimal180.CutGain
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 OddBlock
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Deleting a horizontal edge without a common predecessor leaves
either a block or an edge whose endpoints have no common lower neighbor. -/
theorem horizontal_exit (G : SimpleGraph V) (gc : G.Connected) (block : NoCut G)
    {a b r : V} (adj : G.Adj a b) (flat : G.dist a r=G.dist b r)
    (no : ¬∃ p,G.Adj a p ∧ G.Adj b p ∧ G.dist a r=G.dist p r+1) :
    let K := G.deleteEdges {s(a,b)}
    K.Connected ∧ (NoCut K ∨ ¬∃ u,K.Adj a u ∧ K.Adj b u) := by
  classical
  intro K
  have ab : ¬Arc G r a b := fun z => by have := z.2.1; omega
  have ba : ¬Arc G r b a := fun z => by have := z.2.1; omega
  obtain ⟨kc,ds⟩ := remove_edge_distances G gc r a b ab ba
  refine ⟨kc,?_⟩
  by_cases ok : NoCut K
  · exact Or.inl ok
  right
  rintro ⟨u,au,bu⟩
  have restore : K⊔edge a b=G := by
    apply le_antisymm (sup_le (G.deleteEdges_le _) (by rw [←sup_eq_left]; exact sup_edge_of_adj G adj))
    intro x y xy
    by_cases pair : s(x,y)=s(a,b)
    · exact Or.inr ((adj_edge ..).mpr ⟨pair.symm,xy.ne⟩)
    · exact Or.inl (deleteEdges_adj.mpr ⟨xy,pair⟩)
  obtain ⟨c,S,T,sp⟩ := split_of_cut ok
  obtain ⟨eq,sides⟩ := chord_seam sp (restore ▸ block) au bu.symm
  subst c
  have far {L R : Finset V} (k : Split K u L R) (rl : r∈L) {v : V} (vr : v∈R) (uv : K.Adj u v) :
      G.dist v r=G.dist u r+1 := by
    let s : ↥L := ⟨r,rl⟩
    let l : ↥L := ⟨u,k.both.1⟩
    let t : ↥R := ⟨u,k.both.2⟩
    let z : ↥R := ⟨v,vr⟩
    have rwk := k.distances kc s
    have e : (side K R).dist z t=1 := dist_eq_one_iff_adj.mpr uv.symm
    have score : K.dist v r=K.dist u r+1 := by rw [rwk.2 z,e,rwk.1 l,Nat.add_comm]
    exact (ds v).symm.trans (score.trans (congrArg (·+1) (ds u)))
  apply no
  refine ⟨u,G.deleteEdges_le _ au,G.deleteEdges_le _ bu,?_⟩
  rcases sp.either r with rl|rr
  · rcases sides with v|v
    · exact flat.trans (far sp rl v.2.2.1 bu.symm)
    · exact far sp rl v.1 au.symm
  · rcases sides with v|v
    · exact far sp.flip rr v.1 au.symm
    · exact flat.trans (far sp.flip rr v.2.2.1 bu.symm)

/-- A failure in the deficit-one tight cut branch demands a second,
deeper rank drop of a different structural type in that same upper graph. -/
theorem TightCut.defect_one_exit {J : SimpleGraph V} {S T : Finset V} {x y w : V}
    {r : ↥S} {odd : Bool} {A : Finset V} (h : TightCut J S T x y w r odd A)
    (rank1 : bipartiteNum J+1=Fintype.card V) :
    let G := J⊔edge x y
    let P := parity G r.val odd
    let U := eligible A P r.val
    ¬weightedLeaves J U<weightedLeaves G U →
      ∃ q z, J.Adj q z ∧ G.dist x r.val<G.dist q r.val ∧ G.dist q r.val=G.dist z r.val ∧
        let K := G.deleteEdges {s(q,z)}
        K.Connected ∧ bipartiteNum K=bipartiteNum G+1 ∧
        (NoCut K ∨ ¬∃ u,K.Adj q u ∧ K.Adj z u) := by
  intro G P U ng
  obtain ⟨q,z,_,_,_,edge,deep,flat,rank,no⟩ := h.deeper_chord rank1 ng
  have out := horizontal_exit G (h.connected.mono le_sup_left) h.block (Or.inl edge) flat no
  exact ⟨q,z,edge,deep,flat,out.1,rank,out.2⟩

/-- On the alternate edge, the smaller lower graph is itself a failed
rooted instance or gives a tight transition with exactly zero leaf gain. -/
theorem TightCut.exit_transition {J : SimpleGraph V} {S T : Finset V} {x y w : V}
    {r : ↥S} {odd : Bool} {A : Finset V} (h : TightCut J S T x y w r odd A)
    (rank1 : bipartiteNum J+1=Fintype.card V) :
    let G := J⊔edge x y
    let P := parity G r.val odd
    let U := eligible A P r.val
    let target := 1+A.card+P.card
    ¬weightedLeaves J U<weightedLeaves G U →
      ∃ q z, J.Adj q z ∧ G.dist x r.val<G.dist q r.val ∧ G.dist q r.val=G.dist z r.val ∧
        let K := G.deleteEdges {s(q,z)}
        K.Connected ∧ parity K r.val odd=P ∧ Indep K A ∧
        bipartiteNum K=bipartiteNum G+1 ∧ (NoCut K ∨ ¬∃ u,K.Adj q u ∧ K.Adj z u) ∧
        (weightedLeaves K U+bipartiteNum K<target ∨
          (weightedLeaves K U+bipartiteNum K=target ∧ weightedLeaves K U=weightedLeaves G U)) := by
  intro G P U target ng
  obtain ⟨q,z,qz,deep,flat,kc,bip,exit⟩ := h.defect_one_exit rank1 ng
  let K := G.deleteEdges {s(q,z)}
  have flat' : G.dist q r.val=G.dist z r.val := flat
  have ab : ¬Arc G r.val q z := fun ar => by have := ar.2.1; omega
  have ba : ¬Arc G r.val z q := fun ar => by have := ar.2.1; omega
  have ds := (remove_edge_distances G (h.connected.mono le_sup_left) r.val q z ab ba).2
  have same : parity K r.val odd=P := by
    ext i
    change i∈parity K r.val odd ↔ i∈parity G r.val odd
    simp only [mem_parity]
    rw [show K.dist i r.val=G.dist i r.val from ds i]
  have kg : K≤G := G.deleteEdges_le _
  have k := leaf_mono G kg U
  have j := leaf_mono G (show J≤G from le_sup_left) U
  have rank : bipartiteNum K=bipartiteNum G+1 := bip
  have old : weightedLeaves J U+bipartiteNum J=target := h.tight
  have before : bipartiteNum J=bipartiteNum G+1 := h.rank
  refine ⟨q,z,qz,deep,flat,kc,same,fun i im l lm ne e => h.independent i im l lm ne (kg e),bip,exit,?_⟩
  change weightedLeaves K U+bipartiteNum K<target ∨
    (weightedLeaves K U+bipartiteNum K=target ∧ weightedLeaves K U=weightedLeaves G U)
  omega

/-- The alternate lower graph has deficit one and its root keeps two
neighbors. The previously proved rank-one rooted bound forces an actual
second tight transition, with no inductive hypothesis. -/
theorem TightCut.tight_exit {J : SimpleGraph V} {S T : Finset V} {x y w : V}
    {r : ↥S} {odd : Bool} {A : Finset V} (h : TightCut J S T x y w r odd A)
    (rank1 : bipartiteNum J+1=Fintype.card V) :
    let G := J⊔edge x y
    let P := parity G r.val odd
    let U := eligible A P r.val
    ¬weightedLeaves J U<weightedLeaves G U →
      ∃ q z, J.Adj q z ∧ G.dist x r.val<G.dist q r.val ∧ G.dist q r.val=G.dist z r.val ∧
        let K := G.deleteEdges {s(q,z)}
        K.Connected ∧ ¬TwoColor K univ ∧ parity K r.val odd=P ∧ Indep K A ∧
        bipartiteNum K=bipartiteNum G+1 ∧ (NoCut K ∨ ¬∃ u,K.Adj q u ∧ K.Adj z u) ∧
        weightedLeaves K U+bipartiteNum K=1+A.card+P.card ∧
        weightedLeaves K U=weightedLeaves G U := by
  intro G P U ng
  obtain ⟨q,z,e,deep,flat,kc,same,ind,bip,shape,alt⟩ := h.exit_transition rank1 ng
  let K := G.deleteEdges {s(q,z)}
  have deep' : G.dist x r.val<G.dist q r.val := deep
  have flat' : G.dist q r.val=G.dist z r.val := flat
  have nrq : r.val≠q := by intro eq; rw [←eq,dist_self] at deep'; omega
  have nrz : r.val≠z := by intro eq; rw [←eq,dist_self] at flat'; omega
  have keep {v : V} (rv : G.Adj r.val v) : K.Adj r.val v := by
    apply deleteEdges_adj.mpr
    refine ⟨rv,?_⟩
    intro pair
    rcases Sym2.eq_iff.mp (Set.mem_singleton_iff.mp pair) with a|a
    · exact nrq a.1
    · exact nrz a.1
  obtain ⟨l,m,rl,rm,lm⟩ := block_neighbors G (h.connected.mono le_sup_left) (by have := h.order; omega) h.block r.val
  have rk : bipartiteNum K=bipartiteNum G+1 := bip
  have rj : bipartiteNum J=bipartiteNum G+1 := h.rank
  have deficit : bipartiteNum K+1=Fintype.card V := by omega
  have oddK : ¬TwoColor K univ := by
    intro all
    have cap := size_bip K all
    rw [card_univ] at cap
    omega
  have b := rank_one_rooted K kc (by have := h.order; omega) r.val ⟨l,m,keep rl,keep rm,lm⟩ (by omega) odd A ind
  change 1+A.card+(parity K r.val odd).card≤weightedLeaves K (eligible A (parity K r.val odd) r.val)+bipartiteNum K at b
  change parity K r.val odd=P at same
  rw [same] at b
  change 1+A.card+P.card≤weightedLeaves K U+bipartiteNum K at b
  exact ⟨q,z,e,deep,flat,kc,oddK,same,ind,bip,shape,alt.resolve_left (not_lt_of_ge b)⟩

#print axioms TightCut.tight_exit
#print axioms TightCut.exit_transition
#print axioms horizontal_exit
#print axioms TightCut.defect_one_exit
end Minimal180.CutGain
