import ColorPath180

set_option warningAsError true
namespace Minimal180
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
universe u
variable {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

def SparseAt (r : V) : Prop := ∀ a b, G.Adj a b → ¬Arc G r a b → ¬Arc G r b a →
  bipartiteNum (G.deleteEdges {s(a,b)})=bipartiteNum G+1

theorem rank_antitone {J : SimpleGraph V} (sub : J≤G) : bipartiteNum G≤bipartiteNum J := by
  classical
  obtain ⟨X,⟨C,D,dis,eq,ic,id⟩,top⟩ := optB G
  rw [← top]
  apply size_bip J
  exact ⟨C,D,dis,eq,fun a ha b hb ne e => ic a ha b hb ne (sub e),
    fun a ha b hb ne e => id a ha b hb ne (sub e)⟩

/-- Preserve all distances to the given root and the exact induced
bipartite order while making every dispensable edge rank-critical. -/
theorem sparsify (hc : G.Connected) (r : V) :
    ∃ J≤G, J.Connected ∧ (∀ v, J.dist v r=G.dist v r) ∧ bipartiteNum J=bipartiteNum G ∧ SparseAt J r := by
  classical
  let keep (H : SimpleGraph V) := H.Connected ∧ (∀ v, H.dist v r=G.dist v r) ∧ bipartiteNum H=bipartiteNum G
  obtain ⟨J,sub,hm⟩ := {H : SimpleGraph V | keep H}.toFinite.exists_minimal_le
    (show keep G from ⟨hc,fun _ => rfl,rfl⟩)
  obtain ⟨jc,dist,rank⟩ := hm.prop
  refine ⟨J,sub,jc,dist,rank,?_⟩
  intro a b e no rev
  let K := J.deleteEdges {s(a,b)}
  obtain ⟨kc,kd⟩ := remove_edge_distances J jc r a b no rev
  have ks : K<J := lt_of_le_of_ne (J.deleteEdges_le _) (by
    intro eq
    have missing : ¬K.Adj a b := by simp [K]
    exact missing (eq ▸ e))
  have mono := rank_antitone J ks.le
  have strict : bipartiteNum J<bipartiteNum K := by
    apply lt_of_le_of_ne mono
    intro same
    exact hm.not_prop_of_lt ks (show keep K from ⟨kc,fun v => (kd v).trans (dist v),same.symm.trans rank⟩)
  exact (edge_witness J a b e strict).1

def SparseBlocks : Prop := ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
  G.Connected → 1<Fintype.card V → NoCut G → ∀ r, SparseAt G r → ∀ odd, localBound G r (parity G r odd)

/-- The universal graph conjecture is equivalent to the actual rooted
bound on biconnected blocks satisfying the root-dependent edge condition. -/
theorem universal_iff_sparse_blocks : Universal.{u} ↔ SparseBlocks.{u} := by
  classical
  rw [universal_iff_blocks]
  constructor
  · intro all V _ _ H hc hn noc r _ odd
    exact all V H hc hn noc r odd
  · intro sparse
    have result {W : Type u} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
        (hc : H.Connected) (hn : 1<Fintype.card W) :
        ∀ r odd, localBound H r (parity H r odd) := by
      generalize eq : Fintype.card W=n at *
      induction n using Nat.strong_induction_on generalizing W with
      | h n ih =>
        intro r odd
        obtain ⟨J,sub,jc,d,rank,sp⟩ := sparsify H hc r
        have onJ : localBound J r (parity J r odd) := by
          by_cases ok : NoCut J
          · exact sparse W J jc (eq ▸ hn) ok r sp odd
          obtain ⟨c,S,T,s⟩ := split_of_cut ok
          have next {X Y} (q : Split J c X Y) : ∀ (a : ↥X) p, localBound (side J X) a (parity (side J X) a p) := by
            exact ih (Fintype.card ↥X) (by rw [Fintype.card_coe,← eq]; exact q.smallL)
              _ (q.connectedL jc) rfl q.largeL
          rcases s.either r with h|h
          · exact s.parity_join jc ⟨r,h⟩ odd (next s) (next s.flip)
          · exact s.flip.parity_join jc ⟨r,h⟩ odd (next s.flip) (next s)
        have par : parity J r odd=parity H r odd := by ext v; simp only [mem_parity,d v]
        rw [par] at onJ
        intro A ai
        exact (onJ A (fun v hv w hw ne e => ai v hv w hw ne (sub e))).trans
          (Nat.add_le_add (leaf_mono H sub _) rank.le)
    intro W _ _ H hc hn _
    exact result H hc hn

#print axioms sparsify
#print axioms universal_iff_sparse_blocks
end Minimal180
