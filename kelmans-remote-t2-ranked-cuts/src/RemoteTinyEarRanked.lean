import RemoteTinyEarCore
import RemoteAvoid3RankTransfer
import RemoteT2TinyShoreChain

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteTinyEarRanked
open SquareCap (FactorOn SmallTrivial factor_map)
open RemoteT2CompletionTransfer (marked eraseEdge SmallerIsolatedAvoid3)
open RemoteAvoid3RankTransfer (SmallerRemoteT2 smaller_avoid3_of_remote)
open RemoteT2TinyShoreChain (outside mem_outside tiny_width_two_chain)
open RemoteT2PairCounts (innerCut)
open RemoteT2PairStructure (surviving)

universe u
variable {V W : Type u} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

omit [Fintype V] in
/-- Three repair edges are omitted. Any fourth repair edge may be
used only if it is the shortcut of a genuine three-vertex ear. -/
theorem factor_of_live_ear_tester
    (H : SimpleGraph W) [DecidableRel H.Adj] (G : SimpleGraph V)
    (j : W↪V) (n : ℕ)
    (fit : Fintype.card W<n) (large : 4≤Fintype.card W) (rem : Fintype.card W%6=0)
    (cub : ∀ z,H.degree z=3) (small : SmallTrivial H)
    {a b d e r s i k : W}
    (ab : H.Adj a b) (de : H.Adj d e) (rs : H.Adj r s)
    (ad : a≠d) (ae : a≠e) (bd : b≠d) (be : b≠e)
    (ar : a≠r) (as' : a≠s) (br : b≠r) (bs : b≠s) (dr : ¬marked d e r s)
    (ik : i≠k)
    {l c w : V} (al : G.Adj (j i) l) (lc : G.Adj l c) (cw : G.Adj c w)
    (wb : G.Adj w (j k)) (lw : l≠w)
    (ls : l∉(univ:Finset W).map j) (cs : c∉(univ:Finset W).map j)
    (ws : w∉(univ:Finset W).map j)
    (keep : ∀ x y, H.Adj x y → G.Adj (j x) (j y) ∨
      marked a b x y ∨ marked d e x y ∨ marked r s x y ∨ marked i k x y)
    (avo : SmallerIsolatedAvoid3.{u} n) :
    FactorOn G (((univ:Finset W).map j)∪({l,c,w}:Finset V)) := by
  let D := eraseEdge (eraseEdge (eraseEdge H a b) d e) r s
  have cc := SquareCap.three_connected_of_small_trivial H cub large small
  have tst : FactorOn D univ :=
    avo W H fit cub cc small rem a b d e r s ab de rs ad ae bd be ar as' br bs dr
  let E : SimpleGraph V :=
    G ⊔ (SimpleGraph.fromRel (fun x y=>x=j i∧y=j k))
  have moved := factor_map j (H:=E) (G:=D) (fun x y edge=>by
    have o := keep x y edge.1.1.1
    rcases o with hit|m|m|m|m
    · exact Or.inl hit
    · exact (edge.1.1.2 m).elim
    · exact (edge.1.2 m).elim
    · exact (edge.2 m).elim
    · rcases m with ⟨hx,hy⟩|⟨hx,hy⟩
      · subst x
        subst y
        exact Or.inr ⟨fun eq=>ik (j.injective eq),Or.inl ⟨rfl,rfl⟩⟩
      · subst x
        subst y
        exact Or.inr ⟨fun eq=>ik (j.injective eq.symm),Or.inr ⟨rfl,rfl⟩⟩) tst
  apply RemoteTinyEarCore.lift_live_ear (fun z=>ik (j.injective z)) al lc cw wb lw ls cs ws
    (fact:=moved)
  intro x _ y _ h
  rcases h with h|⟨_,h⟩
  · exact Or.inl h
  · exact Or.inr (h.elim Or.inl (fun p=>Or.inr ⟨p.2,p.1⟩))

/-- A genuine tiny shore whose forced tile exposes a smaller live-ear
tester cannot be a minimal Remote T2 counterexample. The supplied
tester is required to be cubic and cyclically four; its existence is
not asserted here. No larger or equal-order factoring assumption is
used. -/
theorem tiny_remote_of_live_ear_tester
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (small : SmallTrivial G) (big : 5≤Fintype.card V) (cub : ∀ z,G.degree z=3)
    (ambient : Fintype.card V%6=2)
    {x y u v w q : V} (xy : G.Adj x y)
    (ux : u≠x) (uy : u≠y) (vx : v≠x) (vy : v≠y) (wx : w≠x) (wy : w≠y)
    (uw : u≠w) (uv : G.Adj u v)
    (col : V→Bool) (cu : col u=true) (cv : col v=false) (cw : col w=true)
    (precise : ∀ z : V,z≠x → z≠y → (col z=true ↔ z=u∨z=w))
    (cut : (innerCut G col x y).card=2)
    (qx : q≠x) (qy : q≠y) (cq : col q=false) (wq : G.Adj w q)
    (H : SimpleGraph W) [DecidableRel H.Adj] (j : W↪V)
    (order : Fintype.card W+8=Fintype.card V) (large : 4≤Fintype.card W)
    (hcub : ∀ z,H.degree z=3) (hsmall : SmallTrivial H)
    {a b d e r s i k : W}
    (ab : H.Adj a b) (de : H.Adj d e) (rs : H.Adj r s)
    (ad : a≠d) (ae : a≠e) (bd : b≠d) (be : b≠e)
    (ar : a≠r) (as' : a≠s) (br : b≠r) (bs : b≠s) (dr : ¬marked d e r s)
    (ik : i≠k) {l c z : V}
    (al : (eraseEdge G u v).Adj (j i) l) (lc : (eraseEdge G u v).Adj l c)
    (cz : (eraseEdge G u v).Adj c z) (zb : (eraseEdge G u v).Adj z (j k))
    (lz : l≠z)
    (ls : l∉(univ:Finset W).map j) (cs : c∉(univ:Finset W).map j)
    (zs : z∉(univ:Finset W).map j)
    (support : ((univ:Finset W).map j)∪({l,c,z}:Finset V)=
      outside x y \ ({u,w,q}:Finset V))
    (keep : ∀ m n, H.Adj m n → (eraseEdge G u v).Adj (j m) (j n) ∨
      marked a b m n ∨ marked d e m n ∨ marked r s m n ∨ marked i k m n)
    (remote : SmallerRemoteT2.{u} (Fintype.card V)) :
    FactorOn (eraseEdge G u v) (outside x y) := by
  classical
  obtain ⟨q',_,_,_,_,_,_,sw,reduction⟩ := tiny_width_two_chain G small big cub
    xy ux uy vx vy wx wy uw uv col cu cv cw precise cut
  have qm : q∈surviving G x y w := by
    simp [surviving,mem_neighborFinset,qx,qy,wq]
  rw [sw,mem_insert,mem_singleton] at qm
  have what : q=q' := qm.resolve_left (fun p=>by rw [p,cu] at cq; contradiction)
  rw [←what] at reduction
  apply reduction.mpr
  have avo : SmallerIsolatedAvoid3.{u} (Fintype.card V-2) :=
    smaller_avoid3_of_remote (Fintype.card V-2) (by
      have eq : Fintype.card V-2+2=Fintype.card V := by omega
      rwa [eq])
  have ff := factor_of_live_ear_tester H (eraseEdge G u v) j (Fintype.card V-2)
    (by omega) large (by omega) hcub hsmall ab de rs ad ae bd be ar as' br bs dr
    ik al lc cz zb lz ls cs zs keep avo
  rwa [support] at ff

#print axioms factor_of_live_ear_tester
#print axioms tiny_remote_of_live_ear_tester
end KelmansCactus.AtomicBridge.RemoteTinyEarRanked
