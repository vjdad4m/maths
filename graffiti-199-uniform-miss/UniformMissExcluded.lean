import HubExpansion
import IndependentMissRoute
import NoncliqueExample
namespace Graffiti199Depleted.Catalogue.Incomplete
open SimpleGraph
universe u
variable {V : Type u} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {X : Set V} {z r a b : V} {i : RootComponent G X r}

private def AtMostOneFlank (G : SimpleGraph V) (x y : V) : Prop :=
  ∀ u v, u ≠ x → v ≠ x → G.Adj y u → G.Adj y v → ¬ G.Adj x u → ¬ G.Adj x v → u=v

omit [DecidableRel G.Adj] in
private theorem orientation (F : SingletonCut G X z r a b) (good : UniformMissPart G X r i)
    {x y : V} (xi : x ∈ MissPart G X r i) (yi : y ∈ MissPart G X r i) :
    AtMostOneFlank G x y ∨ AtMostOneFlank G y x := by
  classical
  by_cases fit : AtMostOneFlank G x y
  · exact Or.inl fit
  right
  unfold AtMostOneFlank at fit
  push_neg at fit
  obtain ⟨s,t,sx,tx,ys,yt,xs,xt,st⟩ := fit
  have ports : a=s ∧ b=t ∨ a=t ∧ b=s := by
    rcases F.difference_in_ports good yi xi sx ys xs with es|es <;>
      rcases F.difference_in_ports good yi xi tx yt xt with et|et <;> subst s <;> subst t <;> simp_all
  intro u v uy _ xu _ yu _
  have off : ¬ G.Adj x a ∧ ¬ G.Adj x b := by
    rcases ports with ⟨h,k⟩|⟨h,k⟩
    · exact ⟨h.symm ▸ xs,k.symm ▸ xt⟩
    · exact ⟨h.symm ▸ xt,k.symm ▸ xs⟩
  exact (F.difference_in_ports good xi yi uy xu yu).elim (fun e => (off.1 (e ▸ xu)).elim) (fun e => (off.2 (e ▸ xu)).elim)

theorem SingletonCut.no_nonsingleton_uniform_miss (F : SingletonCut G X z r a b)
    (smaller : SmallerAtThree.{u} (Fintype.card V)) (order : 5 ≤ Fintype.card V)
    (cross : CrossingBetweenSurvivingEdges G) (no : ¬ Traceable G)
    (ind : ∀ u v, G.degree u = 3 → G.degree v = 3 → ¬ G.Adj u v)
    (three : ∃ T : Finset V, T.card = 3 ∧ ∀ v ∈ T, v ∈ Noncontacts G X r)
    (large : 2 ≤ Nat.card (MissPart G X r i)) : ¬ UniformMissPart G X r i := by
  classical
  intro good
  obtain ⟨x,y,p,xy,eqC,ed,_,_,_,nbr,unique⟩ :=
    F.uniform_pair_unique_cubic smaller order cross no ind three good large
  have xi : x ∈ MissPart G X r i := eqC.symm ▸ (by simp : x ∈ ({x,y} : Set V))
  have yi : y ∈ MissPart G X r i := eqC.symm ▸ (by simp : y ∈ ({x,y} : Set V))
  have xX := (noncontactComponent_subset i xi).1
  have yX := (noncontactComponent_subset i yi).1
  let D : Finset V := {r,a,b}
  have cd : D.card = 3 := by simp [D,F.ra,F.rb,F.ab]
  have sep : Disjoint D ({z,x,y} : Finset V) := by
    apply Finset.disjoint_left.mpr
    intro v vd vm
    rcases (show v=z ∨ v=x ∨ v=y by simpa using vm) with e|e|e
    · exact F.cut.1 (e ▸ vd)
    · exact F.offX _ vd (e.symm ▸ xX)
    · exact F.offX _ vd (e.symm ▸ yX)
  have zx : z ≠ x := fun e => F.zX (e.symm ▸ xX)
  have zy : z ≠ y := fun e => F.zX (e.symm ▸ yX)
  have six : 6 ≤ Fintype.card V := by
    have h := Finset.card_le_univ (D ∪ {z,x,y})
    rw [Finset.card_union_of_disjoint sep,cd] at h
    simpa [zx,zy,xy] using h
  have only (v : V) : G.Adj p v ↔ v=r ∨ v=x ∨ v=y := by
    rw [← G.mem_neighborFinset,nbr]; simp
  have pr := (only r).mpr (Or.inl rfl)
  have px := (only x).mpr (Or.inr (Or.inl rfl))
  have py := (only y).mpr (Or.inr (Or.inr rfl))
  have close {s t : V} (si : s ∈ MissPart G X r i) (ti : t ∈ MissPart G X r i)
      (st : G.Adj s t) (ps : G.Adj p s) (pt : G.Adj p t)
      (only' : ∀ v, G.Adj p v ↔ v=r ∨ v=s ∨ v=t)
      (fit : AtMostOneFlank G s t) : False := by
    have rs : r ≠ s := fun h => F.offX r (by simp) (h.symm ▸ (noncontactComponent_subset i si).1)
    have rt : r ≠ t := fun h => F.offX r (by simp) (h.symm ▸ (noncontactComponent_subset i ti).1)
    let J := (hubFill G rt).induce (HubKeep s p)
    have connected : ConnectivityAtLeast J 3 := hubFill_connectivity F.conn six cross ps.ne.symm rt
      (fun q sq d => (unique s si q sq).mp d) only'
    have budget : treeNumber J ≤ 5 := (hubFill_budget rt rs st.ne.symm ps.ne only').trans F.budget
    have sz := hubKeep_card ps.ne.symm
    have path := smaller (HubKeep s p) J (by omega) connected budget
    exact no (traceable_of_filled_hub rt st pr.symm ps.symm pt fit path)
  rcases orientation F good xi yi with fit|fit
  · exact close xi yi ed px py only fit
  · exact close yi xi ed.symm py px (fun v => by rw [only]; tauto) fit

/-- Minimum-order catalogue inputs force the new exclusion at every cut and
every ordering of its three ports. For an independent miss set with two
private ordinary contacts at every vertex, the outside-port matching fails. -/
theorem catalogue_minimum_miss_hub_exclusion
    (minimum : ∀ (W : Type u) [Fintype W] (H : SimpleGraph W), Fintype.card W < Fintype.card V →
      H.Connected → 2 ≤ Fintype.card W → treeNumber H ≤ vertexConnectivity H + 2 → Traceable H)
    (k : vertexConnectivity G = 3) (bound : treeNumber G ≤ vertexConnectivity G + 2)
    (order : 5 ≤ Fintype.card V) (no : ¬ Traceable G)
    (ind : ∀ u v, G.degree u = 3 → G.degree v = 3 → ¬ G.Adj u v) :
    (∃ D : Finset V, D.card=3 ∧ ¬ (DeletionGraph G D).Preconnected) ∧
    ∀ D : Finset V, D.card=3 → ¬ (DeletionGraph G D).Preconnected →
      ∃ z : V, ∃ X : Set V, ∀ r a b : V, r ≠ a → r ≠ b → a ≠ b → D={r,a,b} →
        SingletonCut G X z r a b ∧
        (∀ i : RootComponent G X r, 2 ≤ Nat.card (MissPart G X r i) → ¬ UniformMissPart G X r i) ∧
        ((Noncontacts G X r).Pairwise (fun u v => ¬ G.Adj u v) →
          (∀ u ∈ Noncontacts G X r, ∃ q h : V, q ≠ h ∧ PrivateMissContact G X r u q ∧ PrivateMissContact G X r u h) →
          ∀ s ∈ Noncontacts G X r, ∀ t ∈ Noncontacts G X r, G.Adj a s → G.Adj t b → s=t) := by
  obtain ⟨existsCut,every⟩ := catalogue_minimum_all_ports_miss_three minimum k bound order no ind
  refine ⟨existsCut,?_⟩
  intro D size bad
  obtain ⟨z,X,_,all⟩ := every D size bad
  refine ⟨z,X,?_⟩
  intro r a b ra rb ab eq
  obtain ⟨F,_,_,three⟩ := all r a b ra rb ab eq
  have cross := catalogue_minimum_crossing minimum F.conn F.budget order no ind
  refine ⟨F,fun _ large => F.no_nonsingleton_uniform_miss (smallerAtThree_of_catalogue_minimum minimum) order cross no ind three large,?_⟩
  intro indep wide s sm t tm sa tb
  by_contra st
  exact no (F.traceable_of_two_private_contacts_per_miss indep wide sm tm st sa tb)

namespace NoncliqueExample
/-- All ports of the eleven-vertex fixture miss an edge and a nonedge. Thus
miss independence and a uniform-clique description of the entire missed
component both fail on this traceable graph. -/
theorem fixture_missed_edge_and_nonedge (p : W) (hp : p ∈ ports) :
    (8:W) ∈ Noncontacts graph NoncliqueExample.X p ∧ (9:W) ∈ Noncontacts graph NoncliqueExample.X p ∧
    (10:W) ∈ Noncontacts graph NoncliqueExample.X p ∧ graph.Adj 8 9 ∧ ¬ graph.Adj 8 10 := by
  rw [each_port_misses_path p hp]
  decide +kernel
end NoncliqueExample

#print axioms SingletonCut.no_nonsingleton_uniform_miss
#print axioms catalogue_minimum_miss_hub_exclusion
#print axioms NoncliqueExample.fixture_missed_edge_and_nonedge
end Graffiti199Depleted.Catalogue.Incomplete

