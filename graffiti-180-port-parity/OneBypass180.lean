import HorizontalCost180

set_option warningAsError true
namespace Minimal180.PortParity
open Finset SimpleGraph Graffiti177 Graffiti318 Graffiti180 Rooted180 Converse180 Assembly180 HigherRank
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A connected dominating core permits all specified outside leaves and
the full star of any vertex outside the specified leaf set, simultaneously. -/
theorem leaves_and_star (F : SimpleGraph V) (fc : F.Connected) (hn : 1<Fintype.card V)
    (S : Finset V) (con : Con F (univ\S)) (dom : ∀ z∈S,Dominates F (univ\S) z)
    (a : V) (outside : a∉S) :
    ∃ T≤F,T.IsTree ∧ S⊆leaves T ∧ ∀ x,F.Adj a x → T.Adj a x := by
  classical
  have paid := weightedCore F (univ\S) S con (by intro z h; apply dom; simpa using h)
  have diff : S\(univ\S)=S := by ext x; simp
  rw [diff] at paid
  obtain ⟨M,sub,tr,opt⟩ := tree_opt F fc S
  have eq : S∩leaves M=S := eq_of_subset_of_card_le inter_subset_left (opt ▸ paid)
  obtain ⟨T,tf,tree,star,keep⟩ := full_star_exchange F M sub tr hn a
  exact ⟨T,tf,tree,fun v vs => keep v (fun same => outside (same ▸ vs)) (mem_inter.mp (eq.symm ▸ vs)).2,star⟩

/-- For any spanning subgraph F of the failed graph, restoring its
horizontal edges pays for simultaneous odd leaves and the degree excess
of any chosen even star. Independent odd vertices dominate into their
complement automatically. -/
theorem core_star_charge (G F : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel F.Adj]
    (fg : F≤G) (fc : F.Connected) (hn : 1<Fintype.card V) (r : V)
    (rank : Fintype.card V≤bipartiteNum G+secondDegree G+1)
    (bad : maxLeaves G+bipartiteNum G<1+independence G+evenCount G r)
    (S : Finset V) (odd : Disjoint S (parity G r false)) (con : Con F (univ\S))
    (a : V) (ae : a∈parity G r false) :
    S.card+(F.degree a-2)≤(F.edgeFinset∩(parity G r false).sym2).card := by
  classical
  let P := parity G r false
  have gc := fc.mono fg
  have oi := (saturated_counts G gc hn r rank bad).2.2.2
  have os {v : V} (vs : v∈S) : v∈oddSet G r := by
    have no := disjoint_left.mp odd vs
    simpa [oddSet,mem_parity] using no
  have dom (v : V) (vs : v∈S) : Dominates F (univ\S) v := by
    obtain ⟨w,e⟩ := exists_adj F fc hn v
    exact ⟨w,mem_sdiff.mpr ⟨mem_univ _,fun ws => oi v (os vs) w (os ws) e.ne (fg e)⟩,e⟩
  obtain ⟨T,sub,tr,leavesS,star⟩ := leaves_and_star F fc hn S con dom a (fun h => disjoint_left.mp odd h ae)
  have leafInc : S⊆leaves T\P := fun v vs => mem_sdiff.mpr ⟨leavesS vs,disjoint_left.mp odd vs⟩
  have lf := card_le_card leafInc
  have adjInc : F.neighborFinset a⊆T.neighborFinset a := fun x hx => (T.mem_neighborFinset a x).mpr (star x ((F.mem_neighborFinset a x).mp hx))
  have deg := card_le_card adjInc
  rw [card_neighborFinset_eq_degree,card_neighborFinset_eq_degree] at deg
  have edge := card_le_card (inter_subset_inter (edgeFinset_mono sub) (Subset.rfl : P.sym2⊆P.sym2))
  have bill := charge_horizontal G gc hn r rank bad T (sub.trans fg) tr
  change (leaves T\P).card+(∑ v∈P,(T.degree v-2))≤(T.edgeFinset∩P.sym2).card at bill
  have one : T.degree a-2≤∑ v∈P,(T.degree v-2) := single_le_sum (f:=fun v => T.degree v-2) (fun _ _ => Nat.zero_le _) ae
  change S.card+(F.degree a-2)≤(F.edgeFinset∩P.sym2).card
  omega

/-- If one even chord restores connectivity after deleting an odd vertex,
then each endpoint of that chord has at most one crossing neighbor. Apply
the statement again with the endpoints interchanged for the other end. -/
theorem reconnecting_chord (G : SimpleGraph V) [DecidableRel G.Adj] (gc : G.Connected)
    (hn : 1<Fintype.card V) (r : V)
    (rank : Fintype.card V≤bipartiteNum G+secondDegree G+1)
    (bad : maxLeaves G+bipartiteNum G<1+independence G+evenCount G r)
    (v a b : V) (odd : v∉parity G r false) (ap : a∈parity G r false)
    (bp : b∈parity G r false) (ab : G.Adj a b) :
    let P := parity G r false
    let H := alternating G P
    Con (H⊔SimpleGraph.edge a b) (univ.erase v) → H.degree a≤1 := by
  classical
  intro P H con
  let F := H⊔SimpleGraph.edge a b
  letI : Fintype F.edgeSet := F.fintypeEdgeSet
  have fg : F≤G := sup_le (fun _ _ e => e.1) (by rw [← sup_eq_left]; exact sup_edge_of_adj G ab)
  have fc : F.Connected := (alternating_parity G gc r false).1.mono le_sup_left
  have bill := core_star_charge G F fg fc hn r rank bad {v} (by simpa using odd)
    (by simpa only [sdiff_singleton_eq_erase] using con) a ap
  have edgeInc : F.edgeFinset∩P.sym2⊆{s(a,b)} := by
    intro e h
    induction e using Sym2.ind with
    | _ x y =>
      obtain ⟨adj,inside⟩ := mem_inter.mp h
      obtain ⟨xp,yp⟩ := mk_mem_sym2_iff.mp inside
      rcases (mem_edgeFinset.mp adj : F.Adj x y) with cross|chord
      · exact ((cross.2.mp xp) yp).elim
      · exact mem_singleton.mpr ((adj_edge ..).mp chord).1.symm
  have one := card_le_card edgeInc
  rw [card_singleton] at one bill
  have absent : b∉H.neighborFinset a := fun k => (((H.mem_neighborFinset ..).mp k).2.mp ap) bp
  have nb : insert b (H.neighborFinset a)⊆F.neighborFinset a := by
    intro w hw
    apply (F.mem_neighborFinset a w).mpr
    rcases mem_insert.mp hw with eq|h
    · subst w; exact Or.inr ((edge_adj ..).mpr ⟨Or.inl ⟨rfl,rfl⟩,ab.ne⟩)
    · exact Or.inl ((H.mem_neighborFinset ..).mp h)
  have deg := card_le_card nb
  rw [card_insert_of_not_mem absent,card_neighborFinset_eq_degree,card_neighborFinset_eq_degree] at deg
  change 1+(F.degree a-2)≤(F.edgeFinset∩P.sym2).card at bill
  omega

#print axioms leaves_and_star
#print axioms core_star_charge
#print axioms reconnecting_chord
end Minimal180.PortParity
