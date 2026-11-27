import CleanTrial
namespace Graffiti384b.PendantRank
open Finset SimpleGraph Donor
open private FiniteRange.bad from FiniteRange384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def edgeTrials (X : Finset V) (x y : V) := pairTrials G ∅ ((X.erase x).erase y) 10 x y

/-- Pool-only contacts let us transfer the four-class count, which excludes
both endpoints, to usable repair pairs in the full sample. -/
theorem internal_events (X : Finset V) {x y : V} (xm : x∈X) (ym : y∈X)
    (nx : G.neighborFinset x⊆X) (ny : G.neighborFinset y⊆X) :
    edgeTrials G X x y⊆X.powersetCard 10 ∧
      ∀k∈edgeTrials G X x y,x∈FiniteRange.bad G X k ∧ y∈FiniteRange.bad G X k ∧ nbr G x (Xᶜ∪k)=1 := by
  classical
  have move (z : V) (nz : G.neighborFinset z⊆X) (k : Finset V) : nbr G z (Xᶜ∪k)=nbr G z (∅∪k) := by
    rw [empty_union]; unfold nbr; congr 1; ext a
    simp only [mem_filter,mem_union,mem_compl]
    exact ⟨fun ⟨m,za⟩ => ⟨m.resolve_left (fun out => out (nz ((G.mem_neighborFinset ..).mpr za))),za⟩,fun ⟨ak,za⟩ => ⟨Or.inr ak,za⟩⟩
  have inc : (X.erase x).erase y⊆X := (erase_subset ..).trans (erase_subset ..)
  constructor
  · intro k km
    obtain ⟨sub,sz⟩ := mem_powersetCard.mp (mem_filter.mp km).1
    exact mem_powersetCard.mpr ⟨sub.trans inc,sz⟩
  · intro k km
    obtain ⟨kp,recv,vd⟩ := mem_filter.mp km
    obtain ⟨sub,_⟩ := mem_powersetCard.mp kp
    have nk : x∉k := fun m => not_mem_erase x X ((erase_subset ..) (sub m))
    have nyk : y∉k := fun m => not_mem_erase y _ (sub m)
    have one := (move x nx k).trans recv
    exact ⟨mem_filter.mpr ⟨mem_sdiff.mpr ⟨xm,nk⟩,by omega⟩,mem_filter.mpr ⟨mem_sdiff.mpr ⟨ym,nyk⟩,
      (move y ny k).trans_lt (mem_filter.mp vd).2.2⟩,one⟩

/-- For a ten-subset of the 26-vertex pool and an interior edge with both
degrees between three and five, the oriented incidence mass is at least
251680. The bound is 539682 when both degrees are at most four. -/
theorem edge_mass (X : Finset V) (sz : X.card=26) {x y : V} (xm : x∈X) (ym : y∈X) (xy : G.Adj x y)
    (nx : G.neighborFinset x⊆X) (ny : G.neighborFinset y⊆X)
    (dx : 3 ≤ G.degree x ∧ G.degree x ≤ 5) (dy : 3 ≤ G.degree y ∧ G.degree y ≤ 5) :
    (if G.degree x ≤ 4 ∧ G.degree y ≤ 4 then 539682 else 251680) ≤ (edgeTrials G X x y).card := by
  classical
  let Y := (X.erase x).erase y
  let A := Y.filter (G.Adj x)
  let B := Y.filter (fun z => ¬G.Adj x z)
  let v := nbr G y Y
  let d := nbr G y B
  have yt : y∉Y := not_mem_erase y (X.erase x) 
  have yc : Y.card=24 := by
    change ((X.erase x).erase y).card=24
    rw [card_erase_of_mem (mem_erase.mpr ⟨xy.ne.symm,ym⟩),card_erase_of_mem xm,sz]
  have xeq : A=(G.neighborFinset x).erase y := by
    ext a; simp only [A,Y,mem_filter,mem_erase,mem_neighborFinset]
    exact ⟨fun ⟨m,e⟩ => ⟨m.1,e⟩,fun ⟨m,e⟩ => ⟨⟨m,e.ne.symm,nx ((G.mem_neighborFinset ..).mpr e)⟩,e⟩⟩
  have yeq : Y.filter (G.Adj y)=(G.neighborFinset y).erase x := by
    ext a; simp only [Y,mem_filter,mem_erase,mem_neighborFinset]
    exact ⟨fun ⟨m,e⟩ => ⟨m.2.1,e⟩,fun ⟨m,e⟩ => ⟨⟨e.ne.symm,m,ny ((G.mem_neighborFinset ..).mpr e)⟩,e⟩⟩
  have xc : A.card=G.degree x-1 := by
    rw [xeq,card_erase_of_mem ((G.mem_neighborFinset ..).mpr xy),card_neighborFinset_eq_degree]
  have vc : v=G.degree y-1 := by
    dsimp only [v,nbr]; rw [yeq,card_erase_of_mem ((G.mem_neighborFinset ..).mpr xy.symm),card_neighborFinset_eq_degree]
  have ab := filter_card_add_filter_neg_card_eq_card (s:=Y) (G.Adj x)
  change A.card+B.card=Y.card at ab
  have ac := filter_card_add_filter_neg_card_eq_card (s:=A) (G.Adj y)
  have ac2 := filter_card_add_filter_neg_card_eq_card (s:=Y.filter (G.Adj y)) (G.Adj x)
  have comm (p q : V → Prop) [DecidablePred p] [DecidablePred q] :
      (Y.filter p).filter q=(Y.filter q).filter p := by ext; simp [and_left_comm,and_comm,and_assoc]
  rw [comm (G.Adj y) (G.Adj x),comm (G.Adj y) (fun z => ¬G.Adj x z)] at ac2
  change (A.filter (G.Adj y)).card+d=v at ac2
  have sa : (A.filter (fun z => ¬G.Adj y z)).card=A.card+d-v := by omega
  have nz : v ≤ A.card+d := by omega
  have yr : d ≤ v := by omega
  have table : ∀i j t : Fin 5,2 ≤ i.val → 2 ≤ j.val → t.val ≤ j.val → j.val ≤ i.val+t.val →
      (if i.val ≤ 3 ∧ j.val ≤ 3 then 539682 else 251680) ≤ 
        i.val*(24-i.val-t.val).choose 9+(i.val+t.val-j.val)*t.val*(24-i.val-t.val).choose 8 := by
    simp only [Nat.choose_eq_fast_choose]; decide
  have tab := table ⟨A.card,by omega⟩ ⟨v,by omega⟩ ⟨d,by omega⟩ (by change 2 ≤ A.card; omega) (by change 2 ≤ v; omega) yr nz
  have formula := four_classes G Y x y yt (b:=9) (by decide)
  change (edgeTrials G X x y).card=A.card*(B.card-d).choose 9+
    (A.filter (fun z => ¬G.Adj y z)).card*d*(B.card-d).choose 8 at formula
  have nums : (G.degree x ≤ 4 ∧ G.degree y ≤ 4) ↔ (A.card ≤ 3 ∧ v ≤ 3) := by omega
  rw [formula,sa,show B.card=24-A.card by omega,if_congr nums rfl rfl]
  exact tab

end Graffiti384b.PendantRank
#print axioms Graffiti384b.PendantRank.internal_events
#print axioms Graffiti384b.PendantRank.edge_mass
