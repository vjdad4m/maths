import ActiveRank
import InternalEdge
namespace Graffiti384b.PendantRank
open Finset SimpleGraph Donor
open private FiniteRange.bad from FiniteRange384b
open private Donor.rankDegree from PendantBudget
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def Usable (X : Finset V) (Q : Finset (Finset V)) : Prop :=
  Q⊆X.powersetCard 10 ∧ ∀k∈Q,∃x∈FiniteRange.bad G X k,∃y∈FiniteRange.bad G X k,
    G.Adj x y ∧ nbr G x (Xᶜ∪k)=1

/-- An exposed low vertex or an edge between two low vertices in the pool.
The endpoints of the edge may themselves be exposed. -/
def LowFeature (X : Finset V) (d : ℕ) : Prop :=
  (∃x∈exposed G X,G.degree x≤d) ∨
  ∃x∈X,∃y∈X,G.Adj x y ∧ G.degree x≤d ∧ G.degree y≤d

private theorem via_feature (X : Finset V) (sz : X.card=26) (highX : X⊆high G)
    (d : ℕ) (level : d=4 ∨ d=5) (geometry : LowFeature G X d) :
    ∃Q,Usable G X Q ∧ (if d=4 then 539682 else 251680)≤(∑v∈X,marked G X v)+Q.card := by
  classical
  have ext (x : V) (xm : x∈exposed G X) (small : G.degree x≤d) :
      ∃Q,Usable G X Q ∧ (if d=4 then 539682 else 251680)≤(∑v∈X,marked G X v)+Q.card := by
    refine ⟨∅,⟨empty_subset _,by simp⟩,?_⟩
    have below := single_le_sum (s:=X) (f:=marked G X) (fun _ _ => Nat.zero_le _) (mem_filter.mp xm).1
    rw [marked,if_pos xm] at below
    simp only [card_empty,Nat.add_zero]
    exact (show (if d=4 then 539682 else 251680)≤tariff (G.degree x) by unfold tariff; split_ifs <;> omega).trans below
  rcases geometry with ⟨x,xm,dx⟩|⟨x,xm,y,ym,xy,dx,dy⟩
  · exact ext x xm dx
  by_cases xe : x∈exposed G X
  · exact ext x xe dx
  by_cases ye : y∈exposed G X
  · exact ext y ye dy
  have interior {z : V} (zm : z∈X) (ne : z∉exposed G X) : G.neighborFinset z⊆X := by
    intro a am
    by_contra na
    exact ne (mem_filter.mpr ⟨zm,a,na,(G.mem_neighborFinset ..).mp am⟩)
  have nx := interior xm xe
  have ny := interior ym ye
  obtain ⟨qs,win⟩ := internal_events G X xm ym nx ny
  have amount := edge_mass G X sz xm ym xy nx ny ⟨(mem_filter.mp (highX xm)).2,by omega⟩
    ⟨(mem_filter.mp (highX ym)).2,by omega⟩
  refine ⟨edgeTrials G X x y,⟨qs,?_⟩,?_⟩
  · intro k km
    obtain ⟨xb,yb,one⟩ := win k km
    exact ⟨x,xb,y,yb,xy,one⟩
  · split_ifs at * <;> omega

/-- The exact charge inequality is sufficient with any family of usable
second-pair events. Their endpoints may vary from trial to trial. -/
theorem exact_from_mass (X : Finset V) (sz : X.card=26)
    (inj : Set.InjOn (trianglesAt G) (X:Set V)) (pos : ∀v∈X,2≤trianglesAt G v)
    {e : V} (ex : e∉X) (outside : ∀x∈X,¬G.Adj e x) (degree : 2≤G.degree e)
    (floor p : ℕ) (pcap : p≤290000) (fs : floor≤8) (degrees : ∀v∈X,floor≤G.degree v)
    (Q : Finset (Finset V)) (valid : Usable G X Q)
    (budget : (∑i∈range 26,envelope floor p i) <
      26*base+3*(26:ℕ).choose 10+(exposed G X).card*p+(∑v∈X,marked G X v)+Q.card) :
    gamma G≤Fintype.card V-15 := by
  classical
  by_contra! fail
  have enough := card_le_univ X
  have each (k : Finset V) (km : k∈X.powersetCard 10) :
      3+(active G X k).card+(if k∈Q then 1 else 0)≤(FiniteRange.bad G X k).card := by
    obtain ⟨ks,kb⟩ := mem_powersetCard.mp km
    have h := trial G X k ks inj ex outside degree (if k∈Q then 1 else 0) (by
      split_ifs with hit
      · exact Or.inr ⟨rfl,valid.2 k hit⟩
      · exact Or.inl rfl)
    omega
  have lo := sum_le_sum each
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,card_powersetCard,sz,sum_boole,Nat.cast_id,
    filter_mem_eq_inter,inter_eq_right.mpr valid.1] at lo
  have hi := rank_budget G X sz inj pos floor p pcap fs degrees
  omega

/-- The two exposure thresholds in each row are reduced further by an
exposed low vertex or a low-degree edge. -/
def Geometry (X : Finset V) : Prop :=
  let n := (exposed G X).card
  (10≤n ∨ 9≤n ∧ LowFeature G X 5 ∨ 8≤n ∧ LowFeature G X 4) ∨
  (∀x∈X,4≤G.degree x) ∧ (8≤n ∨ 7≤n ∧ LowFeature G X 5 ∨ 5≤n ∧ LowFeature G X 4) ∨
  (∀x∈X,5≤G.degree x)

theorem frame (X : Finset V) (sz : X.card=26) (highX : X⊆high G)
    (inj : Set.InjOn (trianglesAt G) (X:Set V)) (pos : ∀v∈X,2≤trianglesAt G v)
    {e : V} (ex : e∉X) (outside : ∀x∈X,¬G.Adj e x) (degree : 2≤G.degree e)
    (regime : Geometry G X) : gamma G≤Fintype.card V-15 := by
  classical
  let n := (exposed G X).card
  have valid0 : Usable G X ∅ := ⟨empty_subset _,by simp⟩
  have certificates : ∀ f∈({3,4,5}:Finset ℕ),
      (∑i∈range 26,envelope f (if f=5 then 0 else if f=4 then 170000 else 290000) i)=26*base+
      (if f=3 then 18720787 else if f=4 then 17247282 else 15231762) := by
    unfold envelope charge reward base Donor.rankDegree FiniteRange.badCount
    simp only [mem_insert,mem_singleton,Nat.choose_eq_fast_choose]
    intro f h
    rcases h with rfl|rfl|rfl <;> decide
  have win (f : ℕ) (fm : f∈({3,4,5}:Finset ℕ)) (deg : ∀x∈X,f≤G.degree x) (Q : Finset (Finset V))
      (valid : Usable G X Q) (cost : (if f=3 then 18720787 else if f=4 then 17247282 else 15231762) <
        15935205+n*(if f=5 then 0 else if f=4 then 170000 else 290000)+(∑v∈X,marked G X v)+Q.card) : gamma G≤Fintype.card V-15 := by
    have opts : f=3 ∨ f=4 ∨ f=5 := by simpa only [mem_insert,mem_singleton] using fm
    apply exact_from_mass G X sz inj pos ex outside degree f (if f=5 then 0 else if f=4 then 170000 else 290000) (by split_ifs <;> decide) (by omega) deg Q valid
    rw [certificates f fm,show 3*(26:ℕ).choose 10=15935205 by decide]
    dsimp only [n] at cost
    omega
  rcases regime with cases|⟨deg,cases⟩|deg
  · have h3 : ∀x∈X,3≤G.degree x := fun _ xm => (mem_filter.mp (highX xm)).2
    rcases cases with ten|⟨nine,low⟩|⟨eight,low⟩
    · apply win 3 (by decide) h3 ∅ valid0
      change 18720787<15935205+n*290000+(∑v∈X,marked G X v)+0; change 10≤n at ten; omega
    · obtain ⟨Q,ok,amt⟩ := via_feature G X sz highX 5 (by decide) low
      apply win 3 (by decide) h3 Q ok
      change 18720787<15935205+n*290000+(∑v∈X,marked G X v)+Q.card
      change 251680≤(∑v∈X,marked G X v)+Q.card at amt
      change 9≤n at nine; omega
    · obtain ⟨Q,ok,amt⟩ := via_feature G X sz highX 4 (by decide) low
      apply win 3 (by decide) h3 Q ok
      change 18720787<15935205+n*290000+(∑v∈X,marked G X v)+Q.card
      change 539682≤(∑v∈X,marked G X v)+Q.card at amt
      change 8≤n at eight; omega
  · rcases cases with eight|⟨seven,low⟩|⟨five,low⟩
    · apply win 4 (by decide) deg ∅ valid0
      change 17247282<15935205+n*170000+(∑v∈X,marked G X v)+0; change 8≤n at eight; omega
    · obtain ⟨Q,ok,amt⟩ := via_feature G X sz highX 5 (by decide) low
      apply win 4 (by decide) deg Q ok
      change 17247282<15935205+n*170000+(∑v∈X,marked G X v)+Q.card
      change 251680≤(∑v∈X,marked G X v)+Q.card at amt
      change 7≤n at seven; omega
    · obtain ⟨Q,ok,amt⟩ := via_feature G X sz highX 4 (by decide) low
      apply win 4 (by decide) deg Q ok
      change 17247282<15935205+n*170000+(∑v∈X,marked G X v)+Q.card
      change 539682≤(∑v∈X,marked G X v)+Q.card at amt
      change 5≤n at five; omega
  · apply win 5 (by decide) deg ∅ valid0
    change 15231762<15935205+n*0+(∑v∈X,marked G X v)+0; omega

/-- The distinguished vertex can be a pendant-triangle ear or have any other
attachment outside the 26 high vertices. No edge between its neighbors is needed. -/
theorem high27 (t : (types G).card=29) (h : (high G).card=27) {w e : V}
    (wh : w∈high G) (ex : e∉(high G).erase w) (outside : ∀x∈(high G).erase w,¬G.Adj e x)
    (degree : 2≤G.degree e) (geo : Geometry G ((high G).erase w)) :
    gamma G≤Fintype.card V-15 := by
  let X := (high G).erase w
  have sz : X.card=26 := by rw [show X=(high G).erase w from rfl,card_erase_of_mem wh,h]
  have sub : X⊆high G := erase_subset ..
  obtain ⟨inj,rich,_,_⟩ := Repair.maximal_diversity G (by omega)
  exact frame G X sz sub (inj.mono sub) (fun x xm => rich x (sub xm)) ex outside degree geo

/-- An ear with a high neighbor and a neighbor of degree at most two.
This includes the pendant triangle, the leaf attachment, and a pair of
adjacent ears whose other endpoints are distinct. -/
theorem low_mate (t : (types G).card=29) (h : (high G).card=27) {e w v : V}
    (wh : w∈high G) (wv : w≠v) (neigh : G.neighborFinset e={w,v}) (low : G.degree v≤2)
    (geo : Geometry G ((high G).erase w)) : gamma G≤Fintype.card V-15 := by
  have de : G.degree e=2 := by rw [←card_neighborFinset_eq_degree,neigh,card_pair wv]
  have out {z : V} (d : G.degree z≤2) : z∉(high G).erase w := by
    intro m
    have H := (mem_filter.mp (mem_erase.mp m).2).2
    omega
  apply high27 G t h wh (out de.le) _ de.ge geo
  intro x xm ex
  have xt := (G.mem_neighborFinset ..).mpr ex
  rw [neigh,mem_insert,mem_singleton] at xt
  exact xt.elim (mem_erase.mp xm).1 (fun eq => out low (eq ▸ xm))

end Graffiti384b.PendantRank
#print axioms Graffiti384b.PendantRank.exact_from_mass
#print axioms Graffiti384b.PendantRank.frame
#print axioms Graffiti384b.PendantRank.high27
#print axioms Graffiti384b.PendantRank.low_mate
