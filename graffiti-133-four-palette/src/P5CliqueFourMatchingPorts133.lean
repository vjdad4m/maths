import P5CliqueFourConsecutivePorts133

namespace Graffiti133P5CliqueArms
open SimpleGraph Finset Graffiti133Camby Graffiti133
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

private theorem graph_walk_crosses {U : Type*} {J : SimpleGraph U}
    (T : Set U) {a b : U} (w : J.Walk a b) (ha : a∈T) (hb : b∉T) :
    ∃ x∈T,∃ y∉T,J.Adj x y := by
  classical
  induction w with
  | nil => exact (hb ha).elim
  | @cons x y z e w ih =>
      by_cases hy : y∈T
      · exact ih hy hb
      · exact ⟨x,ha,y,hy,e⟩

/-- Any four nonisolated palette ports suffice, including the two disjoint
palette-edge case. Small cores force at least one pair inadmissible. -/
theorem four_port_nonisolated_ambient_mean_four
    (h4 : FourCycleFree G) (D : Finset V) (a b c d : V)
    (am : a∈D) (bm : b∈D) (cm : c∈D) (dm : d∈D)
    (ac : a≠c) (ad : a≠d) (bc : b≠c) (bd : b≠d)
    (ab : G.Adj a b) (cd : G.Adj c d)
    (attach : ∀ q∉D,∃ t∈({a,b,c,d} : Finset V),G.Adj q t)
    (palette : ∀ q∉D,∀ p∈D,G.Adj q p→p∈({a,b,c,d} : Finset V))
    (hc : (G.induce (D : Set V)).Connected) (h7 : NoPath (G.induce (D : Set V)) 7) :
    (∑ v : V,localIndependence G v)≤4*Fintype.card V := by
  classical
  by_cases e₁ : G.Adj a c
  · exact four_consecutive_ports_ambient_mean_four h4 D b a c d bm am cm dm ab.symm e₁ cd
      bc bd ad (by simpa [Finset.insert_comm a b] using attach)
      (by simpa [Finset.insert_comm a b] using palette) hc h7
  by_cases e₂ : G.Adj a d
  · have ep : ({b,a,d,c}:Finset V)={a,b,c,d} := by
      ext v
      simp only [Finset.mem_insert,Finset.mem_singleton]
      tauto
    exact four_consecutive_ports_ambient_mean_four h4 D b a d c bm am dm cm ab.symm e₂ cd.symm
      bd bc ac (ep.symm ▸ attach) (ep.symm ▸ palette) hc h7
  by_cases e₃ : G.Adj b c
  · exact four_consecutive_ports_ambient_mean_four h4 D a b c d am bm cm dm ab e₃ cd
      ac ad bd attach palette hc h7
  by_cases e₄ : G.Adj b d
  · have ep : ({a,b,d,c}:Finset V)={a,b,c,d} := by
      ext v
      simp only [Finset.mem_insert,Finset.mem_singleton]
      tauto
    exact four_consecutive_ports_ambient_mean_four h4 D a b d c am bm dm cm ab e₄ cd.symm
      ad ac bc (ep.symm ▸ attach) (ep.symm ▸ palette) hc h7
  let P : Finset V := {a,b,c,d}
  have sub : P⊆D := by
    intro x xm
    simp only [P,Finset.mem_insert,Finset.mem_singleton] at xm
    rcases xm with rfl|rfl|rfl|rfl <;> assumption
  have pc : P.card=4 := by simp [P,ab.ne,ac,ad,bc,bd,cd.ne]
  have all (p : V) (pp : p∈P) : ∃ t∈P,G.Adj p t := by
    simp only [P,Finset.mem_insert,Finset.mem_singleton] at pp
    rcases pp with rfl|rfl|rfl|rfl
    · exact ⟨b,by simp [P],ab⟩
    · exact ⟨a,by simp [P],ab.symm⟩
    · exact ⟨d,by simp [P],cd⟩
    · exact ⟨c,by simp [P],cd.symm⟩
  refine four_port_nonisolated_admissible_ambient_mean_four h4 D P sub pc attach palette all hc h7 ?_
  let S := P.powersetCard 2
  let A := S.filter (fun F=>¬∃ x∈D,∀ p∈F,G.Adj x p)
  have s6 : S.card=6 := by rw [Finset.card_powersetCard,pc]; decide
  by_cases large : 6≤D.card
  · exact (Finset.card_filter_le _ _).trans (s6 ▸ large)
  let J := G.induce (D : Set V)
  let L : Set (D : Set V) := {x | x.val=a ∨ x.val=b}
  let R : Set (D : Set V) := {x | x.val=c ∨ x.val=d}
  have noCross (x : (D : Set V)) (l : x∈L) (y : (D : Set V)) (r : y∈R) : ¬J.Adj x y := by
    change x.val=a ∨ x.val=b at l
    change y.val=c ∨ y.val=d at r
    change ¬G.Adj x.val y.val
    rcases l with q|q <;> rcases r with t|t <;> rw [q,t] <;> assumption
  have bridgeL : ∃ x : (D : Set V),x∉L ∧ x∉R ∧ ∃ y∈L,J.Adj x y := by
    have reach := hc.preconnected (⟨a,am⟩ : (D : Set V)) ⟨c,cm⟩
    refine reach.elim ?_
    intro w
    obtain ⟨y,yl,x,xl,e⟩ := graph_walk_crosses L w (Or.inl rfl)
      (show ¬((⟨c,cm⟩ : (D : Set V))∈L) from fun h=>h.elim ac.symm bc.symm)
    exact ⟨x,xl,fun xr=>noCross y yl x xr e,y,yl,e.symm⟩
  have bridgeR : ∃ x : (D : Set V),x∉L ∧ x∉R ∧ ∃ y∈R,J.Adj x y := by
    have reach := hc.preconnected (⟨c,cm⟩ : (D : Set V)) ⟨a,am⟩
    refine reach.elim ?_
    intro w
    obtain ⟨y,yr,x,xr,e⟩ := graph_walk_crosses R w (Or.inl rfl)
      (show ¬((⟨a,am⟩ : (D : Set V))∈R) from fun h=>h.elim ac ad)
    exact ⟨x,fun xl=>noCross x xl y yr e.symm,xr,y,yr,e.symm⟩
  obtain ⟨x,xl,xr,p,pl,xp⟩ := bridgeL
  obtain ⟨y,yl,yr,q,qr,yq⟩ := bridgeR
  have np (z : (D : Set V)) (l : z∉L) (r : z∉R) : z.val∉P := by
    simp only [P,Finset.mem_insert,Finset.mem_singleton]
    exact fun e=>e.elim (fun h=>l (Or.inl h)) (fun e=>e.elim (fun h=>l (Or.inr h)) r)
  have sx : (D\P).card≤1 := by
    have eq := Finset.card_sdiff_add_card_eq_card sub
    omega
  have eq : x=y := Subtype.ext (Finset.card_le_one.mp sx _ (Finset.mem_sdiff.mpr ⟨x.property,np x xl xr⟩)
    _ (Finset.mem_sdiff.mpr ⟨y.property,np y yl yr⟩))
  subst y
  have pP : p.val∈P := by
    change p.val=a ∨ p.val=b at pl
    rcases pl with e|e <;> simp [P,e]
  have qP : q.val∈P := by
    change q.val=c ∨ q.val=d at qr
    rcases qr with e|e <;> simp [P,e]
  have ne : p.val≠q.val := by
    change p.val=a ∨ p.val=b at pl
    change q.val=c ∨ q.val=d at qr
    rcases pl with ep|ep <;> rcases qr with eq|eq <;> rw [ep,eq] <;> assumption
  let X : Finset V := {p.val,q.val}
  have xm : X∈S := Finset.mem_powersetCard.mpr ⟨by simp [X,Finset.insert_subset_iff,pP,qP],by simp [X,ne]⟩
  have xa : X∉A := by
    intro xm
    apply (Finset.mem_filter.mp xm).2
    refine ⟨x.val,x.property,?_⟩
    intro z zm
    simp only [X,Finset.mem_insert,Finset.mem_singleton] at zm
    rcases zm with rfl|rfl <;> assumption
  have subX : A⊆S.erase X := fun F fm=>Finset.mem_erase.mpr ⟨fun e=>xa (e ▸ fm),
    (Finset.mem_filter.mp fm).1⟩
  have le := Finset.card_le_card subX
  have ce := Finset.card_erase_add_one xm
  have dx : 5≤D.card := by
    have eq := Finset.card_sdiff_add_card_eq_card sub
    have pos : 0<(D\P).card := Finset.card_pos.mpr
      ⟨x.val,Finset.mem_sdiff.mpr ⟨x.property,np x xl xr⟩⟩
    omega
  change A.card≤D.card
  omega

#print axioms four_port_nonisolated_ambient_mean_four
end Graffiti133P5CliqueArms
