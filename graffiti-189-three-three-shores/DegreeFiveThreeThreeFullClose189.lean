import DegreeFiveThreeThreeNeitherClose189
import DegreeFiveThreeThreeUniversalClose189
import DegreeFiveActualCutSwap189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private Shore shore_off shore_closed shore_disjoint from DegreeFiveActualCut189
open private Cmp count_cut_degree_on_two_shores portColor from DegreeFiveThreeForeignImpossible189
open private swapCut from DegreeFiveActualCutSwap189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

theorem three_three_high_cut_covers_all
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ x y : V,x≠y → 5≤G.degree x ∨ 5≤G.degree y)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ x : V,x=a ∨ x=b ∨ x∈Shore C ∨ x∈Shore D)
    (C3 : (cutPorts C).card=3) (D3 : (cutPorts D).card=3)
    (a5 : 5≤G.degree a) :
    (∀ x∈cutPorts C,G.Adj a x) ∧ (∀ x∈cutPorts D,G.Adj a x) := by
  classical
  let P := G.neighborFinset a
  have nh : ∀ x : V,x∈P ↔ G.Adj a x := fun x=>mem_neighborFinset G a x
  have aCnt : 5≤P.card := by simpa [P] using a5
  have pSub : P⊆cutPorts C∪cutPorts D := by
    intro x xp
    have ax := (nh x).mp xp
    rcases cover x with e|e|xc|xd
    · exact (G.loopless a (e ▸ ax)).elim
    · have d := dist_eq_one_iff_adj.mpr (e ▸ ax : G.Adj a b)
      omega
    · exact mem_union_left _ (mem_filter.mpr ⟨xc,.inl ax⟩)
    exact mem_union_right _ (mem_filter.mpr ⟨xd,.inl ax⟩)
  apply Classical.byContradiction
  intro no
  have nt : P≠cutPorts C∪cutPorts D := by
    intro e
    exact no ⟨fun x xp=>(nh x).mp (e.symm ▸ mem_union_left _ xp),
      fun x xp=>(nh x).mp (e.symm ▸ mem_union_right _ xp)⟩
  have dis : Disjoint (cutPorts C) (cutPorts D) :=
    (shore_disjoint cd).mono (filter_subset _ _) (filter_subset _ _)
  obtain ⟨f,hf,hh⟩ := Graffiti189.one_missing_of_two_triples (cutPorts C) (cutPorts D) P
    C3 D3 dis pSub aCnt nt
  have stage (X Y : Cmp (G:=G) (a:=a) (b:=b)) (xy : X≠Y)
      (cv : ∀ v : V,v=a ∨ v=b ∨ v∈Shore X ∨ v∈Shore Y)
      (Y3 : (cutPorts Y).card=3)
      (fx : f∈cutPorts X) (ys : cutPorts Y⊆P)
      (xs : (cutPorts X).erase f⊆P) (x2 : ((cutPorts X).erase f).card=2) : False := by
    obtain ⟨p,q,pq,eq⟩ := card_eq_two.mp x2
    have pm : p∈(cutPorts X).erase f := by simp [eq]
    have qm : q∈(cutPorts X).erase f := by simp [eq]
    have pf := (mem_erase.mp pm).1
    have qf := (mem_erase.mp qm).1
    have all : cutPorts X={p,q,f} := by
      rw [←insert_erase fx,eq]
      ext x
      simp [or_comm,or_left_comm,or_assoc]
    have af : ¬G.Adj a f := fun h=>hf ((nh f).mpr h)
    have bf := ((mem_filter.mp fx).2).resolve_left af
    let F : FiveMissShore33 X Y p q f :=
      ⟨xy,pq,pf,qf,all,(fun x xp=>(nh x).mp (ys xp)),
        (nh p).mp (xs pm),(nh q).mp (xs qm),af,bf⟩
    exact F.no_local_shape hc two even conn degree cv Y3
  rcases hh with ⟨fc,allD,cSub,c2⟩|⟨fd,allC,dSub,d2⟩
  · exact stage C D cd cover D3 fc allD cSub c2
  exact stage D C cd.symm (fun x=>(cover x).imp id (fun h=>h.imp id Or.symm)) C3 fd allC dSub d2

theorem traceable_of_actual_five_three_three_ports
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ x y : V,x≠y → 5≤G.degree x ∨ 5≤G.degree y)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ x : V,x=a ∨ x=b ∨ x∈Shore C ∨ x∈Shore D)
    (C3 : (cutPorts C).card=3) (D3 : (cutPorts D).card=3) :
    ∃ x y,∃ p : G.Walk x y,p.IsPath ∧ ∀ v,v∈p.support := by
  have ab : a≠b := by intro e; rw [e,dist_self] at two; omega
  rcases degree a b ab with a5|b5
  · have h := three_three_high_cut_covers_all hc two even conn degree cd cover C3 D3 a5
    exact traceable_of_actual_five_three_three_universal_cut hc two even conn degree cd cover C3 D3 h.1 h.2
  let Cs := swapCut C
  let Ds := swapCut D
  have sc : Shore Cs=Shore C := shore_swapCut C
  have sd : Shore Ds=Shore D := shore_swapCut D
  have cp : cutPorts Cs=cutPorts C := by simp [cutPorts,sc,or_comm]
  have dp : cutPorts Ds=cutPorts D := by simp [cutPorts,sd,or_comm]
  have csd : Cs≠Ds := fun e=>cd (swapCut.injective e)
  have ts : G.dist b a=2 := by rwa [SimpleGraph.dist_comm]
  have cv (x : V) : x=b ∨ x=a ∨ x∈Shore Cs ∨ x∈Shore Ds := by
    rw [sc,sd]
    simpa [or_comm,or_left_comm,or_assoc] using cover x
  have cs3 : (cutPorts Cs).card=3 := by rwa [cp]
  have ds3 : (cutPorts Ds).card=3 := by rwa [dp]
  have h := three_three_high_cut_covers_all hc ts even conn degree csd cv cs3 ds3 b5
  exact traceable_of_actual_five_three_three_universal_cut hc ts even conn degree csd cv cs3 ds3 h.1 h.2

#print axioms three_three_high_cut_covers_all
#print axioms traceable_of_actual_five_three_three_ports
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
