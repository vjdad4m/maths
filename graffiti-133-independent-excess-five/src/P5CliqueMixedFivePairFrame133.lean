import P5CliqueMixedHighGeometry133

namespace Graffiti133P5CliqueArms.FivePairFrame
open SimpleGraph Finset Graffiti133 Graffiti133Camby
open scoped Classical
set_option maxHeartbeats 5000000
set_option maxRecDepth 140000
set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

def siteMask : Fin 5→Finset (Fin 4) := ![{0,1},{0,2},{0,3},{1,2},{1,3}]
def parentSite : Fin 5→Fin 8→Fin 5 := ![![1,1,2,2,3,3,4,4],![0,0,2,2,3,3,4,4],![0,0,1,1,3,3,4,4],![0,0,1,1,2,2,4,4],![0,0,1,1,2,2,3,3]]
def leafColor : Fin 5→Fin 8→Fin 4 := ![![1,3,1,2,0,3,0,2],![2,3,1,2,0,3,0,2],![2,3,1,3,0,3,0,2],![2,3,1,3,1,2,0,2],![2,3,1,3,1,2,0,3]]

abbrev Role := Fin 4 ⊕ (Fin 5 ⊕ Fin 8)

def decode (i : Fin 17) : Role :=
  if h : i.val<4 then .inl ⟨i.val,h⟩
  else if hi : i.val<9 then .inr (.inl ⟨i.val-4,by omega⟩)
  else .inr (.inr ⟨i.val-9,by omega⟩)

theorem decode_inj : Function.Injective decode := by
  have p : ∀ i j : Fin 17,decode i=decode j→i=j := by decide
  exact fun _ _ e=>p _ _ e

private theorem site_card (i : Fin 5) : (siteMask i).card=2 := by
  have p : ∀ i : Fin 5,(siteMask i).card=2 := by decide
  exact p i

private theorem site_inj : Function.Injective siteMask := by
  have p : ∀ i j : Fin 5,siteMask i=siteMask j→i=j := by decide
  exact fun _ _ e=>p _ _ e

theorem foreign_leaf_color (b : Fin 5) (i : Fin 8) : leafColor b i∉siteMask (parentSite b i) := by
  have q : ∀ (b : Fin 5) (i : Fin 8),leafColor b i∉siteMask (parentSite b i) := by decide
  exact q b i

private theorem leaves_color_parent_inj (b : Fin 5) (i j : Fin 8)
    (he : parentSite b i=parentSite b j) (cc : leafColor b i=leafColor b j) : i=j := by
  have q : ∀ (b : Fin 5) (i j : Fin 8),parentSite b i=parentSite b j→leafColor b i=leafColor b j→i=j := by decide
  exact q b i j he cc

structure Host (G : SimpleGraph V) (D : Finset V) (p : Fin 4→V)
    (q : Fin 5→V) (L : Fin 8→V) (b : Fin 5) : Prop where
  pin : ∀ i,p i∈D
  pi : Function.Injective p
  ind : ∀ i j,¬G.Adj (p i) (p j)
  qout : ∀ i,q i∉D
  qtag : ∀ i j,G.Adj (q i) (p j)↔j∈siteMask i
  lout : ∀ i,L i∉D
  lpure : ∀ i w,w∈D→(G.Adj (L i) w↔w=p (leafColor b i))
  arm : ∀ i,G.Adj (q (parentSite b i)) (L i)
  siblingNo : ∀ i j,i≠j→parentSite b i=parentSite b j→¬G.Adj (L i) (L j)

def value (p : Fin 4→V) (q : Fin 5→V) (L : Fin 8→V) : Role→V
  | .inl i => p i
  | .inr (.inl j) => q j
  | .inr (.inr k) => L k

private def fixedSiteLeaf (b : Fin 5) (i : Fin 5) (j : Fin 8) : Option Bool :=
  if i=parentSite b j then some true
  else if (siteMask i∩siteMask (parentSite b j)).Nonempty then some false
  else none

private def fixedLeaves (b : Fin 5) (i j : Fin 8) : Option Bool :=
  if parentSite b i=parentSite b j then some false
  else if leafColor b j∈siteMask (parentSite b i) ∧ leafColor b i∈siteMask (parentSite b j) then some false
  else none

def fixed (b : Fin 5) : Role→Role→Option Bool
  | .inl _,.inl _ => some false
  | .inl i,.inr (.inl j) => some (decide (i∈siteMask j))
  | .inr (.inl j),.inl i => some (decide (i∈siteMask j))
  | .inl i,.inr (.inr j) => some (decide (i=leafColor b j))
  | .inr (.inr j),.inl i => some (decide (i=leafColor b j))
  | .inr (.inl i),.inr (.inl j) => if i=j then some false else none
  | .inr (.inl i),.inr (.inr j) => fixedSiteLeaf b i j
  | .inr (.inr j),.inr (.inl i) => fixedSiteLeaf b i j
  | .inr (.inr i),.inr (.inr j) => fixedLeaves b i j

variable {D : Finset V} {p : Fin 4→V} {q : Fin 5→V} {L : Fin 8→V} {b : Fin 5}

private theorem site_value_inj (H : Host G D p q L b) : Function.Injective q := by
  intro i j eq
  apply site_inj
  ext t
  rw [←H.qtag i t,←H.qtag j t,eq]

private theorem site_ne_leaf (H : Host G D p q L b) (i : Fin 5) (j : Fin 8) :
    q i≠L j := by
  intro eq
  have sub : siteMask i⊆{leafColor b j} := by
    intro k km
    have ad := (H.qtag i k).mpr km
    rw [eq] at ad
    exact Finset.mem_singleton.mpr (H.pi ((H.lpure j _ (H.pin k)).mp ad))
  have c := Finset.card_le_card sub
  rw [site_card,Finset.card_singleton] at c
  omega

private theorem leaf_value_inj (h4 : FourCycleFree G) (H : Host G D p q L b) :
    Function.Injective L := by
  intro i j eq
  have ci : leafColor b i=leafColor b j := by
    have h : G.Adj (L i) (p (leafColor b i)) := (H.lpure i _ (H.pin _)).mpr rfl
    rw [eq] at h
    exact H.pi ((H.lpure j _ (H.pin _)).mp h)
  have occupied (a : Fin 8) :
      ((Finset.univ : Finset (Fin 4)).filter (fun j=>G.Adj (q (parentSite b a)) (p j))).card=2 := by
    have he : (Finset.univ : Finset (Fin 4)).filter (fun j=>G.Adj (q (parentSite b a)) (p j)) =
        siteMask (parentSite b a) := by
      ext j
      simp [H.qtag]
    rw [he,site_card]
  have miss (a : Fin 8) : ¬G.Adj (q (parentSite b a)) (p (leafColor b a)) :=
    fun had=>foreign_leaf_color b a ((H.qtag _ _).mp had)
  have he := unique_mixed_center_at_pure_foreign_leaf h4 D p H.pin
    (q (parentSite b i)) (q (parentSite b j)) (L i) (H.lout i) (H.arm i)
    (eq.symm ▸ H.arm j) (leafColor b i) (miss i) (ci.symm ▸ miss j)
    ((occupied i).symm ▸ le_rfl) ((occupied j).symm ▸ le_rfl)
  exact leaves_color_parent_inj b i j (site_value_inj H he) ci

theorem value_injective (h4 : FourCycleFree G) (H : Host G D p q L b) :
    Function.Injective (value p q L) := by
  intro x y eq
  rcases x with i|(i|i) <;> rcases y with j|(j|j)
  · exact congrArg Sum.inl (H.pi eq)
  · change p i=q j at eq
    exact (H.qout j (eq ▸ H.pin i)).elim
  · change p i=L j at eq
    exact (H.lout j (eq ▸ H.pin i)).elim
  · change q i=p j at eq
    exact (H.qout i (eq.symm ▸ H.pin j)).elim
  · exact congrArg (fun x=>Sum.inr (Sum.inl x)) (site_value_inj H eq)
  · exact (site_ne_leaf H i j eq).elim
  · change L i=p j at eq
    exact (H.lout i (eq.symm ▸ H.pin j)).elim
  · exact (site_ne_leaf H j i eq.symm).elim
  · exact congrArg (fun x=>Sum.inr (Sum.inr x)) (leaf_value_inj h4 H eq)

private theorem fixedSiteLeaf_sound (h4 : FourCycleFree G) (H : Host G D p q L b)
    (i : Fin 5) (j : Fin 8) (c : Bool) (eq : fixedSiteLeaf b i j=some c) :
    G.Adj (q i) (L j) ↔ c=true := by
  unfold fixedSiteLeaf at eq
  by_cases home : i=parentSite b j
  · rw [if_pos home] at eq
    have cT : c=true := (Option.some.inj eq).symm
    rw [cT,home]
    exact ⟨fun _=>rfl,fun _=>H.arm j⟩
  rw [if_neg home] at eq
  by_cases shared : (siteMask i∩siteMask (parentSite b j)).Nonempty
  · rw [if_pos shared] at eq
    have cF : c=false := (Option.some.inj eq).symm
    rw [cF]
    obtain ⟨k,km⟩ := shared
    obtain ⟨ki,kj⟩ := Finset.mem_inter.mp km
    refine ⟨fun bad=>?_,fun bad=>Bool.noConfusion bad⟩
    have e := h4 (q i) (q (parentSite b j)) (p k) (L j) (fun e=>home (site_value_inj H e))
      ((H.qtag i k).mpr ki) ((H.qtag _ k).mpr kj) bad (H.arm j)
    exact (H.lout j (e ▸ H.pin _)).elim
  simp [shared] at eq

private theorem fixedLeaves_sound (h4 : FourCycleFree G) (H : Host G D p q L b)
    (i j : Fin 8) (c : Bool) (eq : fixedLeaves b i j=some c) :
    G.Adj (L i) (L j) ↔ c=true := by
  unfold fixedLeaves at eq
  by_cases same : parentSite b i=parentSite b j
  · rw [if_pos same] at eq
    have cF : c=false := (Option.some.inj eq).symm
    rw [cF]
    refine ⟨fun bad=>?_,fun bad=>Bool.noConfusion bad⟩
    by_cases ij : i=j
    · subst j
      exact (G.loopless _ bad).elim
    exact (H.siblingNo i j ij same bad).elim
  rw [if_neg same] at eq
  by_cases conflict : leafColor b j∈siteMask (parentSite b i) ∧ leafColor b i∈siteMask (parentSite b j)
  · rw [if_pos conflict] at eq
    have cF : c=false := (Option.some.inj eq).symm
    rw [cF]
    refine ⟨fun bad=>?_,fun bad=>Bool.noConfusion bad⟩
    have qj : G.Adj (q (parentSite b i)) (p (leafColor b j)) := (H.qtag _ _).mpr conflict.1
    have Lj : G.Adj (L j) (p (leafColor b j)) := (H.lpure j _ (H.pin _)).mpr rfl
    have e := h4 (L i) (p (leafColor b j)) (q (parentSite b i)) (L j)
      (fun e=>H.lout i (e.symm ▸ H.pin _)) (H.arm i).symm qj.symm bad Lj.symm
    exact (site_ne_leaf H _ _ e).elim
  simp [conflict] at eq

theorem fixed_sound (h4 : FourCycleFree G) (H : Host G D p q L b) (x y : Role) (c : Bool)
    (eq : fixed b x y=some c) : G.Adj (value p q L x) (value p q L y)↔c=true := by
  rcases x with i|(i|i) <;> rcases y with j|(j|j)
  · have h : c=false := (Option.some.inj eq).symm
    rw [h]
    exact ⟨fun e=>(H.ind i j e).elim,fun h=>Bool.noConfusion h⟩
  · have h : c=decide (i∈siteMask j) := (Option.some.inj eq).symm
    change G.Adj (p i) (q j) ↔ c=true
    rw [h,decide_eq_true_eq,SimpleGraph.adj_comm]
    exact H.qtag j i
  · have h : c=decide (i=leafColor b j) := (Option.some.inj eq).symm
    change G.Adj (p i) (L j)↔c=true
    rw [h,decide_eq_true_eq,SimpleGraph.adj_comm,H.lpure j _ (H.pin i)]
    exact H.pi.eq_iff
  · have h : c=decide (j∈siteMask i) := (Option.some.inj eq).symm
    change G.Adj (q i) (p j)↔c=true
    rw [h,decide_eq_true_eq]
    exact H.qtag i j
  · change (if i=j then some false else none)=some c at eq
    by_cases ij : i=j
    · subst j
      simp only [if_true,Option.some.injEq] at eq
      exact ⟨fun x=>(G.loopless _ x).elim,fun x=>Bool.noConfusion (eq.trans x)⟩
    simp [ij] at eq
  · exact fixedSiteLeaf_sound h4 H i j c eq
  · have h : c=decide (j=leafColor b i) := (Option.some.inj eq).symm
    change G.Adj (L i) (p j)↔c=true
    rw [h,decide_eq_true_eq,H.lpure i _ (H.pin j)]
    exact H.pi.eq_iff
  · change G.Adj (L i) (q j) ↔ _
    rw [SimpleGraph.adj_comm]
    exact fixedSiteLeaf_sound h4 H j i c eq
  · exact fixedLeaves_sound h4 H i j c eq

#print axioms fixed_sound
#print axioms value_injective
end Graffiti133P5CliqueArms.FivePairFrame
