import SquareCapFactor
import Mathlib.Tactic.FinCases

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.T2AvoidCounterexample
open SquareCap (IsTile FactorOn omitEdge)
abbrev V := Fin 14
def edges : List (V×V) :=
  [(0,1),(0,8),(0,11),(1,7),(1,12),(2,3),(2,4),(2,13),(3,5),(3,12),
    (4,8),(4,10),(5,7),(5,11),(6,10),(6,11),(6,13),(7,13),(8,9),(9,10),(9,12)]

private theorem loop : ∀ x : V,(x,x)∉edges := by decide

def G : SimpleGraph V where
  Adj a b := (a,b)∈edges∨(b,a)∈edges
  symm := fun _ _ e=>e.elim Or.inr Or.inl
  loopless x h := loop x (h.elim id id)

instance : DecidableRel G.Adj :=
  fun a b=>inferInstanceAs (Decidable ((a,b)∈edges∨(b,a)∈edges))

def target := omitEdge G 9 10
def alive : Finset V := (univ.erase 4).erase 8

instance : DecidableRel target.Adj :=
  fun a b=>inferInstanceAs (Decidable (G.Adj a b∧¬((a=9∧b=10)∨(a=10∧b=9))))

theorem domain_shape : (∀ x,G.degree x=3) ∧ G.Adj 4 8 ∧ G.Adj 9 10 ∧
    Fintype.card V%6=2 := by decide

private theorem tile_repr {A : Finset V} (h : IsTile target A) :
    ∃ c u v : V,A={c,u,v} ∧ c≠u∧c≠v∧u≠v∧target.Adj c u∧target.Adj c v := by
  obtain ⟨size,c,hc,star⟩ := h
  have two : (A.erase c).card=2 := by rw [card_erase_of_mem hc,size]
  obtain ⟨u,hu,v,hv,uv⟩ := one_lt_card.mp (by omega : 1<(A.erase c).card)
  obtain ⟨uc,uu⟩ := mem_erase.mp hu
  obtain ⟨vc,vv⟩ := mem_erase.mp hv
  have eq : ({c,u,v}:Finset V)=A := by
    apply eq_of_subset_of_card_le
    · intro q hq
      simp only [mem_insert,mem_singleton] at hq
      rcases hq with rfl|rfl|rfl <;> assumption
    · rw [size]
      simp [card_insert_of_not_mem,uc.symm,vc.symm,uv]
  exact ⟨c,u,v,eq.symm,uc.symm,vc.symm,uv,star u uu uc,star v vv vc⟩

def tile (c u v : V) : Finset V := {c,u,v}
def embeds (A : Finset V) (c u v : V) : Prop :=
  c∈A ∧ u∈A ∧ v∈A ∧ c≠u ∧ c≠v ∧ u≠v ∧ target.Adj c u ∧ target.Adj c v
instance (A : Finset V) (c u v : V) : Decidable (embeds A c u v) := by
  unfold embeds; infer_instance

private theorem find_triple {A K : Finset V} (h : IsTile target A) (sub : A⊆K) :
    ∃ c u v : V,A=tile c u v ∧ embeds K c u v := by
  obtain ⟨c,u,v,eq,e,f,g,cu,cv⟩ := tile_repr h
  subst A
  exact ⟨c,u,v,rfl,sub (by simp [tile]),sub (by simp [tile]),sub (by simp [tile]),e,f,g,cu,cv⟩

def nine (i : Bool) : Finset V := if i then {9,12,1} else {9,12,3}
def ten (i : Bool) : Finset V := if i then {10,6,11} else {10,6,13}

private theorem force_nine (c u v : V) (h : embeds alive c u v) (z : 9∈tile c u v) :
    ∃ i : Bool,tile c u v=nine i := by
  have table : ∀ c u v : V,embeds alive c u v→9∈tile c u v→
      ∃ i : Bool,tile c u v=nine i := by
    intro c
    fin_cases c <;> decide
  exact table c u v h z

private theorem force_ten (c u v : V) (h : embeds alive c u v) (z : 10∈tile c u v) :
    ∃ i : Bool,tile c u v=ten i := by
  have table : ∀ c u v : V,embeds alive c u v→10∈tile c u v→
      ∃ i : Bool,tile c u v=ten i := by
    intro c
    fin_cases c <;> decide
  exact table c u v h z

def residual (i j : Bool) : Finset V := (alive \ nine i) \ ten j

def first (i j : Bool) : V := if i || j then 0 else 2
def forced (i : Bool) : Finset V := if i then {0,11,5} else {0,1,7}
def second (i : Bool) : V := if i then 7 else 5

private theorem first_table (i j : Bool) (c u v : V) (h : embeds (residual i j) c u v)
    (z : first i j∈tile c u v) : i≠j ∧ tile c u v=forced i := by
  have checked : ∀ i j : Bool,∀ c u v : V,embeds (residual i j) c u v→
      first i j∈tile c u v→i≠j ∧ tile c u v=forced i := by
    intro i j c
    cases i <;> cases j <;> fin_cases c <;> decide
  exact checked i j c u v h z

private theorem second_table (i j : Bool) (c u v : V) (diff : i≠j)
    (h : embeds (residual i j \ forced i) c u v)
    (z : second i∈tile c u v) : False := by
  have checked : ∀ i j : Bool,∀ c u v : V,i≠j→embeds (residual i j \ forced i) c u v→
      second i∈tile c u v→False := by
    intro i j c
    cases i <;> cases j <;> fin_cases c <;> decide
  exact checked i j c u v diff h z

private theorem restrict_two {P : Finset (Finset V)} (cover : P.biUnion id=alive)
    (disj : ∀ A∈P,∀ B∈P,A≠B→Disjoint A B)
    {A : Finset V} (ha : A∈P) (i j : Bool) (hi : nine i∈P) (hj : ten j∈P)
    (ia : A≠nine i) (ja : A≠ten j) : A⊆residual i j := by
  intro x hx
  have orig : x∈alive := cover ▸ mem_biUnion.mpr ⟨A,ha,hx⟩
  have h1 : x∉nine i := fun ax=>disjoint_left.mp (disj A ha _ hi ia) hx ax
  have h2 : x∉ten j := fun ax=>disjoint_left.mp (disj A ha _ hj ja) hx ax
  exact mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨orig,h1⟩,h2⟩

theorem no_factor_pair_and_edge : ¬FactorOn target alive := by
  rintro ⟨P,tiles,disj,cover⟩
  have all (x : V) (hx : x∈alive) : ∃ A∈P,x∈A := mem_biUnion.mp (cover.symm ▸ hx)
  have sub (A : Finset V) (Ain : A∈P) : A⊆alive :=
    fun z hz=>cover ▸ mem_biUnion.mpr ⟨A,Ain,hz⟩
  obtain ⟨A,ha,az⟩ := all 9 (by decide)
  obtain ⟨x,y,z,hA,hA'⟩ := find_triple (tiles A ha) (sub A ha)
  obtain ⟨i,ri⟩ := force_nine x y z hA' (hA ▸ az)
  have nineIn : nine i∈P := (hA.trans ri) ▸ ha
  obtain ⟨B,hb,bz⟩ := all 10 (by decide)
  obtain ⟨x,y,z,hB,hB'⟩ := find_triple (tiles B hb) (sub B hb)
  obtain ⟨j,rj⟩ := force_ten x y z hB' (hB ▸ bz)
  have tenIn : ten j∈P := (hB.trans rj) ▸ hb
  have aliveFirst : ∀ i j : Bool,first i j∈alive := by decide
  have niFirst : ∀ i j : Bool,first i j∉nine i := by decide
  have tjFirst : ∀ i j : Bool,first i j∉ten j := by decide
  obtain ⟨C,hc,cz⟩ := all (first i j) (aliveFirst i j)
  have res : C⊆residual i j := restrict_two cover disj hc i j nineIn tenIn
    (fun e=>niFirst i j (e ▸ cz)) (fun e=>tjFirst i j (e ▸ cz))
  obtain ⟨x,y,z,hC,hC'⟩ := find_triple (tiles C hc) res
  obtain ⟨diff,jC⟩ := first_table i j x y z hC' (hC ▸ cz)
  have cf := hC.trans jC
  have aliveSecond : ∀ i : Bool,second i∈alive := by decide
  have niSecond : ∀ i : Bool,second i∉nine i := by decide
  have tjSecond : ∀ i j : Bool,second i∉ten j := by decide
  have ciSecond : ∀ i : Bool,second i∉forced i := by decide
  obtain ⟨D,hd,dz⟩ := all (second i) (aliveSecond i)
  have rest : D⊆residual i j := restrict_two cover disj hd i j nineIn tenIn
    (fun e=>niSecond i (e ▸ dz)) (fun e=>tjSecond i j (e ▸ dz))
  have gone : D⊆residual i j \ forced i := by
    intro v hv
    refine mem_sdiff.mpr ⟨rest hv,?_⟩
    intro h
    have separate : D≠C := fun e=>ciSecond i ((e.trans cf) ▸ dz)
    exact disjoint_left.mp (disj D hd C hc separate) hv (cf.symm ▸ h)
  obtain ⟨x,y,z,hD,hD'⟩ := find_triple (tiles D hd) gone
  exact second_table i j x y z diff hD' (hD ▸ dz)

#print axioms domain_shape
#print axioms no_factor_pair_and_edge
end KelmansCactus.AtomicBridge.T2AvoidCounterexample
