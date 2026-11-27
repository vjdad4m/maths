import ThetaSevenFaithfulValid
import TwinObstruction

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaSevenFaithfulAutomatic
open SquareCap (boundary SmallTrivial FactorOn)
open PentagonCap (SmallFourTrivial)
open PentagonProfile (Port)
open ThetaSevenFaithfulCap (ambient candidate target core9 link? wire9)
open ThetaSevenFaithfulRefill (In)
open ThetaSevenFaithfulValid (IndependentGroups cap_valid_of_independent_groups)

noncomputable section
universe u

private theorem no_four_cut {W : Type*} [Fintype W] [DecidableEq W]
    {G : SimpleGraph W} (S : Finset W) (inside : 3≤S.card)
    (outside : 3≤Fintype.card W-S.card) (small : SmallFourTrivial G)
    (cut : (boundary G (fun x=>decide (x∈S))).card≤4) : False := by
  let c : W→Bool := fun x=>decide (x∈S)
  obtain ⟨b,h⟩ := small c cut
  have witness (T : Finset W) (ht : 3≤T.card) :
      ∃ a∈T,∃ b∈T,∃ d∈T,a≠b∧a≠d∧b≠d := by
    obtain ⟨a,ha,b,hb,ab⟩ := one_lt_card.mp (by omega : 1<T.card)
    have two : ({a,b}:Finset W).card=2 := by simp [card_insert_of_not_mem,ab]
    obtain ⟨d,hd,nd⟩ := exists_mem_not_mem_of_card_lt_card (by omega : ({a,b}:Finset W).card<T.card)
    have both : d≠a∧d≠b := by simpa using nd
    exact ⟨a,ha,b,hb,d,hd,ab,both.1.symm,both.2.symm⟩
  rw [←card_compl] at outside
  cases b
  · obtain ⟨a,ha,b,hb,d,hd,ab,ad,bd⟩ := witness Sᶜ outside
    have ea : c a=false := by simpa [c] using ha
    have eb : c b=false := by simpa [c] using hb
    have ed : c d=false := by simpa [c] using hd
    exact (h a b d ea eb ed).elim ab (fun e=>e.elim ad bd)
  · obtain ⟨a,ha,b,hb,d,hd,ab,ad,bd⟩ := witness S inside
    have ea : c a=true := by simpa [c] using ha
    have eb : c b=true := by simpa [c] using hb
    have ed : c d=true := by simpa [c] using hd
    exact (h a b d ea eb ed).elim ab (fun e=>e.elim ad bd)

private theorem all_neighbors {W : Type*} [Fintype W] [DecidableEq W]
    {G : SimpleGraph W} [DecidableRel G.Adj] {u a b c : W} (cub : G.degree u=3)
    (ab : a≠b) (ac : a≠c) (bc : b≠c)
    (ua : G.Adj u a) (ub : G.Adj u b) (uc : G.Adj u c) :
    ∀ x,G.Adj u x→ x=a∨x=b∨x=c := by
  have exact3 : ({a,b,c}:Finset W)=G.neighborFinset u := by
    apply eq_of_subset_of_card_le
    · intro y hy
      simp only [mem_insert,mem_singleton] at hy
      rcases hy with rfl|rfl|rfl
      all_goals apply (mem_neighborFinset _ _ _).mpr; assumption
    · simp [card_insert_of_not_mem,ab,ac,bc,card_neighborFinset_eq_degree,cub]
  intro x ux
  have hx := (mem_neighborFinset _ _ _).mpr ux
  rw [←exact3] at hx
  simpa using hx

def heavy (b : Bool) : Port := if b then 0 else 2

private theorem heavy_different : ∀ b : Bool,heavy b≠heavy (!b) := by decide
private theorem heavy_values : ∀ b : Bool,heavy b=0∨heavy b=2 := by decide
private theorem heavy_pairs : ∀ b : Bool,∃ a c : Fin 9,
    a≠c∧wire9 (heavy b) a=true∧wire9 (heavy b) c=true := by decide
private theorem singleton_wire : ∀ q : Port,q≠0→q≠2→∃ r : Fin 9,wire9 q r=true := by decide

private def expose (q : Port) : Finset (Fin 9) :=
  univ.filter (fun i=>∃ a : Port,a≠0∧a≠2∧a≠q∧wire9 a i=true)

private theorem expose_bound : ∀ q : Port,q≠0→q≠2→(expose q).card≤2 := by decide
private theorem expose_degree : ∀ q : Port,q≠0→q≠2→∀ i∈expose q,∃ a c : Fin 9,
    a≠c∧core9.Adj i a∧core9.Adj i c := by decide

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {B : SimpleGraph V} [DecidableRel B.Adj] {p : Port↪V}

private theorem no_heavy_heavy_edge (cub : ∀ x,(ambient B p).degree x=3)
    (cyc5 : SmallFourTrivial (ambient B p)) : ¬B.Adj (p 0) (p 2) := by
  classical
  intro edge
  let G := ambient B p
  let a : V⊕Fin 9 := Sum.inl (p 0)
  let b : V⊕Fin 9 := Sum.inl (p 2)
  let c : V⊕Fin 9 := In 8
  let S : Finset (V⊕Fin 9) := {a,b,c}
  have ab : G.Adj a b := edge
  have bc : G.Adj b c := ⟨2,rfl,by decide⟩
  have ca : G.Adj c a := ⟨0,rfl,by decide⟩
  have n : S.card=3 := by simp [S,card_insert_of_not_mem,ab.ne,bc.ne,ca.ne.symm]
  have inner : ∀ x∈S,∃ u∈S,∃ v∈S,u≠v∧G.Adj x u∧G.Adj x v := by
    intro x hx
    simp only [S,mem_insert,mem_singleton] at hx
    rcases hx with rfl|rfl|rfl
    · exact ⟨b,by simp [S],c,by simp [S],bc.ne,ab,ca.symm⟩
    · exact ⟨c,by simp [S],a,by simp [S],ca.ne,bc,ab.symm⟩
    · exact ⟨a,by simp [S],b,by simp [S],ab.ne,ca,bc.symm⟩
  have cut := TwinObstruction.cut_le_exposed_vertices (G:=G) S S
    (fun _ h _ _ _=>h) (fun x _=>(cub x).le) inner
  have room : Fintype.card (V⊕Fin 9)=Fintype.card V+9 := by simp
  exact no_four_cut S (by omega) (by omega) cyc5 (cut.trans (by omega))

/-- Every double-wire contact has no exterior adjacency to any of the
three singleton-wire contacts. The forbidden shore retains all nine
interior sites and exactly those two double ports and the proposed
singleton. This is stronger than merely detecting triangles in a cap. -/
theorem no_heavy_single_edge (cub : ∀ x,(ambient B p).degree x=3)
    (cyc5 : SmallFourTrivial (ambient B p)) (size : 6≤Fintype.card V)
    (b : Bool) (q : Port) (q0 : q≠0) (q2 : q≠2) :
    ¬B.Adj (p (heavy b)) (p q) := by
  classical
  intro edge
  let G := ambient B p
  let h := heavy b
  let k := heavy (!b)
  let S : Finset (V⊕Fin 9) := ({p h,p k,p q}:Finset V).disjSum univ
  let T : Finset (V⊕Fin 9) := ({p k,p q}:Finset V).disjSum (expose q)
  have hk : h≠k := heavy_different b
  have qh : q≠h := (heavy_values b).elim (fun x=>fun y=>q0 (y.trans x))
    (fun x=>fun y=>q2 (y.trans x))
  have qk : q≠k := (heavy_values (!b)).elim (fun x=>fun y=>q0 (y.trans x))
    (fun x=>fun y=>q2 (y.trans x))
  have pNe {a c : Port} (e : a≠c) : p a≠p c := fun x=>e (p.injective x)
  have sCount : S.card=12 := by
    simp [S,card_disjSum,card_insert_of_not_mem,pNe hk,pNe qh.symm,pNe qk.symm]
  have tCount : T.card≤4 := by
    have ct := expose_bound q q0 q2
    simp [T,card_disjSum,card_insert_of_not_mem,pNe qk.symm]
    omega
  have sLeft (v : V) : (Sum.inl v : V⊕Fin 9) ∈ S ↔ v=p h∨v=p k∨v=p q := by simp [S]
  have sRight (i : Fin 9) : (Sum.inr i : V⊕Fin 9) ∈ S := by simp [S]
  have tLeft (v : V) : (Sum.inl v : V⊕Fin 9) ∈ T ↔ v=p k∨v=p q := by simp [T]
  have tRight (i : Fin 9) : (Sum.inr i : V⊕Fin 9) ∈ T ↔ i∈expose q := by simp [T]
  have hasHeavy (i : Port) (ih : i=0∨i=2) : i=h∨i=k := by
    have eqs : ∀ b : Bool,∀ i : Port,i=0∨i=2→i=heavy b∨i=heavy (!b) := by decide
    exact eqs b i ih
  obtain ⟨a,c,ac,ah,ch⟩ := heavy_pairs b
  have ha : G.Adj (Sum.inl (p h)) (Sum.inr a) := ⟨h,rfl,ah⟩
  have hc : G.Adj (Sum.inl (p h)) (Sum.inr c) := ⟨h,rfl,ch⟩
  have hq : G.Adj (Sum.inl (p h)) (Sum.inl (p q)) := edge
  have hAll := all_neighbors (G:=G) (cub (Sum.inl (p h)))
    (fun e=>ac (Sum.inr_injective e)) Sum.noConfusion Sum.noConfusion ha hc hq
  have source : ∀ u∈S,∀ v∉S,G.Adj u v→u∈T := by
    intro u us v vs uv
    cases v with
    | inr j => exact (vs (sRight j)).elim
    | inl w =>
      cases u with
      | inl u =>
        rcases (sLeft u).mp us with rfl|rfl|rfl
        · rcases hAll (Sum.inl w) uv with d|d|d
          · cases d
          · cases d
          · exact (vs ((sLeft w).mpr (Or.inr (Or.inr (Sum.inl_injective d))))).elim
        · exact (tLeft _).mpr (Or.inl rfl)
        · exact (tLeft _).mpr (Or.inr rfl)
      | inr i =>
        obtain ⟨j,rfl,wr⟩ : link? p wire9 w i := uv
        have notSel : ¬(j=h∨j=k∨j=q) := by
          intro x
          apply vs
          apply (sLeft _).mpr
          exact x.imp (congrArg p) (fun y=>y.imp (congrArg p) (congrArg p))
        have j0 : j≠0 := fun d => notSel ((hasHeavy j (Or.inl d)).imp id Or.inl)
        have j2 : j≠2 := fun d => notSel ((hasHeavy j (Or.inr d)).imp id Or.inl)
        have jq : j≠q := fun d=>notSel (Or.inr (Or.inr d))
        apply (tRight i).mpr
        exact mem_filter.mpr ⟨mem_univ _,j,j0,j2,jq,wr⟩
  have inside : ∀ u∈T,∃ a∈S,∃ c∈S,a≠c∧G.Adj u a∧G.Adj u c := by
    intro u ut
    cases u with
    | inl u =>
      rcases (tLeft u).mp ut with rfl|rfl
      · obtain ⟨i,j,ij,hi,hj⟩ := heavy_pairs (!b)
        exact ⟨.inr i,sRight _, .inr j,sRight _,fun e=>ij (Sum.inr_injective e),
          ⟨k,rfl,hi⟩,⟨k,rfl,hj⟩⟩
      · obtain ⟨i,hi⟩ := singleton_wire q q0 q2
        exact ⟨.inr i,sRight _, .inl (p h),(sLeft _).mpr (Or.inl rfl),Sum.noConfusion,
          ⟨q,rfl,hi⟩,hq.symm⟩
    | inr i =>
      obtain ⟨j,k,jk,hj,hk⟩ := expose_degree q q0 q2 i ((tRight i).mp ut)
      exact ⟨.inr j,sRight _, .inr k,sRight _,fun e=>jk (Sum.inr_injective e),hj,hk⟩
  have cut := TwinObstruction.cut_le_exposed_vertices (G:=G) S T source
    (fun u _=>(cub u).le) inside
  have room : Fintype.card (V⊕Fin 9)=Fintype.card V+9 := by simp
  exact no_four_cut S (by omega) (by omega) cyc5 (cut.trans tCount)

/-- No extra exterior-independence hypotheses are needed in the
faithful layout once its ambient graph is cubic, cyclic-five, and
has at least six exterior vertices. -/
theorem cap_valid_automatic (cub : ∀ x,(ambient B p).degree x=3)
    (cyc5 : SmallFourTrivial (ambient B p)) (size : 6≤Fintype.card V) :
    SmallTrivial (candidate B p) := by
  apply cap_valid_of_independent_groups cub cyc5
  have ban (b : Bool) (q : Port) (q0 : q≠0) (q2 : q≠2) :=
    no_heavy_single_edge cub cyc5 size b q q0 q2
  exact ⟨ban false 4 (by decide) (by decide),
    ban true 3 (by decide) (by decide), ban true 1 (by decide) (by decide),
    no_heavy_heavy_edge cub cyc5,
    fun e=>ban false 1 (by decide) (by decide) e.symm⟩

/-- The exact seven-wire faithful F2 branch reduces to six vertices
smaller purely under cyclic-five and the correct order residue. -/
theorem reduce_automatic
    (smaller : EarCase.CyclicF2Below.{u} (Fintype.card (V⊕Fin 9)))
    (cub : ∀ x,(ambient B p).degree x=3)
    (cyc5 : SmallFourTrivial (ambient B p))
    (order : Fintype.card (V⊕Fin 9)%6=4) :
    FactorOn (target B p) (univ.erase (In 6)) := by
  have five : 5≤Fintype.card V := by simpa using Fintype.card_le_of_injective p p.injective
  have n : Fintype.card (V⊕Fin 9)=Fintype.card V+9 := by simp
  exact ThetaSevenFaithfulCap.reduce smaller cub (cap_valid_automatic cub cyc5 (by omega)) order

#print axioms no_heavy_single_edge
#print axioms cap_valid_automatic
#print axioms reduce_automatic
end
end KelmansCactus.AtomicBridge.ThetaSevenFaithfulAutomatic
