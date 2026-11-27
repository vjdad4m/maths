import EarRelease
import EarCase
import EarPorts
import TwinObstruction

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.EarReducesTheta
open SquareCap (FactorOn factor_map boundary omitEdge SmallTrivial)
open EarCase (CyclicF2Below ear_factor_of_smaller_f2)
open EarPorts (exterior_contacts_injective)
open EarRelease (Rest Released releasedOfAdjacent releasedIso armEmbedding contacts releasedMap gadget)
open EarTransfer (EarTarget)
open PentagonProfile (Port)
open PentagonCap (attach attach_degree_outside SmallFourTrivial)
noncomputable section
universe u

def Clean4 {W : Type*} (G : SimpleGraph W) : Prop :=
  ∀ a b c d,G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a=c∨b=d

private theorem degree_iso {A B : Type*} [Fintype A] [Fintype B]
    {H : SimpleGraph A} {K : SimpleGraph B} [DecidableRel H.Adj] [DecidableRel K.Adj]
    (e : H ≃g K) (v : A) : H.degree v = K.degree (e v) := by
  rw [←card_neighborSet_eq_degree,←card_neighborSet_eq_degree]
  let u : H.neighborSet v ≃ K.neighborSet (e v) := {
    toFun := fun x => ⟨e x.val,e.map_adj_iff.mpr x.property⟩
    invFun := fun y => ⟨e.symm y.val,by
      have h : H.Adj (e.symm (e v)) (e.symm y.val) := e.symm.map_adj_iff.mpr y.property
      simpa using h⟩
    left_inv := fun _ => Subtype.ext (e.toEquiv.symm_apply_apply _)
    right_inv := fun _ => Subtype.ext (e.toEquiv.apply_symm_apply _) }
  exact Fintype.card_congr u

private theorem boundary_iso {A B : Type*} [Fintype A] [Fintype B]
    {H : SimpleGraph A} {K : SimpleGraph B} (e : H ≃g K) (c : A → Bool) :
    (boundary H c).card = (boundary K (c ∘ e.symm)).card := by
  classical
  have memA (z : A×A) : z∈boundary H c ↔ c z.1=true ∧ c z.2=false ∧ H.Adj z.1 z.2 := by
    simp [boundary]
  have memB (z : B×B) : z∈boundary K (c ∘ e.symm) ↔
      c (e.symm z.1)=true ∧ c (e.symm z.2)=false ∧ K.Adj z.1 z.2 := by simp [boundary]
  apply card_bij (fun z _ => (e z.1,e z.2))
  · intro z h
    obtain ⟨f,t,u⟩ := (memA z).mp h
    exact (memB _).mpr ⟨by simpa using f,by simpa using t,e.map_adj_iff.mpr u⟩
  · intro a _ b _ h
    exact Prod.ext (e.toEquiv.injective (congrArg Prod.fst h)) (e.toEquiv.injective (congrArg Prod.snd h))
  · intro z h
    obtain ⟨f,t,u⟩ := (memB z).mp h
    exact ⟨(e.symm z.1,e.symm z.2),(memA _).mpr ⟨f,t,e.symm.map_adj_iff.mpr u⟩,
      Prod.ext (e.toEquiv.apply_symm_apply _) (e.toEquiv.apply_symm_apply _)⟩

private theorem small_iso {A B : Type*} [Fintype A] [Fintype B]
    {H : SimpleGraph A} {K : SimpleGraph B} (e : H ≃g K) (h : SmallTrivial K) :
    SmallTrivial H := by
  intro c near
  rw [boundary_iso e] at near
  rcases h (c ∘ e.symm) near with ts|fs
  · left
    intro x y hx hy
    apply e.toEquiv.injective
    exact ts (e x) (e y) (by simpa using hx) (by simpa using hy)
  · right
    intro x y hx hy
    apply e.toEquiv.injective
    exact fs (e x) (e y) (by simpa using hx) (by simpa using hy)


private theorem small4_iso {A B : Type*} [Fintype A] [Fintype B]
    {H : SimpleGraph A} {K : SimpleGraph B} (e : H ≃g K) (h : SmallFourTrivial K) :
    SmallFourTrivial H := by
  intro c near
  rw [boundary_iso e] at near
  obtain ⟨b,cut⟩ := h (c ∘ e.symm) near
  refine ⟨b,?_⟩
  intro x y z hx hy hz
  rcases cut (e x) (e y) (e z) (by simpa using hx) (by simpa using hy) (by simpa using hz) with xy|xz|yz
  · exact Or.inl (e.toEquiv.injective xy)
  · exact Or.inr (Or.inl (e.toEquiv.injective xz))
  · exact Or.inr (Or.inr (e.toEquiv.injective yz))

private theorem no4_iso {A B : Type*} {H : SimpleGraph A} {K : SimpleGraph B}
    (e : H ≃g K) (clean : Clean4 K) : Clean4 H := by
  intro a b c d ab bc cd da
  rcases clean _ _ _ _ (e.map_adj_iff.mpr ab) (e.map_adj_iff.mpr bc)
     (e.map_adj_iff.mpr cd) (e.map_adj_iff.mpr da) with ac|bd
  · exact Or.inl (e.toEquiv.injective ac)
  · exact Or.inr (e.toEquiv.injective bd)


private def castThree : Fin 3 ↪ Fin 9 :=
  ⟨fun i=>⟨i.val,by have l:=i.isLt; omega⟩,
    fun i j e=>Fin.ext (congrArg (fun x : Fin 9=>x.val) e)⟩

private def swapAttach {W X : Type*} (A : SimpleGraph W) (B : SimpleGraph X)
    (a : Port ↪ W) (b : Port ↪ X) :
    attach A B a b ≃g attach B A b a := by
  refine {toEquiv := Equiv.sumComm W X, map_rel_iff' := ?_}
  intro x y
  cases x <;> cases y
  · rfl
  · simp [PentagonCap.attach,PentagonCap.attachAdj,and_comm]
  · simp [PentagonCap.attach,PentagonCap.attachAdj,and_comm]
  · rfl

private theorem port_degree_two {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {P : SimpleGraph (Fin 7)}
    {p : Port↪V} {r : Port ↪ Fin 7} [DecidableRel (attach G P p r).Adj]
    (cub : ∀ v,(attach G P p r).degree v=3) (i : Port) : G.degree (p i)=2 := by
  have fi : (univ : Finset Port).filter (fun j=>p j=p i) = {i} := by
    ext j
    simp [p.injective.eq_iff]
  have count := cub (Sum.inl (p i))
  rw [attach_degree_outside,fi,card_singleton] at count
  omega

/-- Absorb an actual adjacent pair in the original seven-vertex
gadget model. This is a genuine reduction to smaller cyclic-four F2,
not merely a statement about a supplied nine-vertex layout.

Only the four edges of the two old path triples are needed; therefore
the result applies to the exact theta, or to any larger internal
edge set on the same seven labeled vertices. -/
theorem original_adjacent_pair_reduces
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {P : SimpleGraph (Fin 7)}
    {p : Port↪V} {r : Port↪Fin 7}
    [DecidableRel (attach G P p r).Adj]
    (smaller : CyclicF2Below.{u} (Fintype.card (V⊕Fin 7)))
    (cub : ∀ x,(attach G P p r).degree x=3)
    (small : SmallTrivial (attach G P p r))
    (small4 : SmallFourTrivial (attach G P p r))
    (clean : Clean4 (attach G P p r))
    (order : Fintype.card (V⊕Fin 7)%6=4)
    (bad : G.Adj (p 1) (p 4))
    (a01 : P.Adj 0 1) (a12 : P.Adj 1 2)
    (a34 : P.Adj 3 4) (a45 : P.Adj 4 5) :
    FactorOn (omitEdge (attach G P p r) (Sum.inr 5) (Sum.inr 0)) (univ.erase (Sum.inr 6)) := by
  classical
  let A := attach G P p r
  let d1 := port_degree_two cub 1
  let d4 := port_degree_two cub 4
  let L := releasedOfAdjacent d1 d4 bad
  let X := Rest p
  let B : SimpleGraph X := G.comap Subtype.val
  let K := A.comap (gadget p)
  let reversed := attach K B (armEmbedding r) (contacts L)
  let isoB : reversed ≃g A := releasedIso r L
  have revCard : Fintype.card (Fin 9⊕X)=Fintype.card (V⊕Fin 7) := Fintype.card_congr isoB.toEquiv
  have n7 : Fintype.card (V⊕Fin 7)=Fintype.card V+7 := by simp
  have n9 : Fintype.card (Fin 9⊕X)=9+Fintype.card X := by simp
  have ports : 5≤Fintype.card V := by
    have c := Fintype.card_le_of_injective p p.injective
    simpa using c
  have largeA : 16≤Fintype.card (V⊕Fin 7) := by omega
  have largeX : 4≤Fintype.card X := by omega
  have rb (u : X) : reversed.degree (Sum.inr u)=3 :=
    (degree_iso isoB (Sum.inr u)).trans (cub _)
  have inj := exterior_contacts_injective (Q:=K) (G:=B) (left:=armEmbedding r)
    (right:=contacts L) castThree largeX rb (small4_iso isoB small4)
  let q : Port↪X := ⟨contacts L,inj⟩
  let rr := (armEmbedding r)
  let A' := attach B K q rr
  let e : A' ≃g A := (swapAttach B K q rr).trans isoB
  have card : Fintype.card (X⊕Fin 9)=Fintype.card (V⊕Fin 7) := Fintype.card_congr e.toEquiv
  have oe : Fintype.card (X⊕Fin 9)%6=4 := by rw [card]; exact order
  have cb (v : X⊕Fin 9) : A'.degree v=3 := (degree_iso e v).trans (cub _)
  have s4 := small4_iso e small4
  have ss := small_iso e small
  have nr := no4_iso e clean
  have tri (a b c : X) (ab : B.Adj a b) (bc : B.Adj b c) (ca : B.Adj c a) : False :=
    TwinObstruction.no_triangle small (by omega) (show A.Adj (Sum.inl a.val) (Sum.inl b.val) from ab)
      (show A.Adj (Sum.inl b.val) (Sum.inl c.val) from bc)
      (show A.Adj (Sum.inl c.val) (Sum.inl a.val) from ca)
      (cub _).le (cub _).le (cub _).le
  let F := omitEdge A (Sum.inr 5) (Sum.inr 0)
  let H := F.comap e.toEquiv.toEmbedding
  have h01 : H.Adj (Sum.inr 0) (Sum.inr 1) := by
    change F.Adj (Sum.inr 0) (Sum.inr 1)
    exact ⟨a01,by simp⟩
  have h12 : H.Adj (Sum.inr 1) (Sum.inr 2) := by
    change F.Adj (Sum.inr 1) (Sum.inr 2)
    exact ⟨a12,by simp⟩
  have h34 : H.Adj (Sum.inr 3) (Sum.inr 4) := by
    change F.Adj (Sum.inr 3) (Sum.inr 4)
    exact ⟨a34,by simp⟩
  have h45 : H.Adj (Sum.inr 4) (Sum.inr 5) := by
    change F.Adj (Sum.inr 4) (Sum.inr 5)
    exact ⟨a45,by simp⟩
  have ae : K.Adj 7 8 := bad
  have h78 : H.Adj (Sum.inr 7) (Sum.inr 8) := by
    change F.Adj (Sum.inl (p 1)) (Sum.inl (p 4))
    exact ⟨bad,by simp⟩
  have w1 : H.Adj (Sum.inl (q 1)) (Sum.inr 7) := by
    change F.Adj (Sum.inl (contacts L 1).val) (Sum.inl (p 1))
    have s : contacts L 1=L.next1 := by simp [contacts]
    exact ⟨((L.end1 _).mpr s).symm,by simp⟩
  have w4 : H.Adj (Sum.inl (q 4)) (Sum.inr 8) := by
    change F.Adj (Sum.inl (contacts L 4).val) (Sum.inl (p 4))
    have s : contacts L 4=L.next4 := by simp [contacts]
    exact ⟨((L.end4 _).mpr s).symm,by simp⟩
  have target : EarTarget B H := by
    refine ⟨h01,h12,h34,h45,h78,?_⟩
    intro x y h
    change F.Adj (Sum.inl x.val) (Sum.inl y.val)
    exact ⟨h,by simp⟩
  have sub : CyclicF2Below.{u} (Fintype.card (X⊕Fin 9)) := card.symm ▸ smaller
  have one : rr 1=7 := rfl
  have four : rr 4=8 := rfl
  have factor := ear_factor_of_smaller_f2 sub (G:=B) (P:=K) (p:=q) (r:=rr)
    cb ss s4 tri nr oe one four ae
    H target w1 w4
  have mapped := factor_map e.toEquiv.toEmbedding (H:=F) (fun _ _ h=>h) factor
  rw [Finset.map_erase,map_univ_equiv] at mapped
  exact mapped

private theorem degree_eq_of_same {W : Type*} [Fintype W] {A B : SimpleGraph W}
    [DecidableRel A.Adj] [DecidableRel B.Adj] (eq : A=B) (x : W) : A.degree x=B.degree x := by
  subst B
  let f (F : Fintype ↑(A.neighborSet x)) := @SimpleGraph.degree W A x F
  exact congrArg f (Subsingleton.elim _ _)

/-- Either of the two original bad contact pairs is removable under
the same smaller-order hypothesis. Changing the port numbering
retains the exact original ambient graph and omitted edge. -/
theorem original_either_adjacent_pair_reduces
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {P : SimpleGraph (Fin 7)}
    {p : Port↪V} {r : Port↪Fin 7}
    [DecidableRel (attach G P p r).Adj]
    (smaller : CyclicF2Below.{u} (Fintype.card (V⊕Fin 7)))
    (cub : ∀ x,(attach G P p r).degree x=3)
    (small : SmallTrivial (attach G P p r))
    (small4 : SmallFourTrivial (attach G P p r))
    (clean : Clean4 (attach G P p r))
    (order : Fintype.card (V⊕Fin 7)%6=4)
    (bad : G.Adj (p 1) (p 4) ∨ G.Adj (p 2) (p 3))
    (a01 : P.Adj 0 1) (a12 : P.Adj 1 2)
    (a34 : P.Adj 3 4) (a45 : P.Adj 4 5) :
    FactorOn (omitEdge (attach G P p r) (Sum.inr 5) (Sum.inr 0)) (univ.erase (Sum.inr 6)) := by
  rcases bad with kept|discarded
  · exact original_adjacent_pair_reduces smaller cub small small4 clean order kept a01 a12 a34 a45
  · let s : Equiv.Perm Port := (Equiv.swap 1 2).trans (Equiv.swap 4 3)
    let q := s.toEmbedding.trans p
    let k := s.toEmbedding.trans r
    have e : attach G P q k=attach G P p r := EarCase.reindex_attachment p r s
    letI : DecidableRel (attach G P q k).Adj := fun a b => by
      rw [e]
      infer_instance
    have c (x) : (attach G P q k).degree x=3 := (degree_eq_of_same e x).trans (cub x)
    have hit : G.Adj (q 1) (q 4) := discarded
    have res := original_adjacent_pair_reduces (p:=q) (r:=k) smaller c
      (e.symm ▸ small) (e.symm ▸ small4) (e.symm ▸ clean) order hit a01 a12 a34 a45
    rwa [e] at res

#print axioms original_either_adjacent_pair_reduces

#print axioms original_adjacent_pair_reduces

end
end KelmansCactus.AtomicBridge.EarReducesTheta
