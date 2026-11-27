import BicycleChannelPath133
import BicycleComponents133

namespace Graffiti133Bicycle
open SimpleGraph Graffiti133 Finset
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem induced_adj_both_orders {n : Nat} {f : Fin n → V} (hf : InducedPath G f) (i j : Fin n) :
    G.Adj (f i) (f j) ↔ i.val+1=j.val ∨ j.val+1=i.val := by
  rcases lt_trichotomy i j with h|e|h
  · rw [hf.2 i j h]
    have ht : i.val < j.val := h
    omega
  · subst j
    simp
  · rw [G.adj_comm, hf.2 j i h]
    have ht : j.val < i.val := h
    omega

theorem degree_le_two_three_neighbors [DecidableRel G.Adj] {x a b c : V}
    (cap : G.degree x≤2) (ea : G.Adj x a) (eb : G.Adj x b) (ec : G.Adj x c) :
    a=b ∨ a=c ∨ b=c := by
  classical
  by_contra! distinct
  have lower : ({a,b,c} : Finset V) ⊆ G.neighborFinset x := by
    intro w hw
    have ww : w=a ∨ w=b ∨ w=c := by simpa using hw
    rcases ww with rfl|rfl|rfl
    · exact (G.mem_neighborFinset x _).mpr ea
    · exact (G.mem_neighborFinset x _).mpr eb
    · exact (G.mem_neighborFinset x _).mpr ec
  have h := Finset.card_le_card lower
  rw [G.card_neighborFinset_eq_degree] at h
  have three : ({a,b,c} : Finset V).card=3 := by
    rw [Finset.card_insert_of_not_mem (by simp [distinct.1,distinct.2.1]),
        Finset.card_insert_of_not_mem (by simp [distinct.2.2])]
    simp
  omega

structure HubPath (G : SimpleGraph V) (h : V) (S : Finset V) where
  n : Nat
  nontriv : 2≤n
  f : Fin n → (S : Set V)
  path : InducedPath (G.induce (S : Set V)) f
  spans : Function.Surjective f
  attached : ∀ i, G.Adj h (f i).val ↔ i.val=0 ∨ i.val+1=n

theorem single_hub_channel [DecidableRel G.Adj] (S : Finset V) (h : V) (off : h∉S)
    (conn : (G.induce (S : Set V)).Connected) (d2 : ∀ x∈S, G.degree x=2)
    (exit : ∀ x∈S, ∀ y≠h, G.Adj x y → y∈S) {p : V} (hp : p∈S) (hpAdj : G.Adj p h) :
    Nonempty (HubPath G h S) := by
  classical
  obtain ⟨n,pos,f,hf,sur,start⟩ := induced_degree_two_channel conn (⟨p,hp⟩ : (S : Set V)) off hpAdj
    (fun v hv _ _ _ => degree_le_two_three_neighbors (d2 v hv).le)
  have idxCap : 2≤n := by
    have lt : 1<(G.neighborFinset p).card := by rw [G.card_neighborFinset_eq_degree,d2 p hp]; decide
    obtain ⟨q,hq,ne⟩ := Finset.exists_ne_of_one_lt_card lt h
    have qS := exit p hp q ne ((G.mem_neighborFinset p q).mp hq)
    obtain ⟨j,eq⟩ := sur ⟨q,qS⟩
    have ji : j.val≠0 := fun e => by
      have je : j=(⟨0,pos⟩ : Fin n) := Fin.ext e
      rw [je,start] at eq
      have pq := congrArg Subtype.val eq
      exact ((G.mem_neighborFinset p q).mp hq).ne pq
    omega
  let first : Fin n := ⟨0,pos⟩
  let last : Fin n := ⟨n-1,by omega⟩
  have root : G.Adj h (f first).val := by
    change G.Adj h ((f (⟨0,pos⟩ : Fin n)).val)
    rw [start]
    exact hpAdj.symm
  have endAdj : G.Adj h (f last).val := by
    let j : Fin n := ⟨n-2,by omega⟩
    have je : G.Adj (f last).val (f j).val := by
      have q := (induced_adj_both_orders hf last j).mpr (Or.inr (by
        change n-2+1=n-1
        omega))
      exact q
    have lt : 1<(G.neighborFinset (f last).val).card := by
      rw [G.card_neighborFinset_eq_degree,d2 _ (f last).property]
      decide
    obtain ⟨w,hw,ne⟩ := Finset.exists_ne_of_one_lt_card lt (f j).val
    have adjW := (G.mem_neighborFinset _ _).mp hw
    have wh : w=h := by
      by_contra no
      have ws := exit _ (f last).property w no adjW
      obtain ⟨i,eq⟩ := sur ⟨w,ws⟩
      have e : (f i).val=w := congrArg Subtype.val eq
      have ei : (G.induce (S : Set V)).Adj (f last) (f i) := by change G.Adj _ (f i).val; rwa [e]
      have ie := (induced_adj_both_orders hf last i).mp ei
      have ij : i=j := Fin.ext (by
        change i.val=n-2
        have hL : last.val=n-1 := rfl
        have li := i.isLt
        omega)
      exact ne (by rw [←e,ij])
    exact wh ▸ adjW.symm
  refine ⟨⟨n,idxCap,f,hf,sur,fun i => ?_⟩⟩
  constructor
  · intro e
    by_cases z : i.val=0
    · exact Or.inl z
    by_cases en : i.val+1=n
    · exact Or.inr en
    let a : Fin n := ⟨i.val-1,by omega⟩
    let b : Fin n := ⟨i.val+1,by omega⟩
    have ea : G.Adj (f i).val (f a).val :=
      (induced_adj_both_orders hf i a).mpr (Or.inr (by change i.val-1+1=i.val; omega))
    have eb : G.Adj (f i).val (f b).val :=
      (induced_adj_both_orders hf i b).mpr (Or.inl rfl)
    have ab : a≠b := fun w => by
      have h := congrArg Fin.val w
      change i.val-1=i.val+1 at h
      omega
    rcases degree_le_two_three_neighbors (d2 _ (f i).property).le ea eb e.symm with q|q|q
    · exact (ab (hf.1 (Subtype.ext q))).elim
    · exact (off (q ▸ (f a).property)).elim
    · exact (off (q ▸ (f b).property)).elim
  · rintro (z|z)
    · have e : i=first := Fin.ext z
      exact e.symm ▸ root
    · have e : i=last := Fin.ext (by change i.val=n-1; omega)
      exact e.symm ▸ endAdj

#print axioms degree_le_two_three_neighbors
#print axioms single_hub_channel
end Graffiti133Bicycle
namespace Graffiti133Bicycle
open SimpleGraph Finset
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

structure TwoHubPaths (G : SimpleGraph V) (h : V) where
  S : Finset V
  T : Finset V
  offS : h∉S
  offT : h∉T
  sep : Disjoint S T
  noCross : ∀ x∈S, ∀ y∈T, ¬G.Adj x y
  one : HubPath G h S
  two : HubPath G h T

theorem degree_four_single_branch_has_two_paths [DecidableRel G.Adj] (h : V)
    (d4 : G.degree h=4) (d2 : ∀ x≠h,G.degree x=2) :
    Nonempty (TwoHubPaths G h) := by
  classical
  let N := G.neighborFinset h
  have ncard : N.card=4 := (G.card_neighborFinset_eq_degree h).trans d4
  obtain ⟨p,hp⟩ : N.Nonempty := Finset.card_pos.mp (by omega)
  have ph : G.Adj h p := (G.mem_neighborFinset h p).mp hp
  let B : Finset V := {h}
  obtain ⟨S,pS,sb,connS,closeS⟩ := component_after_removing B p (by simpa [B] using ph.ne.symm)
  have hS : h∉S := fun hs => Finset.disjoint_left.mp sb hs (by simp [B])
  have dt (x : V) (hx : x∈S) : G.degree x=2 := d2 x (fun e=>hS (e ▸ hx))
  obtain ⟨P⟩ := single_hub_channel S h hS connS dt
    (fun x xS y yne e =>closeS x xS y (by simpa [B] using yne) e) pS ph.symm
  let z : V := (P.f ⟨0,by have t:=P.nontriv; omega⟩).val
  let w : V := (P.f ⟨P.n-1,by have t:=P.nontriv; omega⟩).val
  have ex : ∃ q∈N,q∉S := by
    by_contra no
    have sub : N⊆({z,w} : Finset V) := by
      intro q hq
      have qS : q∈S := by by_contra hqs; exact no ⟨q,hq,hqs⟩
      obtain ⟨i,ei⟩ := P.spans (⟨q,qS⟩ : (S : Set V))
      have fval : (P.f i).val=q := congrArg Subtype.val ei
      have adj : G.Adj h (P.f i).val := by rw [fval]; exact (G.mem_neighborFinset h q).mp hq
      rcases (P.attached i).mp adj with a|a
      · have eq : i=(⟨0,by have t:=P.nontriv; omega⟩ : Fin P.n) := Fin.ext a
        rw [eq] at fval
        exact Finset.mem_insert.mpr (Or.inl fval.symm)
      · have eq : i=(⟨P.n-1,by have t:=P.nontriv; omega⟩ : Fin P.n) :=
          Fin.ext (by change i.val=P.n-1; omega)
        rw [eq] at fval
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr fval.symm))
    have cap : N.card≤2 := (Finset.card_le_card sub).trans Finset.card_le_two
    omega
  obtain ⟨q,hq,qS⟩ := ex
  have hqAdj := (G.mem_neighborFinset h q).mp hq
  obtain ⟨T,qT,tb,connT,closeT⟩ := component_after_removing B q (by simpa [B] using hqAdj.ne.symm)
  have hT : h∉T := fun ht => Finset.disjoint_left.mp tb ht (by simp [B])
  have sep := disjoint_component_of_outside_anchor B S T closeS tb connT qT qS
  obtain ⟨Q⟩ := single_hub_channel T h hT connT
    (fun x hx => d2 x (fun e=>hT (e ▸ hx)))
    (fun x xT y yne e =>closeT x xT y (by simpa [B] using yne) e) qT hqAdj.symm
  exact ⟨⟨S,T,hS,hT,sep,
    fun x hx y hy e => Finset.disjoint_left.mp sep (closeS x hx y
      (fun b=>Finset.disjoint_left.mp tb hy b) e) hy,P,Q⟩⟩

#print axioms degree_four_single_branch_has_two_paths
end Graffiti133Bicycle
