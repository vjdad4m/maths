import UpperTenAmbient384b
import UpperTenAllModels384b
import Q10ScoreTransfer384b

namespace Graffiti384b.DiversityEleven.CutTen
open Finset SimpleGraph OddStars.LeafCritical

structure NormalForm (G : SimpleGraph Label) (u v : Label) (B : Finset Label) where
  k : Fin 4
  m : Nat
  p : Label≃Label
  allowed : m∈cuts k
  root0 : p 0=v
  root4 : p 4=u
  shore : ∀ i, p i∈B ↔ m.testBit i.val=true
  fixed : ∀ i j b, staticMotif k i j=some b → (G.Adj (p i) (p j) ↔ b=true)

private theorem diag : ∀ k : Fin 4, ∀ i : Label, staticMotif k i i=some false := by decide

private theorem filter_map (p : Label≃Label) (D : Finset Label) (X Y : Label→Prop)
    [DecidablePred X] [DecidablePred Y] (compat : ∀ w,X w↔Y (p w)) :
    (D.filter X).map p.toEmbedding=(D.map p.toEmbedding).filter Y := by
  ext v
  constructor
  · intro vm
    obtain ⟨i,im,rfl⟩ := mem_map.mp vm
    obtain ⟨id,ix⟩ := mem_filter.mp im
    exact mem_filter.mpr ⟨mem_map.mpr ⟨i,id,rfl⟩,(compat i).mp ix⟩
  · intro vm
    obtain ⟨vd,vy⟩ := mem_filter.mp vm
    obtain ⟨i,id,rfl⟩ := mem_map.mp vd
    exact mem_map.mpr ⟨i,mem_filter.mpr ⟨id,(compat i).mpr vy⟩,rfl⟩

theorem cover_from_normal_form (G : SimpleGraph Label) [DecidableRel G.Adj]
    (u v : Label) (B : Finset Label) (f : TenFrame G u v B) (N : NormalForm G u v B) :
    ∃ D : Finset Label,D.card≤4 ∧ TwoDominates G D := by
  obtain ⟨bits,fit⟩ := bits_of_model G (staticMotif N.k) N.p (diag N.k) N.fixed
  let E := withBits (staticMotif N.k) bits
  have fitE (i j : Label) : E i j=true↔G.Adj (N.p i) (N.p j) := fit i j
  have pu : (univ : Finset Label).map N.p.toEmbedding=univ := by
    ext j
    obtain ⟨i,rfl⟩ := N.p.surjective j
    exact ⟨fun _=>mem_univ _,fun _=>mem_map.mpr ⟨i,mem_univ _,rfl⟩⟩
  have dg (i : Label) : degree E i=G.degree (N.p i) := by
    have eq := filter_map N.p univ (fun w=>E i w=true) (G.Adj (N.p i)) (fitE i)
    rw [pu] at eq
    have t := congrArg Finset.card eq
    rw [card_map] at t
    unfold degree
    rw [t,←card_neighborFinset_eq_degree]
    congr 1
    ext w
    simp
  have scoreEq (i : Label) : score E i=trianglesAt G (N.p i) :=
    Graffiti384b.Q10.score_eq_triangles G N.p E fitE i
  have opp (i w : Label) : across N.m i w=true ↔ ¬(N.p i∈B ↔ N.p w∈B) := by
    rw [N.shore i,N.shore w]
    cases ai : N.m.testBit i.val <;> cases aw : N.m.testBit w.val <;>
      simp [across,ai,aw]
  have crossEq (i : Label) : cross E N.m i=(crossed G B (N.p i)).card := by
    have eq := filter_map N.p univ (fun w=>(E i w && across N.m i w)=true)
      (fun w=>G.Adj (N.p i) w ∧ ¬(N.p i∈B ↔ w∈B)) (fun w=>by
        simp only [Bool.and_eq_true,fitE i w,opp i w])
    rw [pu] at eq
    have h := congrArg Finset.card eq
    rw [card_map] at h
    unfold cross degree
    rw [h]
    congr 1
    ext w
    simp only [crossed,mem_filter,mem_univ,true_and,mem_neighborFinset]
  have same (i w : Label) :
      (!across N.m i w)=true ↔ N.p w∈(if N.p i∈B then B else Bᶜ) := by
    by_cases ib : N.p i∈B
    · have p := (N.shore i).mp ib
      rw [if_pos ib,N.shore w]
      cases e : N.m.testBit w.val <;> simp [across,p,e]
    · have p : N.m.testBit i.val=false := Bool.eq_false_iff.mpr (fun h=>ib ((N.shore i).mpr h))
      rw [if_neg ib,mem_compl,N.shore w]
      cases e : N.m.testBit w.val <;> simp [across,p,e]
  have insideEq (i : Label) : inside E N.m i=nbr G (N.p i) (if N.p i∈B then B else Bᶜ) := by
    have eq := filter_map N.p univ (fun w=>(E i w && !across N.m i w)=true)
      (fun w=>G.Adj (N.p i) w ∧ w∈(if N.p i∈B then B else Bᶜ)) (fun w=>by
        simp only [Bool.and_eq_true,fitE i w,same i w])
    rw [pu] at eq
    have h := congrArg Finset.card eq
    rw [card_map] at h
    unfold inside degree nbr
    rw [h]
    congr 1
    ext w
    simp [and_comm]
  have ad : Admissible E N.m := by
    have h (i : Label) (iOrd : Ordinary i) := f.ordinary (N.p i)
      (fun e=>iOrd.2 (N.p.injective (e.trans N.root4.symm)))
      (fun e=>iOrd.1 (N.p.injective (e.trans N.root0.symm)))
    refine ⟨fun i ni=>by rw [dg]; exact (h i ni).1,
      fun i ni=>by rw [scoreEq]; exact (h i ni).2.1,
      fun i ni=>by rw [crossEq]; exact (h i ni).2.2,?_⟩
    intro i large
    rw [insideEq] at large
    rcases f.localActive (N.p i) large with left|right
    · right
      obtain ⟨e,a⟩ := mem_filter.mp left
      have ed := (G.mem_neighborFinset ..).mp e
      unfold adjacentAcross
      rw [Bool.and_eq_true,fitE i 4,opp i 4,N.root4]
      exact ⟨ed.symm,fun h=>a h.symm⟩
    · left
      obtain ⟨e,a⟩ := mem_filter.mp right
      have ed := (G.mem_neighborFinset ..).mp e
      unfold adjacentAcross
      rw [Bool.and_eq_true,fitE i 0,opp i 0,N.root0]
      exact ⟨ed.symm,fun h=>a h.symm⟩
  obtain ⟨D,small,cover⟩ := all_models N.k N.m N.allowed bits ad
  refine ⟨D.map N.p.toEmbedding,by simpa using small,?_⟩
  intro w outside
  obtain ⟨i,rfl⟩ := N.p.surjective w
  have out : i∉D := fun h=>outside (mem_map.mpr ⟨i,h,rfl⟩)
  have eq := filter_map N.p D (fun j=>E i j=true) (G.Adj (N.p i)) (fitE i)
  have c := congrArg Finset.card eq
  rw [card_map] at c
  change 2≤((D.map N.p.toEmbedding).filter (G.Adj (N.p i))).card
  rw [←c]
  exact cover i out

#print axioms cover_from_normal_form
end Graffiti384b.DiversityEleven.CutTen
