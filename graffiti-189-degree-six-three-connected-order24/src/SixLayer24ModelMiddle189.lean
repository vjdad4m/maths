import SixLayer24ChildOrder189
import Equality24ProfileMiddle189

namespace Graffiti189LongestPath.Equality24Profile
open SimpleGraph SimpleGraph.Walk Finset Layer24Numbering
open private mem_distanceTwo distance_on_geodesic dist_two from SmallSeparator189
set_option linter.unusedSectionVars false
set_option maxHeartbeats 12000000

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem model_of_layer24_cover
    (hc : G.Connected) (capE : ∀ v,(EvenFrom G v).card≤7)
    (high : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (x : V) (n : Fintype.card V=24) (L : Layer24Cover G x) :
    ∃ e : Vert≃V,∃ (m : Kind) (t b : ℕ), (t=3∨t=4) ∧
      4≤b ∧ b+childCount m≤17 ∧ b+childCount m≥15 ∧
      b≤6 ∧ (childCount m=12→b≤5) ∧ Model (G.comap e) m t b := by
  classical
  obtain ⟨Q⟩ := canonical_partition24 L
  obtain ⟨cE,cNames,cWitness⟩ := child_order24 L Q
  obtain ⟨e,e0,dep,sel,aLabel,bLabel,cLabel⟩ :=
    exists_layer_twenty_four_label_from_orders hc x n L Q.sel cE
  let t := L.T.card
  let b := (Shell G x 2).card
  let c := (Shell G x 3).card
  let m := Q.mode
  let H := G.comap e
  have tc : t=3∨t=4 := L.tSize
  have b4 : 4≤b := L.secondMin
  have evenCap := L.evenMax
  have b6 : b≤6 := by change b+(Shell G x 4).card≤6 at evenCap; omega
  have cc : c=childCount m := Q.childSize
  have sum : b+c+(Shell G x 4).card=17 := L.shellTotal
  have c11 : 11≤c := by have q := L.thirdSize; change c=11∨c=12 at q; omega
  have n5 : childCount m=12→b≤5 := by omega
  have claimDepth (i : Vert) : G.dist x (e i)=layer m b i := by
    have h := dep i
    change G.dist x (e i)= (if i.val=0 then 0 else if i.val<7 then 1 else
      if i.val<7+b then 2 else if i.val<7+b+c then 3 else 4) at h
    simpa [layer,cc] using h
  have depthA (i : Vert) : G.dist x (e i)=1 ↔ inA i := by
    rw [claimDepth]
    unfold layer inA
    split <;> rename_i p
    · omega
    split <;> rename_i q
    · omega
    split
    · omega
    split <;> omega
  have depthB (i : Vert) : G.dist x (e i)=2 ↔ inB b i := by
    rw [claimDepth]
    unfold layer inB
    split <;> rename_i p
    · omega
    split <;> rename_i q
    · omega
    split <;> rename_i r
    · omega
    split <;> omega
  have depthC (i : Vert) : G.dist x (e i)=3 ↔ inC m b i := by
    rw [claimDepth]
    unfold layer inC
    split <;> rename_i p
    · omega
    split <;> rename_i q
    · omega
    split <;> rename_i r
    · omega
    split <;> omega
  have getSel {i : Vert} (iS : selected t i) : e i∈L.T := (sel i).mpr iS
  have full {i : Vert} (iS : selected t i) (iF : fullSelector m t (i.val-1)) :
      (Layer25Group G x (e i)).card=7-t := by
    obtain ⟨lo,hi⟩ := iS
    have ae := aLabel i lo hi
    rw [ae]
    exact Q.full ⟨i.val-1,by omega⟩ iF
  have markVal {i : Vert} (iS : selected t i) : (markedOf i).val=i.val+6 := by
    obtain ⟨lo,hi⟩ := iS
    exact Nat.mod_eq_of_lt (by omega)
  have getMark {i : Vert} (iS : selected t i) :
      marked t (markedOf i) ∧ e (markedOf i)=L.rep (e i) := by
    obtain ⟨lo,hi⟩ := iS
    have v := markVal (show selected t i from ⟨lo,hi⟩)
    exact ⟨by unfold marked; omega,bLabel i _ lo hi (by omega)⟩
  have invMark {j : Vert} (jM : marked t j) :
      ∃ i : Vert,selected t i ∧ j=markedOf i := by
    obtain ⟨lo,hi⟩ := jM
    let i : Vert := ⟨j.val-6,by have := j.isLt; omega⟩
    have is' : selected t i := by unfold selected; dsimp [i]; omega
    have v := markVal is'
    refine ⟨i,is',Fin.ext ?_⟩
    rw [v]
    dsimp [i]
    omega
  have groupI {i j : Vert} (iS : selected t i) (jC : inC m b j) :
      e j∈Layer25Group G x (e i) ↔ childHas m t (i.val-1) (j.val-(7+b)) := by
    obtain ⟨lo,hi⟩ := iS
    obtain ⟨jl,jh⟩ := jC
    have jj : j.val<7+b+c := by omega
    rw [aLabel i lo hi,cLabel j jl jj]
    exact cNames ⟨i.val-1,by omega⟩ ⟨j.val-(7+b),by omega⟩
  have witnessI {i j : Vert} (iS : selected t i) (jC : inC m b j) :
      firstChild m t (i.val-1) (j.val-(7+b)) → G.Adj (L.rep (e i)) (e j) := by
    obtain ⟨lo,hi⟩ := iS
    obtain ⟨jl,jh⟩ := jC
    have jj : j.val<7+b+c := by omega
    rw [aLabel i lo hi,cLabel j jl jj]
    exact cWitness ⟨i.val-1,by omega⟩ ⟨j.val-(7+b),by omega⟩
  have step {i j : Vert} : TwoStep H i j ↔ G.dist (e i) (e j)=2 := by
    constructor
    · rintro ⟨ne,no,k,ik,kj⟩
      exact dist_two hc (fun h=>ne (e.injective h)) no ik kj
    · intro d
      have ne : i≠j := by intro h; rw [h,dist_self] at d; omega
      have no : ¬H.Adj i j := by
        intro h
        have a : G.dist (e i) (e j)=1 := dist_eq_one_iff_adj.mpr h
        omega
      obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist (e i) (e j)
      have len := hp.trans d
      let k := e.symm (p.getVert 1)
      have ek : e k=p.getVert 1 := e.apply_symm_apply _
      have ik : G.Adj (e i) (e k) := by
        rw [ek]
        simpa using p.adj_getVert_succ (i:=0) (by omega)
      have kj : G.Adj (e k) (e j) := by
        rw [ek]
        have h := p.adj_getVert_succ (i:=1) (by omega)
        have a : p.getVert 2=e j := by rw [←len,getVert_length]
        simpa only [a] using h
      exact ⟨ne,no,k,ik,kj⟩
  have membersOfNear {i j : Vert} (iS : selected t i)
      (iF : fullSelector m t (i.val-1))
      (D2 : G.dist (e i) (e j)=2) :
      e j∈Layer25Group G x (e i) ∨
      ∃ k : Vert,selected t k ∧ k≠i ∧
        ((G.Adj (e i) (e k) ∧ j=markedOf k) ∨ (¬G.Adj (e i) (e k) ∧ j=k)) := by
    have dm := mem_distanceTwo.mpr D2
    rw [L.d2Exact _ (getSel iS) (full iS iF)] at dm
    rcases mem_union.mp dm with go|go
    · exact .inl go
    · right
      obtain ⟨w,wm,wj⟩ := mem_image.mp go
      obtain ⟨wn,wt⟩ := mem_erase.mp wm
      obtain ⟨k,ke⟩ := e.surjective w
      have kt : selected t k := (sel k).mp (ke.symm ▸ wt)
      have ki : k≠i := fun h=>wn (h ▸ ke.symm)
      subst w
      refine ⟨k,kt,ki,?_⟩
      by_cases yes : G.Adj (e i) (e k)
      · rw [if_pos yes,←(getMark kt).2] at wj
        exact .inl ⟨yes,(e.injective wj).symm⟩
      · rw [if_neg yes] at wj
        exact .inr ⟨yes,(e.injective wj).symm⟩
  refine ⟨e,m,t,b,tc,b4,by omega,by omega,b6,n5,?_⟩
  change Model H m t b
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro i j q eq
    unfold forcedAdj at eq
    split at eq
    · simp at eq
    split at eq
    · rename_i iz
      subst i
      have qv : decide (inA j)=q := Option.some.inj eq
      change G.Adj (e 0) (e j) ↔ q=true
      rw [e0,←dist_eq_one_iff_adj,←qv,decide_eq_true_eq]
      exact depthA j
    split at eq
    · rename_i far
      have qv : false=q := Option.some.inj eq
      rw [←qv]
      constructor
      · intro h
        have o : G.dist (e i) (e j)=1 := dist_eq_one_iff_adj.mpr h
        have l := hc.dist_triangle (u:=x) (v:=e i) (w:=e j)
        rw [claimDepth i,claimDepth j,o] at l
        omega
      · simp
    split at eq
    · rename_i sm
      have qv : true=q := Option.some.inj eq
      rw [←qv]
      constructor
      · intro _
        rfl
      · intro _
        exact L.joinRest _ (getSel sm.1) (full sm.1 sm.2.2.2) _
          (mem_shell.mpr ((depthA j).mpr sm.2.1)) (fun u=>sm.2.2.1 ((sel j).mp u))
    split at eq
    · rename_i sm
      obtain ⟨k,kS,rfl⟩ := invMark sm.2
      have qv : decide (markedOf k=markedOf i)=q := Option.some.inj eq
      rw [←qv,decide_eq_true_eq]
      change G.Adj (e i) (e (markedOf k)) ↔ markedOf k=markedOf i
      rw [(getMark kS).2]
      constructor
      · intro h
        by_cases kn : i=k
        · exact (congrArg markedOf kn).symm
        exact False.elim (L.repPrivate _ (getSel kS) _ (getSel sm.1)
          (fun e'=>kn (e.injective e')) h)
      · intro eq
        have hv := congrArg Fin.val eq
        rw [markVal kS,markVal sm.1] at hv
        have same : k=i := Fin.ext (by omega)
        exact same ▸ L.repAdj _ (getSel kS)
    split at eq
    · rename_i mc
      obtain ⟨i',iS,im⟩ := invMark mc.1
      have ie : e i=L.rep (e i') := im ▸ (getMark iS).2
      have idx : i.val-7=i'.val-1 := by
        have a := congrArg Fin.val im
        rw [markVal iS] at a
        omega
      split at eq
      · rename_i no
        have qv : false=q := Option.some.inj eq
        rw [←qv]
        constructor
        · intro h
          have j3 := (depthC j).mpr mc.2
          have i1 := mem_shell.mp (L.selected (getSel iS))
          have h1 : G.Adj (e i') (e i) := ie.symm ▸ L.repAdj _ (getSel iS)
          have d2 : G.dist (e i') (e j)=2 := by
            apply dist_two hc
            · intro x
              rw [x] at i1
              omega
            · intro edge
              have o := dist_eq_one_iff_adj.mpr edge
              have s := hc.dist_triangle (u:=x) (v:=e i') (w:=e j)
              omega
            · exact h1
            · exact h
          have hh := (groupI iS mc.2).mp
            (mem_inter.mpr ⟨mem_shell.mpr j3,mem_distanceTwo.mpr d2⟩)
          exact False.elim (no (idx.symm ▸ hh))
        · simp
      split at eq
      · rename_i w
        have qv : true=q := Option.some.inj eq
        rw [←qv]
        constructor
        · intro _
          rfl
        · intro _
          change G.Adj (e i) (e j)
          rw [ie]
          exact witnessI iS mc.2 (idx ▸ w)
      simp at eq
    simp at eq
  · intro i j q eq
    unfold forcedD2 at eq
    split at eq
    · rename_i iz
      subst i
      have qv : decide (inB b j)=q := Option.some.inj eq
      rw [←qv,decide_eq_true_eq,step,e0]
      exact depthB j
    split at eq
    · rename_i is
      split at eq
      · rename_i jc
        have qv : decide (childHas m t (i.val-1) (j.val-(7+b)))=q := Option.some.inj eq
        rw [←qv,decide_eq_true_eq,step,←groupI is jc]
        constructor
        · intro h
          exact mem_inter.mpr ⟨mem_shell.mpr ((depthC j).mpr jc),mem_distanceTwo.mpr h⟩
        · intro h
          exact mem_distanceTwo.mp (mem_inter.mp h).2
      rename_i noC
      split at eq
      · rename_i no
        have qv : false=q := Option.some.inj eq
        rw [←qv,step]
        constructor
        · intro h
          rcases membersOfNear is no.1 h with a|⟨k,kt,ki,ad⟩
          · exact False.elim (noC ((depthC j).mp (mem_shell.mp (mem_inter.mp a).1)))
          · rcases ad with ⟨_,rfl⟩|⟨_,rfl⟩
            · have ne : markedOf k≠markedOf i := by
                intro e'
                have v := congrArg Fin.val e'
                rw [markVal kt,markVal is] at v
                exact ki (Fin.ext (by omega))
              exact False.elim (no.2 (.inr ⟨(getMark kt).1,ne⟩))
            · exact False.elim (no.2 (.inl ⟨kt,ki⟩))
        · simp
      simp at eq
    simp at eq
  · intro i j iS jS _ iF d
    rcases membersOfNear iS iF (step.mp d) with a|⟨k,kt,_ki,h⟩
    · have j2 := L.repDepth _ (getSel jS)
      rw [(getMark jS).2] at a
      have dd := mem_shell.mp (mem_inter.mp a).1
      omega
    · rcases h with ⟨ik,eq⟩|⟨_,eq⟩
      · have l := congrArg Fin.val eq
        rw [markVal jS,markVal kt] at l
        have same : k=j := Fin.ext (by omega)
        exact same ▸ ik
      · obtain ⟨kl,kh⟩ := kt
        have l := congrArg Fin.val eq
        rw [markVal jS] at l
        have j1 := jS.1
        omega
  · intro i
    have card : (Shadow H i).card=(DistanceTwo G (e i)).card := by
      apply card_bij (fun j _=>e j)
      · intro j jm
        exact mem_distanceTwo.mpr (step.mp (mem_filter.mp jm).2)
      · intro a _ b _ h
        exact e.injective h
      · intro v vm
        obtain ⟨j,rfl⟩ := e.surjective v
        exact ⟨j,mem_filter.mpr ⟨mem_univ _,step.mpr (mem_distanceTwo.mp vm)⟩,rfl⟩
    rw [card]
    exact distanceTwo_le_of_even 6 _ (capE _)
  · intro i j ne
    have deg (v : Vert) : H.degree v=G.degree (e v) := by
      rw [←H.card_neighborFinset_eq_degree,←G.card_neighborFinset_eq_degree]
      apply card_bij (fun j _=>e j)
      · intro j jm
        exact (G.mem_neighborFinset _ _).mpr ((H.mem_neighborFinset _ _).mp jm)
      · intro a _ b _ h
        exact e.injective h
      · intro w wm
        obtain ⟨j,rfl⟩ := e.surjective w
        exact ⟨j,(H.mem_neighborFinset _ _).mpr ((G.mem_neighborFinset _ _).mp wm),rfl⟩
    change 6≤H.degree i ∨ 6≤H.degree j
    rw [deg,deg]
    exact high _ _ (fun h=>ne (e.injective h))
  · intro i ine
    have hi : x≠e i := fun xeq=>ine (e.injective (xeq.symm.trans e0.symm))
    obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist x (e i)
    have hpos : 0<G.dist x (e i) := Nat.pos_of_ne_zero (fun d=>hi (hc.dist_eq_zero_iff.mp d))
    let j := e.symm (p.getVert (p.length-1))
    have ej : e j=p.getVert (p.length-1) := e.apply_symm_apply _
    have lay := distance_on_geodesic hc p hp (p.length-1) (by omega)
    have ew : G.Adj (e i) (e j) := by
      rw [ej]
      have h := p.adj_getVert_succ (i:=p.length-1) (by omega)
      have e' : p.getVert (p.length-1+1)=e i := by
        rw [show p.length-1+1=p.length by omega,getVert_length]
      rw [e'] at h
      exact h.symm
    have a := claimDepth j
    rw [ej,lay] at a
    have b := claimDepth i
    exact ⟨j,by omega,ew⟩

theorem model_at_order_twenty_four
    (hc : G.Connected) (capE : ∀ v,(EvenFrom G v).card≤7)
    (conn : ∀ S : Finset V,S.card<3→(G.induce ((↑S:Set V)ᶜ)).Connected)
    (high : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (x : V) (dx : G.degree x=6) (n : Fintype.card V=24) :
    ∃ e : Vert≃V,∃ (m : Kind) (t b : ℕ), (t=3∨t=4) ∧
      4≤b ∧ b+childCount m≤17 ∧ b+childCount m≥15 ∧
      b≤6 ∧ (childCount m=12→b≤5) ∧ Model (G.comap e) m t b := by
  obtain ⟨L⟩ := layer_cover_at_order_twenty_four hc capE conn high x dx n
  exact model_of_layer24_cover hc capE high x n L

#print axioms model_at_order_twenty_four
end Graffiti189LongestPath.Equality24Profile
