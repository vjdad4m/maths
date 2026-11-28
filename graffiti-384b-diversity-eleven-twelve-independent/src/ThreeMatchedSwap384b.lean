import ThirteenLower384b
import ShorePairs

namespace Graffiti384b.DiversityEleven
open Finset SimpleGraph ShorePairs
open private Repair.nbr_add Repair.full_nbr Repair.omit_set from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Analytic fallback for three disjoint ordinary ears and an untouched
cubic seeing both other untouched highs. No graph enumeration. -/
theorem exact_of_three_matched_cubic_fallback
    (t : (types G).card=11) {O : Finset V} (three : O.card=3)
    (lo : Disjoint O (high G)) (deg : ∀ e∈O,G.degree e=2)
    (hi : ∀ e∈O,G.neighborFinset e⊆high G)
    (disj : (O : Set V).PairwiseDisjoint (fun e : V=>(G.neighborFinset e : Finset V)))
    (scores : Set.InjOn (trianglesAt G) (high G : Set V))
    (min : ∀ u∈high G,2≤trianglesAt G u)
    {x y z a e0 : V} (xy : x≠y) (xz : x≠z) (yz : y≠z)
    (xh : x∈high G) (yh : y∈high G) (zh : z∈high G)
    (yd : 4≤G.degree y) (zd : 4≤G.degree z)
    (e0O : e0∈O) (ae : a∈G.neighborFinset e0)
    (nx : G.neighborFinset x={y,z,a})
    (free : ∀ e∈O, x∉G.neighborFinset e ∧ y∉G.neighborFinset e ∧ z∉G.neighborFinset e) :
    gamma G≤bound G := by
  classical
  let N : V→Finset V := fun u=>G.neighborFinset u
  have ncard (e : V) (eo : e∈O) : (N e).card=2 := by
    rw [show (N e).card=G.degree e from card_neighborFinset_eq_degree ..,deg e eo]
  have agree {e f u : V} (eo : e∈O) (fo : f∈O) (ue : u∈N e) (uf : u∈N f) : e=f :=
    Classical.byContradiction (fun ne=>Finset.disjoint_left.mp (disj eo fo ne) ue uf)
  have lowu {e u w : V} (eo : e∈O) (ue : u∈N e) (wo : w∈O)
      (uw : G.Adj u w) : w=e := agree wo eo ((G.mem_neighborFinset ..).mpr uw.symm) ue
  have aN (e : V) (eo : e∈O) (e0ne : e≠e0) : a∉N e := fun a1=>
    e0ne (agree eo e0O a1 ae)
  have ax : a≠x := fun h=>(free e0 e0O).1 (h ▸ ae)
  have ay : a≠y := fun h=>(free e0 e0O).2.1 (h ▸ ae)
  have az : a≠z := fun h=>(free e0 e0O).2.2 (h ▸ ae)
  let E := O.erase e0
  have E2 : E.card=2 := by dsimp [E]; rw [card_erase_of_mem e0O,three]
  obtain ⟨e1,e2,e12,Eeq⟩ := card_eq_two.mp E2
  have e1E : e1∈E := Eeq ▸ mem_insert_self ..
  have e2E : e2∈E := Eeq ▸ mem_insert_of_mem (mem_singleton_self _)
  let A := fun (e v : V)=>insert x (insert v (N e))
  have A4 {e v : V} (eo : e∈O) (vv : v=y ∨ v=z) : (A e v).card=4 := by
    have vN : v∉N e := vv.elim (fun h=>h ▸ (free e eo).2.1)
      (fun h=>h ▸ (free e eo).2.2)
    have xv : x≠v := vv.elim (fun h=>h ▸ xy) (fun h=>h ▸ xz)
    have xN : x∉N e := (free e eo).1
    have off : x∉insert v (N e) := by simp [xv,xN]
    dsimp [A]
    rw [card_insert_of_not_mem off,card_insert_of_not_mem vN,ncard e eo]
  let goodv := fun (e v : V)=>2+nbr G v (A e v)≤G.degree v
  have all_if_fail {e v : V} (eo : e∈O) (vv : v=y ∨ v=z)
      (dv : 4≤G.degree v) (ng : ¬goodv e v) :
      G.degree v=4 ∧ N e⊆N v := by
    have vm : v∈A e v := mem_insert_of_mem (mem_insert_self ..)
    have inc : (A e v).filter (G.Adj v) ⊆ (A e v).erase v := by
      intro u um
      exact mem_erase.mpr ⟨(mem_filter.mp um).2.ne.symm,(mem_filter.mp um).1⟩
    have c := card_le_card inc
    rw [card_erase_of_mem vm,A4 eo vv] at c
    have n : ¬2+nbr G v (A e v)≤G.degree v := ng
    have nc : nbr G v (A e v)=3 := by unfold nbr; unfold nbr at n; omega
    have d : G.degree v=4 := by omega
    have eq : (A e v).filter (G.Adj v)=(A e v).erase v := by
      apply eq_of_subset_of_card_le inc
      rw [card_erase_of_mem vm,A4 eo vv,←show nbr G v (A e v)
        =((A e v).filter (G.Adj v)).card from rfl,nc]
    refine ⟨d,?_⟩
    intro u ue
    have vN : v∉N e := vv.elim (fun h=>h ▸ (free e eo).2.1)
      (fun h=>h ▸ (free e eo).2.2)
    have uv : u≠v := fun eq=>vN (eq ▸ ue)
    have um : u∈(A e v).erase v := mem_erase.mpr
      ⟨uv,mem_insert_of_mem (mem_insert_of_mem ue)⟩
    rw [←eq] at um
    exact (G.mem_neighborFinset ..).mpr (mem_filter.mp um).2
  have one_good (v : V) (vv : v=y ∨ v=z) (dv : 4≤G.degree v) :
      ∃ e∈E,goodv e v := by
    by_cases g1 : goodv e1 v
    · exact ⟨e1,e1E,g1⟩
    by_cases g2 : goodv e2 v
    · exact ⟨e2,e2E,g2⟩
    have e1O := mem_of_mem_erase e1E
    have e2O := mem_of_mem_erase e2E
    obtain ⟨dd,h1⟩ := all_if_fail e1O vv dv g1
    obtain ⟨_,h2⟩ := all_if_fail e2O vv dv g2
    have vx : G.Adj v x := by
      apply SimpleGraph.Adj.symm
      apply (G.mem_neighborFinset ..).mp
      rw [nx]
      rcases vv with rfl|rfl <;> simp
    have off : x∉N e1∪N e2 := fun m=>(mem_union.mp m).elim (free _ e1O).1 (free _ e2O).1
    have inc : insert x (N e1∪N e2)⊆N v := insert_subset
      ((G.mem_neighborFinset ..).mpr vx) (union_subset h1 h2)
    have c := card_le_card inc
    rw [card_insert_of_not_mem off,card_union_of_disjoint (disj e1O e2O e12),
      ncard e1 e1O,ncard e2 e2O,show (N v).card=G.degree v from card_neighborFinset_eq_degree ..,dd] at c
    omega
  let markGood := fun (e v : V)=>∀ u∈N e,∃ w∉O∪A e v,G.Adj u w
  have pick : ∃ e∈E,∃ v,(v=y ∨ v=z) ∧ goodv e v ∧ markGood e v := by
    obtain ⟨ey,eyE,gy⟩ := one_good y (Or.inl rfl) yd
    obtain ⟨ez,ezE,gz⟩ := one_good z (Or.inr rfl) zd
    by_cases my : markGood ey y
    · exact ⟨ey,eyE,y,Or.inl rfl,gy,my⟩
    by_cases mz : markGood ez z
    · exact ⟨ez,ezE,z,Or.inr rfl,gz,mz⟩
    have getBad {e v : V} (ng : ¬markGood e v) :
        ∃ u∈N e,∀ w,G.Adj u w→w∈O∪A e v := by
      apply Classical.byContradiction
      intro h
      apply ng
      intro u um
      apply Classical.byContradiction
      intro hh
      exact h ⟨u,um,fun w uw=>Classical.byContradiction (fun wn=>hh ⟨w,wn,uw⟩)⟩
    obtain ⟨u,uy,ub⟩ := getBad my
    obtain ⟨w,wz,wb⟩ := getBad mz
    have remainder {e v u : V} (ee : e∈E) (ue : u∈N e)
        (bad : ∀ w,G.Adj u w→w∈O∪A e v) :
        (N u).erase e⊆insert v ((N e).erase u) := by
      intro w wm
      obtain ⟨we,wn⟩ := mem_erase.mp wm
      have uw := (G.mem_neighborFinset ..).mp wn
      have h := (mem_union.mp (bad w uw)).resolve_left
        (fun wo=>we (lowu (mem_of_mem_erase ee) ue wo uw))
      rcases (show w=x ∨ w=v ∨ w∈N e by simpa [A] using h) with h|h|h
      · have xu : G.Adj x u := (h ▸ uw).symm
        have nxu := (G.mem_neighborFinset ..).mpr xu
        rw [nx,mem_insert,mem_insert,mem_singleton] at nxu
        have f := free e (mem_of_mem_erase ee)
        exact (nxu.elim (fun q=>f.2.1 (q ▸ ue))
          (fun p=>p.elim (fun q=>f.2.2 (q ▸ ue))
            (fun q=>aN e (mem_of_mem_erase ee) (mem_erase.mp ee).1 (q ▸ ue)))).elim
      · exact mem_insert.mpr (Or.inl h)
      · exact mem_insert.mpr (Or.inr (mem_erase.mpr ⟨uw.ne.symm,h⟩))
    have score2 {e v u : V} (ee : e∈E) (ue : u∈N e)
        (bad : ∀ w,G.Adj u w→w∈O∪A e v) : trianglesAt G u=2 := by
      let R := (N u).erase e
      have r := card_le_card (remainder ee ue bad)
      have cap := card_insert_le v ((N e).erase u)
      rw [card_erase_of_mem ue,ncard e (mem_of_mem_erase ee)] at cap
      have rc : R.card≤2 := by dsimp [R]; omega
      have eR : nbr G e R≤1 := by
        have sub : R.filter (G.Adj e) ⊆ (N e).erase u := by
          intro y ym
          obtain ⟨yr,ey⟩ := mem_filter.mp ym
          have uy := (G.mem_neighborFinset ..).mp (mem_of_mem_erase yr)
          exact mem_erase.mpr ⟨uy.ne.symm,(G.mem_neighborFinset ..).mpr ey⟩
        have c := card_le_card sub
        rw [card_erase_of_mem ue,ncard e (mem_of_mem_erase ee)] at c
        exact c
      have p1 : (pairs G R).card≤1 := by
        have sub : (pairs G R).card≤(R.powersetCard 2).card := card_le_card (filter_subset _ _)
        rw [card_powersetCard] at sub
        exact sub.trans ((Nat.choose_le_choose 2 rc).trans (by decide))
      have en : e∈N u := (G.mem_neighborFinset ..).mpr ((G.mem_neighborFinset ..).mp ue).symm
      have eq : insert e R=N u := insert_erase en
      have mn := min u (hi e (mem_of_mem_erase ee) ue)
      change 2≤(pairs G (N u)).card at mn
      change (pairs G (N u)).card=2
      rw [←eq,pairs_insert G (not_mem_erase e (N u))] at mn ⊢
      change 2≤(pairs G R).card+nbr G e R at mn
      change (pairs G R).card+nbr G e R=2
      omega
    have eq : u=w := scores (hi ey (mem_of_mem_erase eyE) uy)
      (hi ez (mem_of_mem_erase ezE) wz) ((score2 eyE uy ub).trans (score2 ezE wz wb).symm)
    have wz' : u∈N ez := eq ▸ wz
    have ee := agree (mem_of_mem_erase eyE) (mem_of_mem_erase ezE) uy wz'
    have wb' : ∀ v,G.Adj u v→v∈O∪A ey z := by simpa only [eq,ee] using wb
    have iy := remainder eyE uy ub
    have iz := remainder eyE uy wb'
    have sub : (N u).erase ey⊆(N ey).erase u := by
      intro r rm
      have yr := mem_insert.mp (iy rm)
      have zr := mem_insert.mp (iz rm)
      exact yr.elim (fun h=>zr.resolve_left (fun j=>yz (h.symm.trans j))) id
    have rc := card_le_card sub
    have uey : ey∈N u := (G.mem_neighborFinset ..).mpr ((G.mem_neighborFinset ..).mp uy).symm
    rw [card_erase_of_mem uey,card_erase_of_mem uy,ncard ey (mem_of_mem_erase eyE),
      show (N u).card=G.degree u from card_neighborFinset_eq_degree ..] at rc
    have du := (mem_filter.mp (hi ey (mem_of_mem_erase eyE) uy)).2
    omega
  obtain ⟨e,ee,v,vv,gv,gm⟩ := pick
  have eo := mem_of_mem_erase ee
  have e0ne := (mem_erase.mp ee).1
  let T := (O.erase e)∪A e v
  have vhi : v∈high G := vv.elim (fun h=>h ▸ yh) (fun h=>h ▸ zh)
  have aHi : A e v ⊆ high G := by
    exact insert_subset xh (insert_subset vhi (hi e eo))
  have dT : Disjoint (O.erase e) (A e v) := lo.mono (erase_subset _ _) aHi
  have tc : T.card=6 := by
    change ((O.erase e)∪A e v).card=6
    rw [card_union_of_disjoint dT,card_erase_of_mem eo,A4 eo vv,three]
  have d : ∀ u∈T,2≤nbr G u Tᶜ := by
    intro u um
    rcases mem_union.mp um with uo|ua
    · have no : N u⊆Tᶜ.filter (G.Adj u) := by
        intro w wm
        refine mem_filter.mpr ⟨mem_compl.mpr ?_,(G.mem_neighborFinset ..).mp wm⟩
        intro wt
        rcases mem_union.mp wt with wo|wa
        · exact Finset.disjoint_left.mp lo (mem_of_mem_erase wo) (hi u (mem_of_mem_erase uo) wm)
        · rcases (show w=x ∨ w=v ∨ w∈N e by simpa [A] using wa) with h|h|h
          · exact (free u (mem_of_mem_erase uo)).1 (h ▸ wm)
          · exact vv.elim (fun y0=>(free u (mem_of_mem_erase uo)).2.1 (y0 ▸ h ▸ wm))
              (fun z0=>(free u (mem_of_mem_erase uo)).2.2 (z0 ▸ h ▸ wm))
          · exact (mem_erase.mp uo).1 (agree (mem_of_mem_erase uo) eo wm h)
      have c := card_le_card no
      rw [ncard u (mem_of_mem_erase uo)] at c
      exact c
    · have two_witness {u p q : V} (pq : p≠q) (pt : p∈Tᶜ) (qt : q∈Tᶜ)
          (up : G.Adj u p) (uq : G.Adj u q) : 2≤nbr G u Tᶜ := by
        have qsub : ({p,q} : Finset V) ⊆ Tᶜ.filter (G.Adj u) := insert_subset
          (mem_filter.mpr ⟨pt,up⟩) (singleton_subset_iff.mpr (mem_filter.mpr ⟨qt,uq⟩))
        simpa [nbr,card_pair pq] using card_le_card qsub
      rcases (show u=x ∨ u=v ∨ u∈N e by simpa [A] using ua) with h|h|h
      · subst u
        have aa : a∈Tᶜ := by
          apply mem_compl.mpr
          intro am
          rcases mem_union.mp am with ao|aa
          · exact Finset.disjoint_left.mp lo (mem_of_mem_erase ao) (hi e0 e0O ae)
          · rcases (show a=x ∨ a=v ∨ a∈N e by simpa [A] using aa) with h|h|h
            · exact ax h
            · exact vv.elim (fun q=>ay (h.trans q)) (fun q=>az (h.trans q))
            · exact aN e eo e0ne h
        have axadj : G.Adj x a := (G.mem_neighborFinset ..).mp (by rw [nx]; simp)
        have spare (s : V) (sh : s∈high G) (sx : s≠x) (sv : s≠v) (sn : s∉N e) : s∈Tᶜ := by
          apply mem_compl.mpr
          intro st
          rcases mem_union.mp st with so|sa
          · exact Finset.disjoint_left.mp lo (mem_of_mem_erase so) sh
          · exact (show s=x ∨ s=v ∨ s∈N e by simpa [A] using sa).elim sx
              (fun h=>h.elim sv sn)
        rcases vv with hv|hv
        · exact two_witness az aa (spare z zh xz.symm (fun q=>yz (hv.symm.trans q.symm))
             (free e eo).2.2) axadj ((G.mem_neighborFinset ..).mp (by rw [nx]; simp))
        · exact two_witness ay aa (spare y yh xy.symm (fun q=>yz (q.trans hv))
             (free e eo).2.1) axadj ((G.mem_neighborFinset ..).mp (by rw [nx]; simp))
      · subst u
        have zero : nbr G v (O.erase e)=0 := by
          rw [nbr,filter_eq_empty_iff.mpr (fun w wm vw => vv.elim
            (fun q=>(free w (mem_of_mem_erase wm)).2.1 ((G.mem_neighborFinset ..).mpr (q ▸ vw.symm)))
            (fun q=>(free w (mem_of_mem_erase wm)).2.2 ((G.mem_neighborFinset ..).mpr (q ▸ vw.symm)))),
            card_empty]
        have full := Repair.full_nbr G v T
        change nbr G v ((O.erase e)∪A e v)+nbr G v Tᶜ=G.degree v at full
        rw [Repair.nbr_add G v dT,zero,zero_add] at full
        change 2+nbr G v (A e v)≤G.degree v at gv
        omega
      · obtain ⟨w,wo,uw⟩ := gm u h
        have et : e∈Tᶜ := mem_compl.mpr (fun et=>(mem_union.mp et).elim
          (fun h=>(mem_erase.mp h).1 rfl) (fun h=>Finset.disjoint_left.mp lo eo (aHi h)))
        have wt : w∈Tᶜ := mem_compl.mpr (fun h=>wo ((mem_union.mp h).elim
          (fun h=>mem_union_left _ (mem_of_mem_erase h)) (fun h=>mem_union_right _ h)))
        have ew : e≠w := fun h=>wo (mem_union_left _ (h ▸ eo))
        exact two_witness ew et wt ((G.mem_neighborFinset ..).mp h).symm uw
  have om := Repair.omit_set G T d
  unfold bound
  rw [t]
  omega

#print axioms exact_of_three_matched_cubic_fallback
end Graffiti384b.DiversityEleven
