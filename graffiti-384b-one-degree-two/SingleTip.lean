import FrontierTwentyNine384b

namespace Graffiti384b.QuotaEar
open Finset SimpleGraph LowSample OneEar
open private LowSample.two_degree from LowSample384b
open private Repair.full_nbr from Repair384b
open private OneEar.deg2 from OneEarFinish384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/- The cut and route constructions of OneEarCut384b and OneEarFinish384b
need the two anchors to be distinct, including when there is no edge between them. -/
private theorem separated {e a b : V} (only : twos G={e}) (q : (types G).card≤(nonleaves G).card)
    (ear : G.neighborFinset e={a,b}) (ab : a≠b)
    (apart : ¬(opened G {e,a,b}).Reachable a b) : gamma G≤bound G := by
  classical
  let K : Finset V := {e,a,b}
  let H := opened G K
  have ea : G.Adj e a := (G.mem_neighborFinset _ _).mp (ear ▸ mem_insert_self ..)
  have eb : G.Adj e b := (G.mem_neighborFinset _ _).mp (ear ▸ mem_insert_of_mem (mem_singleton_self _))
  have ek : e∈K := mem_insert_self ..
  have ak : a∈K := mem_insert_of_mem (mem_insert_self ..)
  have bk : b∈K := mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self _))
  have iso {v : V} (edge : H.Adj e v) : False := by
    have vm := (G.mem_neighborFinset _ _).mpr edge.1
    rw [ear] at vm
    exact edge.2 ⟨ek,mem_insert_of_mem vm⟩
  obtain ⟨A,_,_,left,right⟩ := PinnedColor34.cut H ∅ ∅ (by simp)
  let opp (v : V) := if v∈A then Aᶜ else A
  have balance (v : V) : H.degree v ≤ 2*nbr H v (opp v) := by
    have total := Repair.full_nbr H v A
    by_cases va : v∈A
    · have h := left v va (by simp)
      simp only [opp,if_pos va]; omega
    · have h := right v (mem_compl.mpr va) (by simp)
      simp only [opp,if_neg va]; omega
  let ref (v : V) := if H.Reachable a v then a else b
  let S := univ.filter (fun v => v≠e ∧ (v∈A ↔ ref v∈A))
  have sm {v : V} : v∈S ↔ v≠e ∧ (v∈A ↔ ref v∈A) := by simp [S]
  have as' : a∈S := sm.mpr ⟨ea.ne.symm,by simp [ref,Reachable.refl]⟩
  have bs' : b∈S := sm.mpr ⟨eb.ne.symm,by simp [ref,apart,H,K]⟩
  have es : e∉S := fun m => (sm.mp m).1 rfl
  have across {u v : V} (adj : H.Adj u v) (ov : v∈opp u) : (v∈S ↔ u∉S) := by
    have ue : u≠e := fun eq => iso (eq ▸ adj)
    have ve : v≠e := fun eq => iso (eq ▸ adj.symm)
    have reach : H.Reachable a u ↔ H.Reachable a v :=
      ⟨fun r => r.trans adj.reachable,fun r => r.trans adj.symm.reachable⟩
    have fixed : ref u=ref v := by simp only [ref,reach]
    rw [sm,sm]
    simp only [ue,ve,true_and,fixed]
    by_cases ua : u∈A
    · have va : v∉A := mem_compl.mp (show v∈Aᶜ by simpa [opp,ua] using ov)
      simp [ua,va,ue,ve]
    · have va : v∈A := by simpa [opp,ua] using ov
      simp [ua,va,ue,ve]
  let outside (v : V) := if v∈S then Sᶜ else S
  have inc (v : V) : (opp v).filter (H.Adj v)⊆(outside v).filter (G.Adj v) := by
    intro i im
    obtain ⟨ic,vi⟩ := mem_filter.mp im
    apply mem_filter.mpr ⟨?_,vi.1⟩
    have h := across vi ic
    by_cases vs : v∈S <;> simp [outside,vs,h]
  have nonEar {v : V} (vn : v∈nonleaves G) (ve : v≠e) : 3≤G.degree v := by
    by_cases vh : v∈high G
    · exact (mem_filter.mp vh).2
    · have vm : v∈twos G := mem_sdiff.mpr ⟨vn,vh⟩
      exact (ve (mem_singleton.mp (only ▸ vm))).elim
  have atAnchor (v : V) (vn : v∈nonleaves G) (vs : v∈S) (ev : G.Adj e v) (vk : v∈K) :
      2≤nbr G v (outside v) := by
    have vd := nonEar vn ev.ne.symm
    have hd : 0<H.degree v := by
      apply Nat.pos_of_ne_zero
      intro zero
      have nc : (H.neighborFinset v).card=0 := by rw [card_neighborFinset_eq_degree]; omega
      have cover : G.neighborFinset v⊆K.erase v := by
        intro i im
        have vi := (G.mem_neighborFinset _ _).mp im
        apply mem_erase.mpr ⟨vi.ne.symm,?_⟩
        apply Classical.byContradiction
        intro out
        have edge : H.Adj v i := ⟨vi,fun both => out both.2⟩
        have bad := (H.mem_neighborFinset _ _).mpr edge
        rw [card_eq_zero.mp nc] at bad
        exact Finset.not_mem_empty _ bad
      have cap := card_le_card cover
      rw [card_neighborFinset_eq_degree,card_erase_of_mem vk] at cap
      have kc : K.card=3 := by simp [K,ea.ne,eb.ne,ab]
      omega
    have bal := balance v
    obtain ⟨i,im⟩ := card_pos.mp (show 0<((opp v).filter (H.Adj v)).card by change 0<nbr H v (opp v); omega)
    have vi := (mem_filter.mp im).2
    have ie : i≠e := fun eq => iso (eq ▸ vi.symm)
    exact PinnedColor34.two G ie vi.1 ev.symm (mem_filter.mp (inc v im)).1 (by simp [outside,vs,es])
  have good (v : V) (vn : v∈nonleaves G) : 2≤nbr G v (outside v) := by
    by_cases ve : v=e
    · subst v
      simpa [outside,es] using PinnedColor34.two G ab ea eb as' bs'
    by_cases va : v=a
    · subst v; exact atAnchor a vn as' ea ak
    by_cases vb : v=b
    · subst v; exact atAnchor b vn bs' eb bk
    have vk : v∉K := by simp [K,ve,va,vb]
    have eq : H.neighborFinset v = G.neighborFinset v := by
      ext i; simp [H,opened,vk]
    have de : H.degree v=G.degree v := by simpa only [card_neighborFinset_eq_degree] using congrArg Finset.card eq
    have min := nonEar vn ve
    have bal := balance v
    have low : 2 ≤ nbr H v (opp v) := by omega
    exact low.trans (card_le_card (inc v))
  exact PinnedColor34.both G S q (fun v vn vs => by simpa [outside,vs] using good v vn)
    (fun v vn vs => by simpa [outside,mem_compl.mp vs] using good v vn)
private theorem route_of_reach {e a b : V} (ear : G.neighborFinset e={a,b}) (eb : G.Adj e b) (ab : a≠b)
    (reach : (opened G {e,a,b}).Reachable a b) : ∃ n, 2≤n ∧ Nonempty (Route G e a b n) := by
  classical
  let K : Finset V := {e,a,b}
  let H := opened G K
  obtain ⟨p,hp⟩ := reach.exists_isPath
  let f := p.getVert
  have one : 1≤p.length := by
    by_contra! short
    have zero : p.length=0 := by omega
    exact ab (p.getVert_zero.symm.trans (zero ▸ p.getVert_length))
  have two : 2≤p.length := by
    by_contra! short
    have l : p.length=1 := by omega
    have edge := p.adj_getVert_succ (i:=0) (by omega)
    rw [p.getVert_zero,show 0+1=p.length by omega,p.getVert_length] at edge
    exact edge.2 ⟨by simp [K],by simp [K]⟩
  have st (i : ℕ) (hi : i < p.length) : H.Adj (f i) (f (i+1)) := p.adj_getVert_succ hi
  have iso {v : V} (edge : H.Adj e v) : False := by
    have vm := (G.mem_neighborFinset _ _).mpr edge.1
    rw [ear] at vm
    exact edge.2 ⟨by simp [K],mem_insert_of_mem vm⟩
  let r : Route G e a b p.length := {
    atIdx := f
    start := p.getVert_zero
    finish := p.getVert_length
    step := fun i hi => (st i hi).1
    unique := fun i hi j hj eq => hp.getVert_injOn hi hj eq
    avoid := by
      intro i hi eq
      by_cases lt : i < p.length
      · exact iso (eq ▸ st i lt)
      · have endv : f i=b := (show i=p.length by omega) ▸ p.getVert_length
        exact eb.ne (eq.symm.trans endv)
  }
  exact ⟨p.length,two,⟨r⟩⟩



/-- Away from the unique ear, all edges without a triangle may be incident
to a single exceptional vertex f. The first and last edges of an odd route
of length at least three cannot both meet f. -/
theorem one_exception {e f : V} (only : twos G={e})
    (q : (types G).card≤(nonleaves G).card)
    (support : ∀ u v,u≠e → v≠e → u≠f → v≠f → G.Adj u v → ∃ z,G.Adj u z ∧ G.Adj v z) :
    gamma G≤bound G := by
  classical
  have et : e∈twos G := only ▸ mem_singleton_self _
  obtain ⟨a,b,ab,ear⟩ := card_eq_two.mp ((card_neighborFinset_eq_degree G e).trans (LowSample.two_degree G et))
  have ea : G.Adj e a := (G.mem_neighborFinset ..).mp (ear ▸ mem_insert_self ..)
  have eb : G.Adj e b := (G.mem_neighborFinset ..).mp (ear ▸ mem_insert_of_mem (mem_singleton_self _))
  by_cases reach : (opened G {e,a,b}).Reachable a b
  · obtain ⟨n,two,⟨p⟩⟩ := route_of_reach G ear eb ab reach
    by_cases ev : n%2=0
    · exact p.close only q ea eb ab ev
    have three : 3≤n := by omega
    have finishAt {a b : V} (r : Route G e a b n) (ea : G.Adj e a) (eb : G.Adj e b)
        (ab : a≠b) (ear : G.neighborFinset e={a,b}) (af : a≠f) (away : r.atIdx 1≠f) : gamma G≤bound G := by
      have near := r.step 0 (by omega)
      rw [r.start] at near
      obtain ⟨z,az,iz⟩ := support a _ ea.ne.symm (r.avoid 1 (by omega)) af away near
      have ze : z≠e := by
        intro eq
        have m := (G.mem_neighborFinset _ _).mpr (show G.Adj e (r.atIdx 1) from eq ▸ iz.symm)
        rw [ear,mem_insert,mem_singleton] at m
        rcases m with ua|ub
        · exact near.ne ua.symm
        · have idx := r.unique 1 (by omega) n le_rfl (ub.trans r.finish.symm)
          omega
      exact change_parity r two only q ea eb ab ze az iz
    by_cases front : a≠f ∧ p.atIdx 1≠f
    · exact finishAt p ea eb ab ear front.1 front.2
    · have clean (j : ℕ) (js : 2≤j) (jn : j≤n) : p.atIdx j≠f := by
        intro wrong
        apply front
        constructor
        · intro af
          have := p.unique 0 (by omega) j jn ((p.start.trans af).trans wrong.symm)
          omega
        · intro af
          have := p.unique 1 (by omega) j jn (af.trans wrong.symm)
          omega
      exact finishAt p.reverse eb ea ab.symm (ear.trans (pair_comm ..))
        (p.finish ▸ clean n (by omega) le_rfl) (clean (n-1) (by omega) (by omega))
  · exact separated G only q ear ab reach

end Graffiti384b.QuotaEar
#print axioms Graffiti384b.QuotaEar.one_exception
