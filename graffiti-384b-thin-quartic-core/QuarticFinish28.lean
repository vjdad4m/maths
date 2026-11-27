import QuarticCredits28
import QuarticContact28

namespace Graffiti384b.Four28
open Finset SimpleGraph HighEar Core28
open private Repair.full_nbr from Repair384b
open private Four28.mono_cap from FourSquareSaving28
open private FiniteRange.bad from FiniteRange384b
open private Four28.core_data Four28.ear_one from FourFrontier28
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- Omit the ear and its quartic fourth vertex and retain both endpoints.
The second common neighbor and an asymmetric contact pay for the uncredited neighbor. -/
theorem quartic_layout_saving {e s p q x y : V} (n : Fintype.card V=28) (pqE : H.Adj p q)
    (en : H.neighborFinset e={p,q}) (es : e≠s) (sp : H.Adj s p) (sq : H.Adj s q)
    (se : trianglesAt H e=1) (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H))
    (free : H.CliqueFree 5) (ss : trianglesAt H s=4)
    (lx : leaks H s p q={x}) (ns : H.neighborFinset s={p,q,x,y})
    (yc : y∈additional H e p q) (ys : y≠s) : gamma H≤13 := by
  classical
  have pq := pqE.ne
  have ep : H.Adj e p := (H.mem_neighborFinset ..).mp (en ▸ mem_insert_self ..)
  have eq' : H.Adj e q := (H.mem_neighborFinset ..).mp (en ▸ mem_insert_of_mem (mem_singleton_self _))
  let S := ({e,s}:Finset V)ᶜ
  let J := H.induce (S:Set V)
  let i : S := ⟨p,by simp [S,ep.ne.symm,sp.ne.symm]⟩
  let j : S := ⟨q,by simp [S,eq'.ne.symm,sq.ne.symm]⟩
  have ij : i≠j := fun h => pq (congrArg Subtype.val h)
  let W := ({i,j}:Finset S)ᶜ
  have cardS : Fintype.card S=26 := by rw [Fintype.card_coe]; simp [S,card_compl,n,es]
  have ws : W.card=24 := by simp [W,card_compl,cardS,ij]
  let f (w : S) := trianglesAt H w.val
  have fi : Function.Injective f := fun _ _ h => Subtype.ext (inj h)
  have range' (w : S) (_ : w∈W) : 2≤f w ∧ f w≠trianglesAt H s := by
    have off : w.val≠e ∧ w.val≠s := by simpa [S,not_or] using w.property
    have ne : f w≠1 := fun h => off.1 (inj (h.trans se.symm))
    have lo : 0<f w := pos _
    exact ⟨by omega,fun eq => off.2 (inj eq)⟩
  let L := W.filter (fun w => w.val∈leaks H s p q)
  have lsize : L.card≤(leaks H s p q).card := by
    have sub : L.map (Function.Embedding.subtype _)⊆leaks H s p q := by
      intro x xm; obtain ⟨w,wm,rfl⟩ := mem_map.mp xm; exact (mem_filter.mp wm).2
    exact (card_map ..).symm.le.trans (card_le_card sub)
  have ext (w : S) (wm : w∈W) : w.val≠p ∧ w.val≠q := by
    have h : w≠i ∧ w≠j := by simpa [W,not_or] using wm
    exact ⟨fun eq => h.1 (Subtype.ext eq),fun eq => h.2 (Subtype.ext eq)⟩
  have away (w : S) (wm : w∈W) : ¬H.Adj w.val e := by
    intro ed; have inside := (H.mem_neighborFinset ..).mpr ed.symm
    rw [en] at inside
    exact (mem_insert.mp inside).elim (ext w wm).1 (fun z => (ext w wm).2 (mem_singleton.mp z))
  have loss (w : S) (wm : w∈W) :
      H.degree w.val=J.degree w+(if H.Adj w.val s then 1 else 0) := by
    have ct : nbr H w.val {e,s}+J.degree w=H.degree w.val := by
      rw [EarAnchor.induced_degree]; exact Repair.full_nbr H w.val {e,s}
    unfold nbr at ct
    by_cases b : H.Adj w.val s
    · have one : ({s}:Finset V).filter (H.Adj w.val)={s} := filter_true_of_mem (by simpa using b)
      simpa [Finset.filter_insert,away w wm,b,one,Nat.add_comm] using ct.symm
    · have zero : ({s}:Finset V).filter (H.Adj w.val)=∅ := filter_eq_empty_iff.mpr (by simpa using b)
      simpa [Finset.filter_insert,away w wm,b,zero] using ct.symm
  have full (w : S) (wm : w∈W) :
      f w≤(turanGraph (J.degree w+1) 3).edgeFinset.card ∨ 10≤J.degree w := by
    by_cases big : 10≤J.degree w
    · exact Or.inr big
    apply Or.inl
    have de := loss w wm
    have le : H.degree w.val≤J.degree w+1 := by split_ifs at de <;> omega
    have a := RankTuran.local_turan H 3 (by decide) free w.val
    have old := RankTable.cap_table ⟨H.degree w.val,by omega⟩ ⟨3,by decide⟩ (by decide)
    have new := RankTable.cap_table ⟨J.degree w+1,by omega⟩ ⟨3,by decide⟩ (by decide)
    exact (a.trans_eq old).trans ((Four28.mono_cap ⟨H.degree w.val,by omega⟩ ⟨J.degree w+1,by omega⟩ le).trans_eq new.symm)
  have plain (w : S) (wm : w∈W) (nl : w∉L) (unc : ∀ z,z∉W → ¬J.Adj w z) :
      f w≤(turanGraph (J.degree w) 3).edgeFinset.card ∨ 10≤J.degree w := by
    have np : ¬H.Adj w.val p := unc i (by simp [W])
    have nq : ¬H.Adj w.val q := unc j (by simp [W])
    have no : ¬H.Adj w.val s := fun ed => nl (mem_filter.mpr ⟨wm,mem_filter.mpr
      ⟨(H.mem_neighborFinset ..).mpr ed.symm,(ext w wm).1,(ext w wm).2,np,nq⟩⟩)
    have h := RankTuran.local_turan H 3 (by decide) free w.val
    rw [loss w wm,if_neg no,Nat.add_zero] at h
    exact Or.inl h
  have ca := (HighEar.additional_mem H).mp yc
  obtain ⟨t,te,tp,tq,dist⟩ := distinguishing_contact H en pqE (fun h => pq (inj h))
  have ts : t≠s := by
    intro z; subst t; exact dist ⟨fun _ => sq.symm,fun _ => sp.symm⟩
  have ty : t≠y := by
    intro z; subst t; exact dist ⟨fun _ => ca.2.2,fun _ => ca.2.1⟩
  have touches : H.Adj p t ∨ H.Adj q t := by
    by_contra! no; exact dist ⟨fun h => (no.1 h).elim,fun h => (no.2 h).elim⟩
  have xmem : x∈leaks H s p q := lx ▸ mem_singleton_self _
  obtain ⟨_,_,_,xp,xq⟩ := mem_filter.mp xmem
  have tx : t≠x := by
    rintro rfl; exact touches.elim (fun h => xp h.symm) (fun h => xq h.symm)
  have notS : ¬H.Adj t s := by
    intro h
    have mem := (H.mem_neighborFinset ..).mpr h.symm
    simp [ns,tp,tq,tx,ty] at mem
  let Y : S := ⟨y,by simp [S,ca.1,ys]⟩
  let U : S := ⟨t,by simp [S,te,ts]⟩
  have yw : Y∈W := by
    have d : Y≠i := fun h => ca.2.1.ne.symm (congrArg Subtype.val h)
    have f : Y≠j := fun h => ca.2.2.ne.symm (congrArg Subtype.val h)
    simp [W,d,f]
  have uw : U∈W := by
    have d : U≠i := fun h => tp (congrArg Subtype.val h)
    have g : U≠j := fun h => tq (congrArg Subtype.val h)
    simp [W,d,g]
  have yu : Y≠U := fun h => ty (congrArg Subtype.val h).symm
  have safe : fibers J W 9 Y=0 := by
    unfold fibers
    rw [card_eq_zero,filter_eq_empty_iff]
    intro k _ bad
    have il : i∈Wᶜ∪k := mem_union_left _ (by simp [W])
    have jl : j∈Wᶜ∪k := mem_union_left _ (by simp [W])
    have ge := PinnedColor34.two J ij (show J.Adj Y i from ca.2.1.symm)
      (show J.Adj Y j from ca.2.2.symm) il jl
    exact (Nat.not_lt_of_ge ge) (mem_filter.mp bad).2
  have touchU : ∃ v,v∉W ∧ J.Adj U v := by
    rcases touches with h|h
    · exact ⟨i,by simp [W],h.symm⟩
    · exact ⟨j,by simp [W],h.symm⟩
  have du := loss U uw
  have nUs : ¬H.Adj U.val s := notS
  rw [if_neg nUs,Nat.add_zero] at du
  have noLoss := RankTuran.local_turan H 3 (by decide) free U.val
  rw [du] at noLoss
  have ls : L.card≤1 := lsize.trans (by rw [lx,card_singleton])
  rw [ss] at range'
  obtain ⟨T,pinned,dom,smallT⟩ := quartic_sample J ws ls yw uw yu safe touchU f fi range' full plain (Or.inl noLoss)
  have ti : i∈T := pinned (by simp [W])
  have tj : j∈T := pinned (by simp [W])
  let D := T.map (Function.Embedding.subtype _)
  have lift {w : S} (m : w∈T) : w.val∈D := mem_map.mpr ⟨w,m,rfl⟩
  have domH : TwoDominates H D := by
    intro w out
    by_cases wm : w∈S
    · let x : S := ⟨w,wm⟩
      have h := dom x (fun m => out (lift m))
      have map : (T.filter (J.Adj x)).map (Function.Embedding.subtype _)=D.filter (H.Adj w) := by
        ext y; constructor
        · intro ym; obtain ⟨b,bm,rfl⟩ := mem_map.mp ym
          exact mem_filter.mpr ⟨lift (mem_filter.mp bm).1,(mem_filter.mp bm).2⟩
        · intro ym; obtain ⟨b,bm,rfl⟩ := mem_map.mp (mem_filter.mp ym).1
          exact mem_map.mpr ⟨b,mem_filter.mpr ⟨bm,(mem_filter.mp ym).2⟩,rfl⟩
      change 2≤(D.filter (H.Adj w)).card
      rwa [←map,card_map]
    · have m : w=e ∨ w=s := by simpa only [S,mem_compl,Classical.not_not,mem_insert,mem_singleton] using wm
      rcases m with rfl|rfl
      · exact PinnedColor34.two H pq ep eq' (lift ti) (lift tj)
      · exact PinnedColor34.two H pq sp sq (lift ti) (lift tj)
  have pair : Wᶜ.card=2 := by simp [W,ij]
  have size : D.card=T.card := card_map ..
  have bound : gamma H≤D.card := Nat.sInf_le ⟨_,domH,rfl⟩
  omega

/-- The exact catalogue inequality in the K₅-free, 28-nonleaf, diversity-29
branch when the square through the ear has a degree-four fourth vertex. -/
theorem exact_quartic_square (t : (types H).card=29) (q : (nonleaves H).card=28) :
    let J := triangleEdges (H.induce (nonleaves H:Set V))
    J.CliqueFree 5 → ∀ e a b s,J.Adj a b → J.neighborFinset e={a,b} →
      s∈additional J e a b → J.degree s=4 → gamma H≤bound H := by
  dsimp only
  intro free e a b s ab en sm ds
  by_contra! bad
  let J := triangleEdges (H.induce (nonleaves H:Set V))
  obtain ⟨n,pos,fi,half,_⟩ := Four28.core_data H t q bad
  obtain ⟨⟨ss,x,y,lx,ns,_,yc,ys⟩,_⟩ := quartic_frontier H t q bad free e a b s ab en sm ds
  obtain ⟨se,as',bs⟩ := (additional_mem J).mp sm
  have win := quartic_layout_saving J n ab en se.symm as'.symm bs.symm (Four28.ear_one J ab.ne en pos)
    pos fi free ss lx ns yc ys
  exact (Nat.not_succ_le_self 13) (half.trans win)

end Graffiti384b.Four28
#print axioms Graffiti384b.Four28.quartic_layout_saving
#print axioms Graffiti384b.Four28.exact_quartic_square
