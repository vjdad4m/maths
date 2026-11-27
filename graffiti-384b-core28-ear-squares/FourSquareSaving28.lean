import FourPairSample28
namespace Graffiti384b.Four28
open Finset SimpleGraph
open private Repair.full_nbr Repair.nbr_mono from Repair384b
open private FiniteRange.bad from FiniteRange384b
open private ForcedCubics.third_contact from SharedSaving33
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

def leaks (s p q : V) := (H.neighborFinset s).filter
  (fun w => w≠p ∧ w≠q ∧ ¬H.Adj w p ∧ ¬H.Adj w q)

private theorem mono_cap : ∀ d j : Fin 11,d.val≤j.val → RankTable.cap d 3≤RankTable.cap j 3 := by decide

/-- Omit both the ear and a low-count fourth vertex on its square, retaining
their common neighbors. At counts two or three one exterior neighbor may
lose its support without receiving credit from either retained neighbor. -/
theorem square_saving_routes {e s p q : V} (n : Fintype.card V=28) (pq : p≠q)
    (en : H.neighborFinset e={p,q}) (es : e≠s) (ep : H.Adj e p) (eq' : H.Adj e q)
    (sp : H.Adj s p) (sq : H.Adj s q) (se : trianglesAt H e=1)
    (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H))
    (free : H.CliqueFree 5) (sm : trianglesAt H s∈Icc 2 5)
    (route : (leaks H s p q).card≤allowance (trianglesAt H s) ∨
      ((trianglesAt H s=2 ∨ trianglesAt H s=3) ∧
        ∃ x y,leaks H s p q={x,y} ∧ H.Adj x y)) : gamma H≤13 := by
  classical
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
    exact (a.trans_eq old).trans ((mono_cap ⟨H.degree w.val,by omega⟩ ⟨J.degree w+1,by omega⟩ le).trans_eq new.symm)
  have plain (w : S) (wm : w∈W) (nl : w∉L) (unc : ∀ z,z∉W → ¬J.Adj w z) :
      f w≤(turanGraph (J.degree w) 3).edgeFinset.card ∨ 10≤J.degree w := by
    have np : ¬H.Adj w.val p := unc i (by simp [W])
    have nq : ¬H.Adj w.val q := unc j (by simp [W])
    have no : ¬H.Adj w.val s := fun ed => nl (mem_filter.mpr ⟨wm,mem_filter.mpr
      ⟨(H.mem_neighborFinset ..).mpr ed.symm,(ext w wm).1,(ext w wm).2,np,nq⟩⟩)
    have h := RankTuran.local_turan H 3 (by decide) free w.val
    rw [loss w wm,if_neg no,Nat.add_zero] at h
    exact Or.inl h
  obtain ⟨T,pinned,dom,smallT⟩ : ∃ T,Wᶜ⊆T ∧ TwoDominates J T ∧ T.card≤Wᶜ.card+11 := by
    rcases route with few|⟨low,x,y,both,xy⟩
    · obtain ⟨k,km,small⟩ := square_sample J ws sm (lsize.trans few) f fi range' full plain
      obtain ⟨_,ks⟩ := mem_powersetCard.mp km
      let T := Wᶜ∪k∪FiniteRange.bad J W k
      have front : Wᶜ∪k⊆T := subset_union_left
      have dom : TwoDominates J T := by
        intro w out
        have wm : w∈W := by apply Classical.byContradiction; intro no; exact out (front (mem_union_left _ (mem_compl.mpr no)))
        apply (show 2≤nbr J w (Wᶜ∪k) from ?_).trans (Repair.nbr_mono J w front)
        apply Nat.le_of_not_gt; intro low
        exact out (mem_union_right _ (mem_filter.mpr ⟨mem_sdiff.mpr ⟨wm,fun h => out (front (mem_union_right _ h))⟩,low⟩))
      have size := card_union_le (Wᶜ∪k) (FiniteRange.bad J W k)
      have first := card_union_le Wᶜ k
      refine ⟨T,subset_union_left.trans front,dom,?_⟩
      change T.card≤_ at size
      omega
    · have members {w : V} (m : w∈leaks H s p q) : w∈S ∧ w≠p ∧ w≠q ∧ ¬H.Adj w p ∧ ¬H.Adj w q := by
        obtain ⟨sn,wp,wq,np,nq⟩ := mem_filter.mp m
        have sw := (H.mem_neighborFinset ..).mp sn
        have we : w≠e := by
          intro eq; subst w
          have m := (H.mem_neighborFinset ..).mpr sw.symm
          rw [en] at m
          exact (mem_insert.mp m).elim sp.ne (fun z => sq.ne (mem_singleton.mp z))
        exact ⟨by simp [S,we,sw.ne.symm],wp,wq,np,nq⟩
      have xx := members (show x∈leaks H s p q from both ▸ mem_insert_self ..)
      have yy := members (show y∈leaks H s p q from both ▸ mem_insert_of_mem (mem_singleton_self _))
      let X : S := ⟨x,xx.1⟩
      let Y : S := ⟨y,yy.1⟩
      have neighborhood {z : S} (np : ¬H.Adj z.val p) (nq : ¬H.Adj z.val q) : J.neighborFinset z⊆W := by
        intro w wm
        have edge := (J.mem_neighborFinset ..).mp wm
        apply mem_compl.mpr
        intro pin
        rcases mem_insert.mp pin with rfl|wq
        · exact np edge
        · rw [mem_singleton.mp wq] at edge; exact nq edge
      have forPair (w : S) (wm : w∈W) (ex : w∉({X,Y}:Finset S)) (nc : ∀ z,z∉W → ¬J.Adj w z) :
          f w≤(turanGraph (J.degree w) 3).edgeFinset.card ∨ 10≤J.degree w := by
        apply plain w wm _ nc
        intro wl
        have m := (mem_filter.mp wl).2
        rw [both] at m
        rcases mem_insert.mp m with b|b
        · have eq : w=X := Subtype.ext b
          exact ex (eq ▸ mem_insert_self ..)
        · have eq : w=Y := Subtype.ext (mem_singleton.mp b)
          exact ex (eq ▸ mem_insert_of_mem (mem_singleton_self _))
      exact repaired_sample J ws low (show J.Adj X Y from xy)
        (neighborhood xx.2.2.2.1 xx.2.2.2.2) (neighborhood yy.2.2.2.1 yy.2.2.2.2) f fi range' full forPair
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

theorem cubic_square {e s p q : V} (n : Fintype.card V=28) (pq : p≠q)
    (en : H.neighborFinset e={p,q}) (es : e≠s) (sp : H.Adj s p) (sq : H.Adj s q)
    (se : trianglesAt H e=1) (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H))
    (free : H.CliqueFree 5) (ds : H.degree s=3) : gamma H≤13 := by
  have de : H.degree e=2 := by rw [←card_neighborFinset_eq_degree,en,card_pair pq]
  have scores := HighEar.cubic_scores H de ds pos inj
  have small : trianglesAt H s∈Icc 2 5 := mem_Icc.mpr (by omega)
  have no : leaks H s p q=∅ := filter_eq_empty_iff.mpr (by
    intro w wm cond
    obtain ⟨wp,wq,np,nq⟩ := cond
    exact (ForcedCubics.third_contact H ds (by omega) pq sp sq ((H.mem_neighborFinset ..).mp wm) wp wq).elim np nq)
  exact square_saving_routes H n pq en es ((H.mem_neighborFinset ..).mp (en ▸ mem_insert_self ..))
    ((H.mem_neighborFinset ..).mp (en ▸ mem_insert_of_mem (mem_singleton_self _))) sp sq se pos inj free small
    (Or.inl (by rw [no,card_empty]; exact Nat.zero_le _))

end Graffiti384b.Four28
#print axioms Graffiti384b.Four28.square_saving_routes
#print axioms Graffiti384b.Four28.cubic_square
