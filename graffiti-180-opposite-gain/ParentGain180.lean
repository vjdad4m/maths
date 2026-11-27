import ActiveContacts180
import ParentFiber180

set_option warningAsError true
namespace Minimal180.OppositeGain
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Transversals HigherRank
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem root_children (T : SimpleGraph V) (tree : T.IsTree) (r : V) (q : V→V) (k : V→ℕ)
    (down : ∀ x≠r,k (q x)<k x) (take : ∀ x≠r,T.Adj x (q x)) :
    (((univ.erase r).filter (fun x => q x=r)).card)=T.degree r := by
  classical
  have all := parent_image T tree r q k down take
  have eq : (univ.erase r).filter (fun x => q x=r)=T.neighborFinset r := by
    ext x
    constructor
    · intro m
      obtain ⟨nr,ex⟩ := mem_filter.mp m
      exact (T.mem_neighborFinset _ _).mpr (ex ▸ (take x (mem_erase.mp nr).1).symm)
    · intro m
      have ed := (T.mem_neighborFinset _ _).mp m
      have old : s(r,x)∈T.edgeFinset := mem_edgeFinset.mpr ed
      rw [←all] at old
      obtain ⟨u,um,eq⟩ := mem_image.mp old
      rcases Sym2.eq_iff.mp eq with ⟨h,_⟩|⟨h,j⟩
      · exact ((mem_erase.mp um).1 h).elim
      · subst u;exact mem_filter.mpr ⟨um,j⟩
  rw [eq,card_neighborFinset_eq_degree]

/-- Each nonroot doubly marked vertex pays for itself when its parent
is outside both marks. Further children with such parents, and all
nonroot branching in the marked union, are simultaneous credits. -/
theorem parent_gain_with_root (G T : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (sub : T≤G) (tree : T.IsTree) (r : V) (p : Bool) (A : Finset V) (ai : Indep G A)
    (q : V→V) (k : V→ℕ) (down : ∀ x≠r,k (q x)<k x) (take : ∀ x≠r,T.Adj x (q x))
    (pay : ∀ x∈A∩parity G r p,x≠r → q x∉A∪parity G r p)
    (F : Finset V) (extra : ∀ x∈F,x≠r ∧ x∉A∩parity G r p ∧ q x∉A∪parity G r p) :
    (if r∈(A∪parity G r p)\(A∩parity G r p) then T.degree r-1 else 0)+F.card+(∑ v∈(A∪parity G r p).erase r,(T.degree v-2))≤allowance G r p A := by
  classical
  let P := parity G r p
  let X := A∪P
  let I := A∩P
  let E := eligible A P r∩leaves T
  let S := univ.erase r
  let kids (v : V) := (S.filter (fun x => q x=v)).card
  let B (v : V) := if v=r then (if r∈I then 0 else T.degree r-1) else T.degree v-2
  have es : E⊆X := fun x m => mem_union.mpr (eligible_iff.mp (mem_inter.mp m).1).1
  have point (v : V) (vm : v∈X) : 1+(if v=r ∧ r∈I then 1 else 0)+B v ≤
      kids v+(if v∈E then 1 else 0) := by
    by_cases vr : v=r
    · subst v
      have ct := root_children T tree r q k down take
      change kids r=T.degree r at ct
      obtain ⟨w,ed⟩ := exists_adj T tree.isConnected hn r
      have pos := (T.degree_pos_iff_exists_adj r).mpr ⟨w,ed⟩
      by_cases rm : r∈I
      · by_cases one : T.degree r=1
        · have m : r∈E := mem_inter.mpr ⟨eligible_iff.mpr ⟨mem_union.mp vm,Or.inr (mem_inter.mp rm)⟩,
            mem_filter.mpr ⟨mem_univ _,one⟩⟩
          simp [B,rm,m,ct,one]
        · simp only [B,rm,and_self,if_true,true_and,add_zero,ct];split_ifs <;> omega
      · simp only [B,rm,and_false,if_false,if_true,add_zero,ct];split_ifs <;> omega
    · have ct := parent_neighbors T tree r q k down take v vr
      change T.degree v=kids v+1 at ct
      by_cases leaf : T.degree v=1
      · have m : v∈E := mem_inter.mpr ⟨eligible_iff.mpr ⟨mem_union.mp vm,Or.inl vr⟩,
          mem_filter.mpr ⟨mem_univ _,leaf⟩⟩
        simp [B,vr,leaf,m]
      · simp only [vr,false_and,if_false,add_zero,B];split_ifs <;> omega
  have bound := sum_le_sum (s:=X) point
  have iSum : (∑ v∈X,(if v=r ∧ r∈I then 1 else 0 : ℕ))=weight r I := by
    by_cases ri : r∈I
    · have rx : r∈X := mem_union_left _ (mem_inter.mp ri).1
      simp [ri,rx,weight]
    · simp [ri,weight]
  have eSum : (∑ v∈X,(if v∈E then 1 else 0 : ℕ))=E.card := by simp [filter_mem_eq_inter,inter_eq_right.mpr es]
  have bSum : (∑ v∈X,B v)=(if r∈X\I then T.degree r-1 else 0)+∑ v∈X.erase r,(T.degree v-2) := by
    by_cases rm : r∈X
    · rw [←add_sum_erase X B rm]
      simp only [B,if_true,mem_sdiff,rm,true_and]
      have id : (∑ v∈X.erase r,B v)=∑ v∈X.erase r,(T.degree v-2) :=
        sum_congr rfl (fun v vm => if_neg (mem_erase.mp vm).1)
      by_cases ri : r∈I <;> simp [ri,B] at id ⊢ <;> exact id
    · simp only [mem_sdiff,rm,false_and,if_false,zero_add,erase_eq_of_not_mem rm]
      exact sum_congr rfl (fun v vm => if_neg (show v≠r from fun eq => rm (eq ▸ vm)))
  have kSum : (∑ v∈X,kids v)=(S.filter (fun x => q x∈X)).card := sum_card_fiberwise_eq_card_filter ..
  simp only [sum_add_distrib,sum_const,Nat.nsmul_eq_mul,mul_one,iSum,eSum,bSum,kSum] at bound
  have inOut := filter_card_add_filter_neg_card_eq_card (s:=S) (p:=fun x => q x∈X)
  have sNum := card_erase_add_one (mem_univ r)
  change S.card+1=Fintype.card V at sNum
  have inc : I.erase r∪F⊆S.filter (fun x => q x∉X) := by
    intro x m
    rcases mem_union.mp m with im|fm
    · obtain ⟨nr,ii⟩ := mem_erase.mp im
      exact mem_filter.mpr ⟨mem_erase.mpr ⟨nr,mem_univ _⟩,pay x ii nr⟩
    · have h := extra x fm
      exact mem_filter.mpr ⟨mem_erase.mpr ⟨h.1,mem_univ _⟩,h.2.2⟩
  have dis : Disjoint (I.erase r) F := disjoint_left.mpr (fun x m f => (extra x f).2.1 (mem_of_mem_erase m))
  have cnt := card_le_card inc
  rw [card_union_of_disjoint dis] at cnt
  have trim := card_trim I r
  have ac := card_union_add_card_inter A P
  change X.card+I.card=A.card+P.card at ac
  have opt : E.card≤weightedLeaves G (eligible A P r) :=
    le_sup (f:=fun J => (eligible A P r∩leaves J).card) (mem_filter.mpr ⟨mem_univ _,sub,tree⟩)
  have eq := allowance_eq G gc hn r p A ai
  change 1+A.card+P.card+allowance G r p A=weightedLeaves G (eligible A P r)+Fintype.card V at eq
  change (if r∈X\I then T.degree r-1 else 0)+F.card+(∑ v∈X.erase r,(T.degree v-2))≤_
  omega

theorem parent_gain (G T : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (sub : T≤G) (tree : T.IsTree) (r : V) (p : Bool) (A : Finset V) (ai : Indep G A)
    (q : V→V) (k : V→ℕ) (down : ∀ x≠r,k (q x)<k x) (take : ∀ x≠r,T.Adj x (q x))
    (pay : ∀ x∈A∩parity G r p,x≠r → q x∉A∪parity G r p)
    (F : Finset V) (extra : ∀ x∈F,x≠r ∧ x∉A∩parity G r p ∧ q x∉A∪parity G r p) :
    F.card+(∑ v∈(A∪parity G r p).erase r,(T.degree v-2))≤allowance G r p A := by
  have full := parent_gain_with_root G T gc hn sub tree r p A ai q k down take pay F extra
  omega

#print axioms parent_gain_with_root
#print axioms parent_gain
end Minimal180.OppositeGain
