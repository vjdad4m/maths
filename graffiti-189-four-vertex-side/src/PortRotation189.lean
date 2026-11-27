import CutDistance189
namespace Graffiti189LongestPath.TwoCut.PortRotation
open SimpleGraph SimpleGraph.Walk Finset
variable {V : Type*} {G : SimpleGraph V}
set_option maxHeartbeats 2100000
set_option linter.unusedSectionVars false

private lemma lengths_take_drop {x y : V} (p : G.Walk x y) (n : ℕ) (hn : n ≤ p.length) :
    (p.take n).length = n ∧ (p.drop n).length = p.length - n := by
  induction p generalizing n with
  | nil =>
    have : n=0 := by simpa using hn
    subst n
    exact ⟨rfl,rfl⟩
  | @cons a b c h p ih =>
    cases n with
    | zero => simp [Walk.take,Walk.drop]
    | succ n =>
      have hh : n ≤ p.length := by
        simp only [length_cons] at hn
        omega
      obtain ⟨h₁,h₂⟩ := ih n hh
      simp [Walk.take,Walk.drop,h₁,h₂,Nat.add_sub_add_right]



private lemma split_path_edge {a b : V} (p : G.Walk a b) (j : ℕ) (hj : j < p.length) :
    (p.take j).append (.cons (p.adj_getVert_succ hj) (p.drop (j+1))) = p := by
  induction p generalizing j with
  | nil => simp at hj
  | @cons a u b edge p ih =>
    cases j with
    | zero =>
      have h : HEq (p.drop 0) p := by cases p <;> rfl
      simpa [Walk.take,Walk.drop] using h
    | succ j =>
      have hj' : j < p.length := by simpa using hj
      exact congrArg (Walk.cons edge) (ih j hj')

/-- Pósa rotation at the initial endpoint preserves the vertex set. -/
private theorem rotate_start {a b : V} {p : G.Walk a b} (hp : p.IsPath) (j : ℕ) (hj : j < p.length)
    (jump : G.Adj a (p.getVert (j+1))) :
    ∃ q : G.Walk (p.getVert j) b, q.IsPath ∧
      (∀ z : V, z ∈ p.support ↔ z ∈ q.support) ∧
      q.length = p.length ∧ q.getVert j = a ∧ q.getVert (j+1) = p.getVert (j+1) := by
  let l := p.take j
  let r := p.drop (j+1)
  let q := l.reverse.append (.cons jump r)
  have split := split_path_edge p j hj
  have ps : p.support = l.support ++ r.support := by
    conv_lhs => rw [←split]
    simp only [support_append,support_cons,List.tail_cons,l,r]
  have qs : q.support = l.support.reverse ++ r.support := by
    simp only [q,support_append,support_reverse,support_cons,List.tail_cons]
  have qpath : q.IsPath := by
    rw [isPath_def,qs,List.nodup_append]
    have nod := hp.support_nodup
    rw [ps,List.nodup_append] at nod
    refine ⟨List.nodup_reverse.mpr nod.1,nod.2.1,?_⟩
    intro u hu hv
    exact nod.2.2 (List.mem_reverse.mp hu) hv
  have qsupport (z : V) : z ∈ p.support ↔ z ∈ q.support := by
    rw [ps,qs]
    simp
  have llen : l.length = j := (lengths_take_drop p j (by omega)).1
  have rlen : r.length = p.length-(j+1) := (lengths_take_drop p (j+1) (by omega)).2
  have qlen : q.length = p.length := by
    simp only [q,length_append,length_reverse,length_cons,llen,rlen]
    omega
  refine ⟨q,qpath,qsupport,qlen,?_,?_⟩
  · simp [q,getVert_append,llen]
  · have jj : j+1-j=1 := by omega
    simp [q,getVert_append,llen,jj]


variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
def MaxFrom (P : Finset V) {s t : V} (p : G.Walk s t) : Prop :=
  s∈P ∧ p.IsPath ∧ ∀ u∈P, ∀ v : V, ∀ q : G.Walk u v, q.IsPath → q.length≤p.length

theorem exists_max (P : Finset V) (pos : P.Nonempty) :
    ∃ s t : V, ∃ p : G.Walk s t, MaxFrom P p := by
  classical
  let L := (range (Fintype.card V)).filter fun i =>
    ∃ u∈P, ∃ v : V, ∃ w : G.Walk u v, w.IsPath ∧ w.length=i
  obtain ⟨u,up⟩ := pos
  have cn : 0<Fintype.card V := Fintype.card_pos_iff.mpr ⟨u⟩
  have z : 0∈L := mem_filter.mpr ⟨mem_range.mpr cn,u,up,u,Walk.nil,IsPath.nil,rfl⟩
  let k := L.max' ⟨0,z⟩
  obtain ⟨s,sp,t,p,hp,eq⟩ := (mem_filter.mp (max'_mem L ⟨0,z⟩)).2
  refine ⟨s,t,p,sp,hp,?_⟩
  intro v vp w q hq
  have cp : q.length<Fintype.card V := by
    have cb := card_le_univ q.support.toFinset
    rw [List.toFinset_card_of_nodup hq.support_nodup,length_support] at cb
    omega
  have qm : q.length∈L := mem_filter.mpr ⟨mem_range.mpr cp,v,vp,w,q,hq,rfl⟩
  rw [eq]
  exact le_max' L _ qm

theorem terminal_closed {P : Finset V} {s t : V} {p : G.Walk s t}
    (hp : MaxFrom P p) {x : V} (tx : G.Adj t x) : x∈p.support := by
  by_contra off
  have r : (Walk.cons tx.symm p.reverse).reverse.IsPath :=
    (hp.2.1.reverse.cons (by simpa using off)).reverse
  have le := hp.2.2 s hp.1 x _ r
  simp at le

theorem rotated_set {P : Finset V} {s t : V} {p : G.Walk s t}
    (hp : MaxFrom P p) :
    ∃ R : Finset V, R⊆p.support.toFinset ∧ s∉R ∧ R.card=G.degree t ∧
      ∀ x∈R, ∃ q : G.Walk s x, MaxFrom P q ∧ (∀ z,z∈q.support ↔ z∈p.support) := by
  let q := p.reverse
  let J := (range q.length).filter (fun i => G.Adj t (q.getVert (i+1)))
  let R := J.image q.getVert
  have memJ {j : ℕ} : j∈J ↔ j<q.length ∧ G.Adj t (q.getVert (j+1)) := by simp [J]
  have inj (f : ℕ → V) (inj : ∀ i∈J, ∀ j∈J, f i=f j → i=j) :
      (J.image f).card=J.card := card_image_iff.mpr inj
  have eq : J.image (fun i => q.getVert (i+1)) = G.neighborFinset t := by
    ext x
    constructor
    · intro e
      obtain ⟨j,jj,rfl⟩ := mem_image.mp e
      exact (mem_neighborFinset G t _).mpr (memJ.mp jj).2
    · intro e
      have edge := (mem_neighborFinset G t x).mp e
      have support : x∈q.support := by simpa [q] using terminal_closed hp edge
      obtain ⟨j,jx,jq⟩ := mem_support_iff_exists_getVert.mp support
      have jpos : 0<j := by
        by_contra! z
        have j0 : j=0 := by omega
        rw [j0,getVert_zero] at jx
        exact edge.ne jx
      have jprev : j-1+1=j := by omega
      exact mem_image.mpr ⟨j-1,memJ.mpr ⟨by omega,by rwa [jprev,jx]⟩,by rwa [jprev]⟩
  have eqcard : J.card=G.degree t := by
    have h := inj (fun i => q.getVert (i+1)) (by
      intro i hi j hj e
      have eq := hp.2.1.reverse.getVert_injOn
        (show i+1≤q.length from (memJ.mp hi).1) (show j+1≤q.length from (memJ.mp hj).1) e
      omega)
    rw [eq,card_neighborFinset_eq_degree] at h
    exact h.symm
  have Rcard : R.card=J.card := inj q.getVert (by
    intro i hi j hj e
    exact hp.2.1.reverse.getVert_injOn (memJ.mp hi).1.le (memJ.mp hj).1.le e)
  refine ⟨R,?_,?_,Rcard.trans eqcard,?_⟩
  · intro x e
    obtain ⟨j,_,rfl⟩ := mem_image.mp e
    exact List.mem_toFinset.mpr (by simpa [q] using q.getVert_mem_support j)
  · intro e
    obtain ⟨j,jj,js⟩ := mem_image.mp e
    have js' : q.getVert j=q.getVert q.length := by rw [getVert_length]; exact js
    have same := hp.2.1.reverse.getVert_injOn (memJ.mp jj).1.le (show q.length≤p.reverse.length from le_rfl) js'
    have lj := (memJ.mp jj).1
    omega
  · intro x e
    obtain ⟨j,jj,rfl⟩ := mem_image.mp e
    obtain ⟨w,hpath,ws,len,_,_⟩ := rotate_start hp.2.1.reverse j (memJ.mp jj).1 (memJ.mp jj).2
    refine ⟨w.reverse,⟨hp.1,hpath.reverse,?_⟩,?_⟩
    · intro u hu v r hr
      simpa only [length_reverse,len,q] using hp.2.2 u hu v r hr
    · intro z
      simpa [q] using (ws z).symm

theorem omitted_avoids_rotated {P R : Finset V} {s t : V} {p : G.Walk s t}
    (rot : ∀ x∈R, ∃ q : G.Walk s x, MaxFrom P q ∧ (∀ z,z∈q.support ↔ z∈p.support))
    {x y : V} (xo : x∉p.support) (yr : y∈R) : ¬G.Adj x y := by
  obtain ⟨q,hq,same⟩ := rot y yr
  intro e
  exact xo ((same _).mp (terminal_closed hq e.symm))

#print axioms rotated_set

private theorem marker_cards {s t : V} {p : G.Walk s t} (hp : p.IsPath)
    (sinside : ∀ x, G.Adj s x → x∈p.support) (tinside : ∀ x,G.Adj t x → x∈p.support) :
    ((range p.length).filter (fun i => G.Adj s (p.getVert (i+1)))).card=G.degree s ∧
    ((range p.length).filter (fun i => G.Adj t (p.getVert i))).card=G.degree t := by
  let L := (range p.length).filter (fun i => G.Adj s (p.getVert (i+1)))
  let R := (range p.length).filter (fun i => G.Adj t (p.getVert i))
  have eL : L.image (fun i => p.getVert (i+1))=G.neighborFinset s := by
    ext x
    constructor
    · intro hx
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
      exact (mem_neighborFinset G s _).mpr (mem_filter.mp hi).2
    · intro hx
      have sAdj := (mem_neighborFinset G s x).mp hx
      obtain ⟨i,e,hi⟩ := mem_support_iff_exists_getVert.mp (sinside x sAdj)
      have iz : 0 < i := by
        by_contra! z
        have eq : i=0 := by omega
        rw [eq,getVert_zero] at e
        exact sAdj.ne e
      have e' : i-1+1=i := by omega
      exact mem_image.mpr ⟨i-1,mem_filter.mpr ⟨mem_range.mpr (by omega),by rwa [e',e]⟩,by rwa [e']⟩
  have eR : R.image p.getVert=G.neighborFinset t := by
    ext x
    constructor
    · intro hx
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
      exact (mem_neighborFinset G t _).mpr (mem_filter.mp hi).2
    · intro hx
      have tAdj := (mem_neighborFinset G t x).mp hx
      obtain ⟨i,e,hi⟩ := mem_support_iff_exists_getVert.mp (tinside x tAdj)
      have im : i<p.length := by
        apply Nat.lt_of_le_of_ne hi
        intro eq
        rw [eq,getVert_length] at e
        exact tAdj.ne e
      exact mem_image.mpr ⟨i,mem_filter.mpr ⟨mem_range.mpr im,by rwa [e]⟩,e⟩
  have l : (L.image (fun i => p.getVert (i+1))).card=L.card := card_image_iff.mpr (by
    intro i hi j hj eq
    have e := hp.getVert_injOn (show i+1≤p.length from mem_range.mp (mem_filter.mp hi).1)
      (show j+1≤p.length from mem_range.mp (mem_filter.mp hj).1) eq
    omega)
  have r : (R.image p.getVert).card=R.card := card_image_iff.mpr (by
    intro i hi j hj eq
    exact hp.getVert_injOn (mem_range.mp (mem_filter.mp hi).1).le (mem_range.mp (mem_filter.mp hj).1).le eq)
  rw [eL,card_neighborFinset_eq_degree] at l
  rw [eR,card_neighborFinset_eq_degree] at r
  exact ⟨l.symm,r.symm⟩

theorem close_path_from_degrees {s t : V} {p : G.Walk s t} (hp : p.IsPath)
    (sinside : ∀ x, G.Adj s x → x∈p.support) (tinside : ∀ x,G.Adj t x → x∈p.support)
    (sum : p.length<G.degree s+G.degree t) :
    ∃ z, ∃ q : G.Walk s z, q.IsPath ∧ G.Adj z s ∧ (∀ x,x∈q.support ↔ x∈p.support) := by
  let L := (range p.length).filter (fun i => G.Adj s (p.getVert (i+1)))
  let R := (range p.length).filter (fun i => G.Adj t (p.getVert i))
  obtain ⟨lc,rc⟩ := marker_cards hp sinside tinside
  have ex : ∃ i∈L,i∈R := by
    by_cases ex : ∃ i∈L,i∈R
    · exact ex
    exfalso
    have dis : Disjoint L R := disjoint_left.mpr (fun i li ri => ex ⟨i,li,ri⟩)
    have sub : L∪R ⊆ range p.length := union_subset (filter_subset _ _) (filter_subset _ _)
    have c := card_le_card sub
    change L.card=G.degree s at lc
    change R.card=G.degree t at rc
    rw [card_union_of_disjoint dis,card_range,lc,rc] at c
    omega
  obtain ⟨i,il,ir⟩ := ex
  have hi := mem_range.mp (mem_filter.mp il).1
  let l := p.take i
  let r := p.drop (i+1)
  have edge : G.Adj (p.getVert i) t := (mem_filter.mp ir).2.symm
  let q := l.append (.cons edge r.reverse)
  have split := split_path_edge p i hi
  have ps : p.support=l.support++r.support := by
    conv_lhs => rw [←split]
    simp only [support_append,support_cons,List.tail_cons,l,r]
  have qs : q.support=l.support++r.support.reverse := by
    simp only [q,support_append,support_reverse,support_cons,List.tail_cons]
  have nd := hp.support_nodup
  rw [ps,List.nodup_append] at nd
  have qpath : q.IsPath := by
    rw [isPath_def,qs,List.nodup_append]
    exact ⟨nd.1,List.nodup_reverse.mpr nd.2.1,
      fun x xl xr => nd.2.2 xl (List.mem_reverse.mp xr)⟩
  exact ⟨p.getVert (i+1),q,qpath,(mem_filter.mp il).2.symm,fun x => by simp [ps,qs]⟩

theorem reroot_closed_path {s t x : V} {p : G.Walk s t} (hp : p.IsPath)
    (closing : G.Adj t s) (xs : x∈p.support) :
    ∃ y, ∃ q : G.Walk x y, q.IsPath ∧ x≠y ∧ (∀ z,z∈q.support↔z∈p.support) := by
  by_cases e : x=s
  · subst x
    exact ⟨t,p,hp,closing.ne.symm,fun _ => Iff.rfl⟩
  obtain ⟨j,jx,jp⟩ := mem_support_iff_exists_getVert.mp xs
  have pos : 0<j := by
    by_contra! zero
    have z : j=0 := by omega
    rw [z,getVert_zero] at jx
    exact e jx.symm
  let i := j-1
  have hi : i<p.length := by omega
  have eq : i+1=j := by omega
  have xx : p.getVert (i+1)=x := by rwa [eq]
  let l := p.take i
  let r := p.drop (i+1)
  let q := r.append (.cons closing l)
  have split := split_path_edge p i hi
  have ps : p.support=l.support++r.support := by
    conv_lhs => rw [←split]
    simp only [support_append,support_cons,List.tail_cons,l,r]
  have qs : q.support=r.support++l.support := by
    simp only [q,support_append,support_cons,List.tail_cons]
  have nd := hp.support_nodup
  rw [ps,List.nodup_append] at nd
  have qpath : q.IsPath := by
    rw [isPath_def,qs,List.nodup_append]
    exact ⟨nd.2.1,nd.1,fun x xr xl => nd.2.2 xl xr⟩
  have xy : x≠p.getVert i := by
    intro he
    have equiv := hp.getVert_injOn (show i+1≤p.length from hi) hi.le (xx.trans he)
    omega
  exact ⟨p.getVert i,q.copy xx rfl,by simpa using qpath,xy,fun z => by
    simp only [support_copy,ps,qs,List.mem_append,or_comm]⟩

#print axioms close_path_from_degrees
#print axioms reroot_closed_path
end Graffiti189LongestPath.TwoCut.PortRotation
