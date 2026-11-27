import SquareFrame29
import EarFixture33
namespace Graffiti384b.Squares29
open Finset SimpleGraph EarFrame33 LowSample
open private Squares29.merge from SquareFrame29
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] in
private theorem pair_at {S : Finset V} {r : V} (sz : S.card=2) (m : r∈S) :
    ∃ a,r≠a ∧ S={r,a} := by
  obtain ⟨a,b,ab,eq⟩ := card_eq_two.mp sz
  rw [eq] at m ⊢
  rcases mem_insert.mp m with rfl|rb
  · exact ⟨b,ab,rfl⟩
  · obtain rfl := mem_singleton.mp rb
    exact ⟨a,ab.symm,pair_comm ..⟩

/-- The two anchor pairs share exactly one vertex. At least one ear has
a unique opposite vertex, namely the nonshared anchor of the other ear. -/
theorem rigid_pair (sp : Sparse G) {e f x y : V} (ne : e≠f) (s : Opposite G e x) (v : Opposite G f y) :
    ∃ r a b,r≠a ∧ r≠b ∧ a≠b ∧ G.neighborFinset e={r,a} ∧ G.neighborFinset f={r,b} ∧
      ((∀ z,Opposite G e z → z=b) ∨ (∀ z,Opposite G f z → z=a)) := by
  obtain ⟨r,rm⟩ := (contact G sp ne s v).1
  obtain ⟨a,ra,ea⟩ := pair_at ((card_neighborFinset_eq_degree ..).trans s.1) (mem_inter.mp rm).1
  obtain ⟨b,rb,fb⟩ := pair_at ((card_neighborFinset_eq_degree ..).trans v.1) (mem_inter.mp rm).2
  have alt {i j : V} (si : Opposite G e i) (vj : Opposite G f j) : i=b ∨ j=a := by
    have ir : i≠r := ((G.mem_neighborFinset ..).mp (si.2.2 (mem_inter.mp rm).1)).ne
    have jr : j≠r := ((G.mem_neighborFinset ..).mp (vj.2.2 (mem_inter.mp rm).2)).ne
    have z := (contact G sp ne si vj).2
    simp only [ea,fb,mem_insert,mem_singleton] at z
    tauto
  have ab : a≠b := by
    intro eq; subst b
    rcases alt s v with eq|eq
    · exact ((G.mem_neighborFinset ..).mp (s.2.2 (ea ▸ mem_insert_of_mem (mem_singleton_self _)))).ne eq
    · exact ((G.mem_neighborFinset ..).mp (v.2.2 (fb ▸ mem_insert_of_mem (mem_singleton_self _)))).ne eq
  refine ⟨r,a,b,ra,rb,ab,ea,fb,?_⟩
  by_cases all : ∀ z,Opposite G e z → z=b
  · exact Or.inl all
  push_neg at all
  obtain ⟨z,sz,zb⟩ := all
  exact Or.inr (fun j vj => (alt sz vj).resolve_left zb)

private theorem sides {e f x y r a b : V} (sp : Sparse G) (ne : e≠f)
    (s : Opposite G e x) (v : Opposite G f y) (ea : G.neighborFinset e={r,a}) (fb : G.neighborFinset f={r,b}) :
    G.Adj a b ∧ (G.Adj r a ∨ G.Adj r b) := by
  have see {u z p q : V} (w : Opposite G u z) (eq : G.neighborFinset u={p,q}) :
      G.Adj z p ∧ G.Adj z q :=
    ⟨(G.mem_neighborFinset ..).mp (w.2.2 (eq ▸ mem_insert_self _ _)),
      (G.mem_neighborFinset ..).mp (w.2.2 (eq ▸ mem_insert_of_mem (mem_singleton_self _)))⟩
  obtain ⟨xr,xa⟩ := see s ea
  obtain ⟨yr,yb⟩ := see v fb
  have z := (contact G sp ne s v).2
  simp only [ea,fb,mem_insert,mem_singleton] at z
  rcases z with (eq|eq)|(eq|eq)
  · exact (xr.ne eq).elim
  · subst b; exact ⟨xa.symm,Or.inr xr.symm⟩
  · exact (yr.ne eq).elim
  · subst a; exact ⟨yb,Or.inl yr.symm⟩

private theorem star_close {e f x y r a b c : V} (sp : Sparse G) (ne : e≠f)
    (s : Opposite G e x) (v : Opposite G f y) (ea : G.neighborFinset e={r,a}) (fb : G.neighborFinset f={r,b})
    (ec : e≠c) (fc : f≠c) (cr : G.Adj c r) (ca : G.Adj c a) (cb : G.Adj c b) : False := by
  have make {u p : V} (du : G.degree u=2) (uc : u≠c) (eq : G.neighborFinset u={r,p}) (cp : G.Adj c p) :
      Opposite G u c := ⟨du,uc,by
        rw [eq]; exact insert_subset ((G.mem_neighborFinset ..).mpr cr) (singleton_subset_iff.mpr ((G.mem_neighborFinset ..).mpr cp))⟩
  have z := (contact G sp ne (make s.1 ec ea ca) (make v.1 fc fb cb)).2
  simp [ea,fb,cr.ne,ca.ne,cb.ne] at z

private theorem triangle_close {e f g x y z r a b : V} (sp : Sparse G) (ef : e≠f) (eg : e≠g) (fg : f≠g)
    (s : Opposite G e x) (v : Opposite G f y) (w : Opposite G g z) (ra : r≠a) (rb : r≠b) (ab : a≠b)
    (ea : G.neighborFinset e={r,a}) (fb : G.neighborFinset f={r,b}) (gc : G.neighborFinset g={a,b}) : False := by
  let L : Finset V := {e,f,g}
  let R : Finset V := {r,a,b}
  have edges {u p q : V} (eq : G.neighborFinset u={p,q}) : G.Adj u p ∧ G.Adj u q :=
    ⟨(G.mem_neighborFinset ..).mp (eq ▸ mem_insert_self _ _),(G.mem_neighborFinset ..).mp (eq ▸ mem_insert_of_mem (mem_singleton_self _))⟩
  obtain ⟨er,ee⟩ := edges ea
  obtain ⟨fr,ff⟩ := edges fb
  obtain ⟨ga,gb⟩ := edges gc
  have off {u i j l : V} (o : Opposite G u l) (ij : u≠i) (di : G.degree i=2) (jm : j∈G.neighborFinset u) :
      i≠j := fun eq => outside G sp ij o di (mem_union_right _ (eq ▸ jm))
  have eb := off v ef.symm s.1 (fb ▸ mem_insert_of_mem (mem_singleton_self b))
  have fa := off s ef v.1 (ea ▸ mem_insert_of_mem (mem_singleton_self a))
  have gr := off s eg w.1 (ea ▸ mem_insert_self r {a})
  have u : Frame G L R := by
    refine ⟨?_,?_,?_⟩
    · simp [L,R,disjoint_left,er.ne,ee.ne,eb,fr.ne,ff.ne,fa,gr,ga.ne,gb.ne]
    · intro k km
      rcases (show k=e ∨ k=f ∨ k=g by simpa [L] using km) with rfl|rfl|rfl
      · exact PinnedColor34.two G ra er ee (by simp [R]) (by simp [R])
      · exact PinnedColor34.two G rb fr ff (by simp [R]) (by simp [R])
      · exact PinnedColor34.two G ab ga gb (by simp [R]) (by simp [R])
    · intro k km
      rcases (show k=r ∨ k=a ∨ k=b by simpa [R] using km) with rfl|rfl|rfl
      · exact PinnedColor34.two G ef er.symm fr.symm (by simp [L]) (by simp [L])
      · exact PinnedColor34.two G eg ee.symm ga.symm (by simp [L]) (by simp [L])
      · exact PinnedColor34.two G fg ff.symm gb.symm (by simp [L]) (by simp [L])
  exact ef (sp _ _ u e (mem_union_left _ (by simp [L])) f (mem_union_left _ (by simp [L])) s.1 v.1)

/-- Three distinct degree-two vertices on four-cycles force a protected
frame containing at least two of them. -/
theorem triple (sp : Sparse G) {e f g x y z : V} (ef : e≠f) (eg : e≠g) (fg : f≠g)
    (s : Opposite G e x) (v : Opposite G f y) (w : Opposite G g z) : False := by
  obtain ⟨r,a,b,ra,rb,ab,ea,fb,_⟩ := rigid_pair G sp ef s v
  have dg := (card_neighborFinset_eq_degree G g).trans w.1
  by_cases rg : r∈G.neighborFinset g
  · obtain ⟨c,_,gc⟩ := pair_at dg rg
    obtain ⟨ab',rchoice⟩ := sides G sp ef s v ea fb
    have ac' := (sides G sp eg s w ea gc).1
    have bc' := (sides G sp fg v w fb gc).1
    have anti {u v' i j : V} (ne : u≠v') (sv : Opposite G v' j) (du : G.degree u=2) (m : i∈G.neighborFinset v') : u≠i :=
      fun h => outside G sp ne.symm sv du (mem_union_right _ (h ▸ m))
    rcases rchoice with raa|rbb
    · have am : a∈G.neighborFinset e := ea ▸ mem_insert_of_mem (mem_singleton_self _)
      exact star_close G sp fg v w fb gc (anti ef.symm s v.1 am) (anti eg.symm s w.1 am) raa.symm ab' ac'
    · have bm : b∈G.neighborFinset f := fb ▸ mem_insert_of_mem (mem_singleton_self _)
      exact star_close G sp eg s w ea gc (anti ef v s.1 bm) (anti fg.symm v w.1 bm) rbb.symm ab'.symm bc'
  · obtain ⟨i,im⟩ := (contact G sp eg s w).1
    obtain ⟨j,jm⟩ := (contact G sp fg v w).1
    have pick {u d k : V} (eq : G.neighborFinset u={r,d}) (km : k∈G.neighborFinset u∩G.neighborFinset g) :
        d∈G.neighborFinset g := by
      obtain ⟨ku,kg⟩ := mem_inter.mp km
      rw [eq,mem_insert,mem_singleton] at ku
      exact ku.elim (fun kr => (rg (kr ▸ kg)).elim) (fun kd => kd ▸ kg)
    have pair := insert_subset (pick ea im) (singleton_subset_iff.mpr (pick fb jm))
    have gc := (eq_of_subset_of_card_le pair (by rw [dg,card_pair ab])).symm
    exact triangle_close G sp ef eg fg s v w ra rb ab ea fb gc

/-- At the 32-nonleaf quota some degree-two vertex is on no four-cycle:
its two neighbors have it as their unique common neighbor. -/
theorem thin_at_32 (t : (types G).card=31) (q : (nonleaves G).card=32) (bad : bound G<gamma G) :
    ∃ e a b,G.degree e=2 ∧ a≠b ∧ G.neighborFinset e={a,b} ∧
      G.neighborFinset a∩G.neighborFinset b={e} := by
  classical
  obtain ⟨_,sz⟩ := Cover31.residual G t q bad
  have sp := sparse G bad
  obtain ⟨u,v,w,uv,uw,vw,eq⟩ := card_eq_three.mp sz
  have degree (i : V) (m : i∈twos G) : G.degree i=2 := by
    obtain ⟨nl,nh⟩ := mem_sdiff.mp m
    have lo : 2≤G.degree i := (mem_filter.mp nl).2
    have hi : ¬3≤G.degree i := fun d => nh (mem_filter.mpr ⟨mem_univ _,d⟩)
    omega
  have low : ∃ e,G.degree e=2 ∧ ∀ x,¬Opposite G e x := by
    apply Classical.byContradiction; intro no; push_neg at no
    obtain ⟨x,s⟩ := no u (degree _ (eq ▸ (by simp)))
    obtain ⟨y,v'⟩ := no v (degree _ (eq ▸ (by simp)))
    obtain ⟨z,w'⟩ := no w (degree _ (eq ▸ (by simp)))
    exact triple G sp uv uw vw s v' w'
  obtain ⟨e,de,off⟩ := low
  obtain ⟨a,b,ab,en⟩ := card_eq_two.mp ((card_neighborFinset_eq_degree G e).trans de)
  have ea : G.Adj e a := (G.mem_neighborFinset ..).mp (en ▸ mem_insert_self _ _)
  have eb : G.Adj e b := (G.mem_neighborFinset ..).mp (en ▸ mem_insert_of_mem (mem_singleton_self _))
  refine ⟨e,a,b,de,ab,en,?_⟩
  ext x; rw [mem_inter,mem_singleton]; constructor
  · rintro ⟨xa,xb⟩
    apply Classical.byContradiction; intro ne
    apply off x
    refine ⟨de,Ne.symm ne,?_⟩
    rw [en]
    exact insert_subset ((G.mem_neighborFinset ..).mpr ((G.mem_neighborFinset ..).mp xa).symm)
      (singleton_subset_iff.mpr ((G.mem_neighborFinset ..).mpr ((G.mem_neighborFinset ..).mp xb).symm))
  · rintro rfl; exact ⟨(G.mem_neighborFinset ..).mpr ea.symm,(G.mem_neighborFinset ..).mpr eb.symm⟩

private theorem many {e : V} (de : G.degree e=2) {C : Finset V} (cl : G.IsNClique 4 C)
    (sub : G.neighborFinset e⊆C) : ∃ x y,x≠y ∧ Opposite G e x ∧ Opposite G e y := by
  have out : e∉C := by
    intro ec
    have inc : C.erase e⊆G.neighborFinset e := fun u um => (G.mem_neighborFinset ..).mpr
      (cl.1 ec (mem_erase.mp um).2 (mem_erase.mp um).1.symm)
    have cap := card_le_card inc
    rw [card_erase_of_mem ec,cl.2,card_neighborFinset_eq_degree,de] at cap; omega
  have size : (C\G.neighborFinset e).card=2 := by rw [card_sdiff sub,cl.2,card_neighborFinset_eq_degree,de]
  obtain ⟨x,xm,y,ym,ne⟩ := one_lt_card.mp (by omega : 1<(C\G.neighborFinset e).card)
  have sq (i : V) (im : i∈C\G.neighborFinset e) : Opposite G e i := by
    obtain ⟨ic,ine⟩ := mem_sdiff.mp im
    exact ⟨de,fun eq => out (eq ▸ ic),fun j jm => (G.mem_neighborFinset ..).mpr
      (cl.1 ic (sub jm) (fun eq => ine (eq ▸ jm)))⟩
  exact ⟨x,y,ne,sq x xm,sq y ym⟩

/-- Two low vertices can use different four-cliques to supply alternative
four-cycles. No intersection or disjointness of the cliques is required. -/
theorem two_cliques {e f : V} (ef : e≠f) (de : G.degree e=2) (df : G.degree f=2)
    {C D : Finset V} (cc : G.IsNClique 4 C) (dc : G.IsNClique 4 D)
    (es : G.neighborFinset e⊆C) (fs : G.neighborFinset f⊆D) : gamma G≤bound G := by
  apply Nat.le_of_not_gt; intro bad
  obtain ⟨x,x',ne,s,s'⟩ := many G de cc es
  obtain ⟨y,y',nf,v,v'⟩ := many G df dc fs
  obtain ⟨_,_,_,_,_,_,_,_,one|one⟩ := rigid_pair G (sparse G bad) ef s v
  · exact ne ((one x s).trans (one x' s').symm)
  · exact nf ((one y v).trans (one y' v').symm)

/-- If one color of another ear's frame misses both anchors, the other color
must contain every possible fourth vertex of this ear's four-cycles. -/
theorem barrier (sp : Sparse G) {e f : V} (ne : e≠f) (df : G.degree f=2)
    {A B : Finset V} (fr : Frame G A B) (fm : f∈A∪B) (off : Disjoint (G.neighborFinset e) B)
    {x : V} (sq : Opposite G e x) : x∈A := by
  classical
  apply Classical.byContradiction; intro xa
  have en : e∉A := fun z => ne (sp _ _ fr e (mem_union_left _ z) f fm sq.1 df)
  have ap : Disjoint A ({e,x}:Finset V) := disjoint_left.mpr (by
    intro j jm m; rcases mem_insert.mp m with eq|eq
    · exact en (eq ▸ jm)
    · exact xa ((mem_singleton.mp eq) ▸ jm))
  have old := frame G sq
  have swapped : Frame G (G.neighborFinset e) {e,x} := ⟨old.1.symm,old.2.2,old.2.1⟩
  have both := Squares29.merge G fr swapped ap off.symm
  apply ne (sp _ _ both e (mem_union_right _ (mem_union_right _ (mem_insert_self ..))) f ?_ sq.1 df)
  exact (mem_union.mp fm).elim (fun z => mem_union_left _ (mem_union_left _ z))
    (fun z => mem_union_right _ (mem_union_left _ z))

/-- If a five-clique contains the two anchors of e, every protected frame for
a different degree-two vertex, with at most three pins of either color, has
one anchor on each side. This includes alternate colorings of six-cycles. -/
theorem five_splits (sp : Sparse G) {e f : V} (ne : e≠f) (de : G.degree e=2) (df : G.degree f=2)
    {C A B : Finset V} (cl : G.IsNClique 5 C) (sub : G.neighborFinset e⊆C)
    (fr : Frame G A B) (fm : f∈A∪B) (sa : A.card≤3) (sb : B.card≤3) :
    (G.neighborFinset e∩A).Nonempty ∧ (G.neighborFinset e∩B).Nonempty := by
  classical
  let W := C\G.neighborFinset e
  have sz : W.card=3 := by dsimp [W]; rw [card_sdiff sub,cl.2,card_neighborFinset_eq_degree,de]
  have out : e∉C := by
    intro ec
    have inc : C.erase e⊆G.neighborFinset e := fun u um => (G.mem_neighborFinset ..).mpr
      (cl.1 ec (mem_erase.mp um).2 (mem_erase.mp um).1.symm)
    have cap := card_le_card inc
    rw [card_erase_of_mem ec,cl.2,card_neighborFinset_eq_degree,de] at cap; omega
  have sq (i : V) (im : i∈W) : Opposite G e i := by
    obtain ⟨ic,ine⟩ := mem_sdiff.mp im
    exact ⟨de,fun eq => out (eq ▸ ic),fun j jm => (G.mem_neighborFinset ..).mpr
      (cl.1 ic (sub jm) (fun eq => ine (eq ▸ jm)))⟩
  have hit {P Q : Finset V} (pq : Frame G P Q) (fmem : f∈P∪Q) (ps : P.card≤3) :
      (G.neighborFinset e∩Q).Nonempty := by
    apply Classical.byContradiction; intro none
    have no : Disjoint (G.neighborFinset e) Q := disjoint_left.mpr (fun i iN iQ => none ⟨i,mem_inter.mpr ⟨iN,iQ⟩⟩)
    have wp : W⊆P := fun i im => barrier G sp ne df pq fmem no (sq i im)
    have eq := eq_of_subset_of_card_le wp (by omega)
    have np : Disjoint (G.neighborFinset e) P := disjoint_left.mpr (fun _ im ip => (mem_sdiff.mp (eq.symm ▸ ip : _∈W)).2 im)
    obtain ⟨i,im⟩ := card_pos.mp (by omega : 0<W.card)
    have iq := barrier G sp ne df (show Frame G Q P from ⟨pq.1.symm,pq.2.2,pq.2.1⟩) (union_comm P Q ▸ fmem) np (sq i im)
    exact disjoint_left.mp pq.1 (wp im) iq
  exact ⟨hit ⟨fr.1.symm,fr.2.2,fr.2.1⟩ (union_comm A B ▸ fm) sb,hit fr fm sa⟩

/-- Graffiti.pc #384b holds at every diversity if three distinct degree-two
vertices lie on four-cycles. The four-cycles may overlap in any way. -/
theorem exact_three {e f g x y z : V} (ef : e≠f) (eg : e≠g) (fg : f≠g)
    (s : Opposite G e x) (v : Opposite G f y) (w : Opposite G g z) : gamma G≤bound G :=
  Nat.le_of_not_gt (fun bad => triple G (sparse G bad) ef eg fg s v w)

end Graffiti384b.Squares29
#print axioms Graffiti384b.Squares29.rigid_pair
#print axioms Graffiti384b.Squares29.triple
#print axioms Graffiti384b.Squares29.thin_at_32
#print axioms Graffiti384b.Squares29.two_cliques
#print axioms Graffiti384b.Squares29.barrier
#print axioms Graffiti384b.Squares29.five_splits
#print axioms Graffiti384b.Squares29.exact_three
namespace Graffiti384b.Squares29.Example
open Finset SimpleGraph EarFrame33
open private EarFixture33.gamma_of_test from EarFixture33

def neighbors : Fin 5 → Finset (Fin 5)
  | 0 => {1,2,3,4}
  | 1 => {0,2,3}
  | 2 => {0,1,4}
  | 3 => {0,1}
  | 4 => {0,2}

def graph : SimpleGraph (Fin 5) where
  Adj u v := v∈neighbors u
  symm := by
    have s : ∀ u v : Fin 5,v∈neighbors u → u∈neighbors v := by decide
    exact fun i j => s i j
  loopless := by change ∀ i : Fin 5,i∉neighbors i; decide

instance : DecidableRel graph.Adj := fun i j => inferInstanceAs (Decidable (j∈neighbors i))

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- Both degree-two vertices lie on four-cycles, but no frame protects both.
The five-vertex graph attains equality in the catalogue bound. -/
theorem sharp_two : Opposite graph 3 2 ∧ Opposite graph 4 1 ∧ Sparse graph ∧
    List.ofFn (trianglesAt graph)=[3,2,2,1,1] ∧ gamma graph=3 ∧ bound graph=3 := by
  refine ⟨?_,?_,?_,by decide,?_,by decide⟩
  · unfold Opposite; decide
  · unfold Opposite; decide
  · unfold Sparse Frame; decide
  · apply EarFixture33.gamma_of_test; unfold TwoDominates; decide

end Graffiti384b.Squares29.Example
#print axioms Graffiti384b.Squares29.Example.sharp_two
