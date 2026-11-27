import ComponentPorts180

set_option warningAsError true
namespace Minimal180.PairRepair
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution Transversals
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A whole connected, balanced remainder component that sees the center
supplies an odd-cycle obstruction through the center. -/
theorem mixed_of_balance (G : SimpleGraph V) (a b : V) (c : V→Bool) (C : Finset V)
    (rig : G.degree a=4 ∧ ∀ d : V→Bool,ProperOn G (univ\{a,b}) d → ∀ t,(sideNeighbors G a d t).card=2)
    (cp : ProperOn G (univ\{a,b}) c) (closed : ClosedIn G (univ\{a,b}) C)
    (con : ∀ x∈C,∀ y∈C,Joined G C x y) (hit : ∃ x∈C,G.Adj a x) : MixedAt G a C c := by
  classical
  obtain ⟨v,vm,ed⟩ := hit
  have nz := card_pos.mpr (show (G.neighborFinset a∩C).Nonempty from
    ⟨v,mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr ed,vm⟩⟩)
  obtain ⟨eq,twice⟩ := component_balance G a b rig C closed c cp
  obtain ⟨x,xm⟩ := card_pos.mp (show 0<(sideNeighbors G a c true∩C).card by omega)
  obtain ⟨y,ym⟩ := card_pos.mp (show 0<(sideNeighbors G a c false∩C).card by omega)
  obtain ⟨xhit,xc⟩ := mem_inter.mp xm
  obtain ⟨yhit,yc⟩ := mem_inter.mp ym
  exact ⟨x,y,(G.mem_neighborFinset _ _).mp (mem_filter.mp xhit).1,(G.mem_neighborFinset _ _).mp (mem_filter.mp yhit).1,
    (mem_filter.mp xhit).2,(mem_filter.mp yhit).2,con x xc y yc⟩

/-- Any budget-two repair keeping the center spends exactly one deletion
in each of two disjoint odd-cycle witnesses away from the center. -/
theorem forced_two_deletions (G : SimpleGraph V) (a : V) (C D Z : Finset V) (apart : Disjoint C D)
    (first : ¬TwoColor G (insert a C)) (second : ¬TwoColor G (insert a D))
    (col : TwoColor G Z) (az : a∈Z) (cap : Fintype.card V-Z.card≤2) :
    ∃ x∈C,∃ y∈D,univ\Z={x,y} := by
  classical
  have hit (E : Finset V) (non : ¬TwoColor G (insert a E)) : ∃ x∈E,x∉Z := by
    by_contra! all
    obtain ⟨c,proper⟩ := (color_function ..).mp col
    have inclusion := insert_subset az all
    exact non ((color_function ..).mpr ⟨c,fun x xm y ym => proper x (inclusion xm) y (inclusion ym)⟩)
  obtain ⟨x,xc,xz⟩ := hit C first
  obtain ⟨y,yd,yz⟩ := hit D second
  have ne : x≠y := fun eq => disjoint_left.mp apart xc (eq ▸ yd)
  have sub : ({x,y}:Finset V)⊆univ\Z := insert_subset (mem_sdiff.mpr ⟨mem_univ _,xz⟩)
    (singleton_subset_iff.mpr (mem_sdiff.mpr ⟨mem_univ _,yz⟩))
  have count := card_sdiff_add_card_eq_card (subset_univ Z)
  rw [card_univ] at count
  exact ⟨x,xc,y,yd,(eq_of_subset_of_card_le sub (by rw [card_pair ne];omega)).symm⟩

/-- Exact test when two disjoint obstructions through a exhaust the
budget. Both terminals are retained. Normalize the center to true.
The three component regions then share only one Boolean parameter. -/
theorem two_region_iff (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (r : V) (p : Bool) (A : Finset V) (ai : Indep G A) (a b : V) (ak : a∈A∩insert r (parity G r p))
    (C D O : Finset V) (partition : univ\({a,b}:Finset V)=(C∪D)∪O)
    (apart : Disjoint C D) (other : Disjoint (C∪D) O)
    (cross : ∀ x∈C,∀ y∈D,¬G.Adj x y) (out : ∀ x∈C∪D,∀ y∈O,¬G.Adj x y)
    (first : ¬TwoColor G (insert a C)) (second : ¬TwoColor G (insert a D))
    (two : allowance G r p A=2) :
    Protected G r p A ↔ ∃ t : Bool,
      (∃ x∈C,x∉A∩insert r (parity G r p) ∧ TerminalColor G a b (C.erase x) t) ∧
      (∃ y∈D,y∉A∩insert r (parity G r p) ∧ TerminalColor G a b (D.erase y) t) ∧ TerminalColor G a b O t := by
  classical
  let K := A∩insert r (parity G r p)
  let X : Finset V := {a,b}
  have dirs (x : V) (xc : x∈C) (y : V) (yd : y∈D) :
      ∀ w,(w∈univ\({x,y}:Finset V)) ↔ w∈X∪((C.erase x∪D.erase y)∪O) := by
    intro w
    have cover := Finset.ext_iff.mp partition w
    have sepc := disjoint_left.mp apart
    have sepo := disjoint_left.mp other
    have ex1 : w∈C → w∉D := fun h => sepc h
    have ex2 : w∈C → w∉O := fun h => sepo (mem_union_left _ h)
    have ex3 : w∈D → w∉O := fun h => sepo (mem_union_right _ h)
    have wx : w=x → w∈C := fun eq => eq ▸ xc
    have wy : w=y → w∈D := fun eq => eq ▸ yd
    change (w∈univ\({x,y}:Finset V)) ↔ w∈({a,b}:Finset V)∪((C.erase x∪D.erase y)∪O)
    simp only [mem_sdiff,mem_univ,true_and,mem_insert,mem_singleton,mem_union,mem_erase] at cover ⊢
    by_cases eq : w=x
    · have wc := wx eq
      have nd := ex1 wc
      have no := ex2 wc
      simp_all only [true_or,not_true_eq_false,or_true,or_false,false_or,and_false,false_and,not_false_eq_true,
        and_true,true_and,ne_eq]
      tauto
    by_cases e : w=y
    · have wd := wy e
      have nc : w∉C := fun wc => ex1 wc wd
      have no := ex3 wd
      simp_all only [true_or,not_true_eq_false,or_true,or_false,false_or,and_false,false_and,not_false_eq_true,
        and_true,true_and,ne_eq]
      tauto
    have miss : ¬(w=x ∨ w=y) := not_or.mpr ⟨eq,e⟩
    by_cases tip : w=a ∨ w=b
    · exact ⟨fun _ => Or.inl tip,fun _ => miss⟩
    · have rest := cover.mp tip
      simp [eq,e,tip,rest]
  have localize (x y : V) (t : Bool) :
      TerminalColor G a b ((C.erase x∪D.erase y)∪O) t ↔
      (TerminalColor G a b (C.erase x) t ∧ TerminalColor G a b (D.erase y) t) ∧ TerminalColor G a b O t := by
    have sub : C.erase x∪D.erase y⊆C∪D := union_subset_union (erase_subset ..) (erase_subset ..)
    rw [terminal_union G a b _ O t (other.mono_left sub) (fun u um => out u (sub um))]
    rw [terminal_union G a b _ _ t (apart.mono (erase_subset ..) (erase_subset ..))
      (fun u um v vm => cross u (mem_of_mem_erase um) v (mem_of_mem_erase vm))]
  rw [protected_iff G gc hn r p A ai]
  constructor
  · rintro ⟨Z,col,keep,budget⟩
    obtain ⟨x,xc,y,yd,del⟩ := forced_two_deletions G a C D Z apart first second col (keep ak) (two ▸ budget)
    have exactZ : univ\({x,y}:Finset V)=Z := by rw [←del,Finset.sdiff_sdiff_eq_self (subset_univ Z)]
    have form : Z=X∪((C.erase x∪D.erase y)∪O) := exactZ ▸ Finset.ext (dirs x xc y yd)
    obtain ⟨e,proper⟩ := (color_function ..).mp col
    have norm : TerminalColor G a b ((C.erase x∪D.erase y)∪O) (e b==e a) := by
      refine ⟨fun v => e v==e a,?_,by simp,rfl⟩
      intro u um v vm ed
      have diff := proper u (form.symm ▸ um) v (form.symm ▸ vm) ed
      cases hu : e u <;> cases hv : e v <;> cases ha : e a <;> simp_all
    obtain ⟨⟨lc,rc⟩,oc⟩ := (localize x y _).mp norm
    have free (z : V) (zm : z∈({x,y}:Finset V)) : z∉K := fun zk =>
      (mem_sdiff.mp (show z∈univ\Z from del ▸ zm)).2 (keep zk)
    exact ⟨_,⟨x,xc,free x (mem_insert_self ..),lc⟩,⟨y,yd,free y (mem_insert_of_mem (mem_singleton_self _)),rc⟩,oc⟩
  · rintro ⟨t,⟨x,xc,xk,lc⟩,⟨y,yd,yk,rc⟩,oc⟩
    obtain ⟨e,ok,_,_⟩ := (localize x y t).mpr ⟨⟨lc,rc⟩,oc⟩
    have orig : TwoColor G (univ\({x,y}:Finset V)) :=
      (color_function ..).mpr ⟨e,fun u um v vm => ok u ((dirs x xc y yd u).mp um) v ((dirs x xc y yd v).mp vm)⟩
    have ne : x≠y := fun eq => disjoint_left.mp apart xc (eq ▸ yd)
    have charge := card_sdiff_add_card_eq_card (subset_univ ({x,y}:Finset V))
    rw [card_pair ne,card_univ] at charge
    refine ⟨_,orig,fun w wk => mem_sdiff.mpr ⟨mem_univ _,?_⟩,by omega⟩
    intro wm
    rcases mem_insert.mp wm with eq|inY
    · exact xk (eq ▸ wk)
    · exact yk ((mem_singleton.mp inY) ▸ wk)

#print axioms mixed_of_balance
#print axioms forced_two_deletions
#print axioms two_region_iff
end Minimal180.PairRepair
