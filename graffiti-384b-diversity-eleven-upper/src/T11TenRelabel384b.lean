import T11TenGraph384b

namespace Graffiti384b.T11TenNormalize
open Finset SimpleGraph
set_option maxHeartbeats 3000000

private def color (i : Label) : Fin 4 :=
  if i=0 then 0 else if i=4 then 1 else if i∈clique then 2 else 3

private theorem color_zero : ∀ i, color i=0 ↔ i=0 := by decide
private theorem color_four : ∀ i, color i=1 ↔ i=4 := by decide
private theorem color_clique : ∀ i, color i=2 ↔ i∈clique := by decide

private theorem swap_color {i j : Label} (h : color i = color j) (k : Label) :
    color (Equiv.swap i j k) = color k := by
  by_cases a : k=i
  · subst k; rw [Equiv.swap_apply_left]; exact h.symm
  by_cases b : k=j
  · subst k; rw [Equiv.swap_apply_right]; exact h
  rw [Equiv.swap_apply_of_ne_of_ne a b]

private theorem place3 {i j k a b c : Label}
    (ij : i≠j) (ik : i≠k) (jk : j≠k) (ab : a≠b) (ac : a≠c) (bc : b≠c)
    (ia : color i = color a) (jb : color j=color b) (kc : color k=color c) :
    ∃ e : Label ≃ Label, e i=a ∧ e j=b ∧ e k=c ∧ ∀ w, color (e w)=color w := by
  let f := Equiv.swap i a
  have fi : f i=a := Equiv.swap_apply_left _ _
  have fc (w : Label) : color (f w)=color w := swap_color ia w
  let B := f.symm b
  have fB : f B = b := f.apply_symm_apply b
  have nB : i ≠ B := fun h => ab (fi.symm.trans ((congrArg f h).trans fB))
  have BJ : color j = color B := jb.trans ((congrArg color fB).symm.trans (fc B))
  let g := (Equiv.swap j B).trans f
  have gi : g i=a := by
    change f (Equiv.swap j B i)=a
    rw [Equiv.swap_apply_of_ne_of_ne ij nB,fi]
  have gj : g j=b := by
    change f (Equiv.swap j B j)=b
    rw [Equiv.swap_apply_left,fB]
  have gc (w : Label) : color (g w)=color w := (fc _).trans (swap_color BJ w)
  let C := g.symm c
  have gC : g C = c := g.apply_symm_apply c
  have nCi : i ≠ C := fun h => ac (gi.symm.trans ((congrArg g h).trans gC))
  have nCj : j ≠ C := fun h => bc (gj.symm.trans ((congrArg g h).trans gC))
  have CK : color k = color C := kc.trans ((congrArg color gC).symm.trans (gc C))
  let e := (Equiv.swap k C).trans g
  refine ⟨e,?_,?_,?_,fun w => (gc _).trans (swap_color CK w)⟩
  · change g (Equiv.swap k C i)=a
    rw [Equiv.swap_apply_of_ne_of_ne ik nCi,gi]
  · change g (Equiv.swap k C j)=b
    rw [Equiv.swap_apply_of_ne_of_ne jk nCj,gj]
  · change g (Equiv.swap k C k)=c
    rw [Equiv.swap_apply_left,gC]

private def dA (k : Fin 4) : Label := (![5,1,5,1] : Fin 4→Label) k
private def dB (k : Fin 4) : Label := (![6,5,6,5] : Fin 4→Label) k
private def dC (k : Fin 4) : Label := (![7,6,1,2] : Fin 4→Label) k
private theorem dSpec : ∀ k, dA k≠dB k ∧ dA k≠dC k ∧ dB k≠dC k ∧
    diamond k = {dA k,dB k,dC k} ∧ missing k = {dA k,dB k} := by decide

private theorem shapes_for_colors {a b c : Label}
    (a0 : a≠0) (a4 : a≠4) (b0 : b≠0) (b4 : b≠4) (c0 : c≠0) (c4 : c≠4)
    (h : ¬(a∈clique ∧ b∈clique)) :
    ∃ k, ((color (dA k)=color a ∧ color (dB k)=color b) ∨
      (color (dA k)=color b ∧ color (dB k)=color a)) ∧ color (dC k)=color c := by
  by_cases aa : a∈clique <;> by_cases bb : b∈clique <;> by_cases cc : c∈clique
  · exact False.elim (h ⟨aa,bb⟩)
  · exact False.elim (h ⟨aa,bb⟩)
  · refine ⟨3,Or.inl ⟨?_,?_⟩,?_⟩ <;> simp only [color,a0,a4,b0,b4,c0,c4,aa,bb,cc,if_true,if_false] <;> rfl
  · refine ⟨1,Or.inl ⟨?_,?_⟩,?_⟩ <;> simp only [color,a0,a4,b0,b4,c0,c4,aa,bb,cc,if_true,if_false] <;> rfl
  · refine ⟨3,Or.inr ⟨?_,?_⟩,?_⟩ <;> simp only [color,a0,a4,b0,b4,c0,c4,aa,bb,cc,if_true,if_false] <;> rfl
  · refine ⟨1,Or.inr ⟨?_,?_⟩,?_⟩ <;> simp only [color,a0,a4,b0,b4,c0,c4,aa,bb,cc,if_true,if_false] <;> rfl
  · refine ⟨2,Or.inl ⟨?_,?_⟩,?_⟩ <;> simp only [color,a0,a4,b0,b4,c0,c4,aa,bb,cc,if_true,if_false] <;> rfl
  · refine ⟨0,Or.inl ⟨?_,?_⟩,?_⟩ <;> simp only [color,a0,a4,b0,b4,c0,c4,aa,bb,cc,if_true,if_false] <;> rfl

private theorem relabel_diamond {a b c : Label}
    (ab : a≠b) (ac : a≠c) (bc : b≠c)
    (a0 : a≠0) (a4 : a≠4) (b0 : b≠0) (b4 : b≠4) (c0 : c≠0) (c4 : c≠4)
    (h : ¬(a∈clique ∧ b∈clique)) :
    ∃ (k : Fin 4) (e : Label ≃ Label), e 0=0 ∧ e 4=4 ∧
      (∀ i, e i∈clique ↔ i∈clique) ∧
      (diamond k).map e.toEmbedding={a,b,c} ∧ (missing k).map e.toEmbedding={a,b} ∧
      e (dC k)=c := by
  obtain ⟨k,first,last⟩ := shapes_for_colors a0 a4 b0 b4 c0 c4 h
  obtain ⟨de,df,ef,hd,hm⟩ := dSpec k
  have sw : ∃ e : Label ≃ Label,
      ((e (dA k)=a ∧ e (dB k)=b) ∨ (e (dA k)=b ∧ e (dB k)=a)) ∧
      e (dC k)=c ∧ (∀ w,color (e w)=color w) := by
    rcases first with ⟨ca,cb⟩|⟨cb,ca⟩
    · obtain ⟨e,ha,hb,hc,cp⟩ := place3 de df ef ab ac bc ca cb last
      exact ⟨e,Or.inl ⟨ha,hb⟩,hc,cp⟩
    · obtain ⟨e,hb,ha,hc,cp⟩ := place3 de df ef ab.symm bc ac cb ca last
      exact ⟨e,Or.inr ⟨hb,ha⟩,hc,cp⟩
  obtain ⟨e,he,hc,cp⟩ := sw
  refine ⟨k,e,(color_zero _).mp ((cp 0).trans (by decide)),
    (color_four _).mp ((cp 4).trans (by decide)),fun i => by rw [← color_clique,← color_clique,cp],
    ?_,?_,hc⟩
  · rw [hd]
    simp only [Finset.map_insert,Finset.map_singleton,Equiv.toEmbedding_apply,hc]
    rcases he with ⟨ha,hb⟩|⟨hb,ha⟩
    · rw [ha,hb]
    · rw [ha,hb]; ext i; simp only [mem_insert,mem_singleton]; tauto
  · rw [hm]
    simp only [Finset.map_insert,Finset.map_singleton,Equiv.toEmbedding_apply]
    rcases he with ⟨ha,hb⟩|⟨hb,ha⟩
    · rw [ha,hb]
    · rw [ha,hb]; ext i; simp only [mem_insert,mem_singleton]; tauto

private theorem diamond_local (G : SimpleGraph Label) (a b c x y : Label)
    (ab : a≠b) (ac : a≠c) (bc : b≠c) (nab : ¬G.Adj a b) (ea : G.Adj a c) (eb : G.Adj b c)
    (hx : x∈({a,b,c}:Finset Label)) (hy : y∈({a,b,c}:Finset Label)) (xy : x≠y) :
    G.Adj x y ↔ ({x,y}:Finset Label) ≠ {a,b} := by
  have pa : ({a,c} : Finset Label) ≠ {a,b} := by
    intro h; have : c∈({a,b} : Finset Label) := h ▸ (by simp : c∈({a,c} : Finset Label))
    simp [ac.symm,bc.symm] at this
  have pb : ({b,c} : Finset Label) ≠ {a,b} := by
    intro h; have : c∈({a,b} : Finset Label) := h ▸ (by simp : c∈({b,c} : Finset Label))
    simp [ac.symm,bc.symm] at this
  simp only [mem_insert,mem_singleton] at hx hy
  rcases hx with rfl|rfl|rfl <;> rcases hy with rfl|rfl|rfl
  · exact (xy rfl).elim
  · simp [nab]
  · simp [ea,pa]
  · rw [Finset.pair_comm]; exact iff_of_false (fun h => nab h.symm) (fun h => h rfl)
  · exact (xy rfl).elim
  · simp [eb,pb]
  · rw [Finset.pair_comm]; exact iff_of_true ea.symm pa
  · rw [Finset.pair_comm]; exact iff_of_true eb.symm pb
  · exact (xy rfl).elim

theorem normalize_motif (G : SimpleGraph Label) [DecidableRel G.Adj]
    (u v : Label) (uv : u≠v) (sep : ¬G.Adj u v)
    (du : G.degree u=3) (su : trianglesAt G u=2) (dv : G.degree v=3) (sv : trianglesAt G v=3) :
    ∃ (k : Fin 4) (p : Label ≃ Label), p 0=v ∧ p 4=u ∧
      (∀ i, G.Adj v (p i) ↔ i∈clique) ∧ (∀ i, G.Adj u (p i) ↔ i∈diamond k) ∧
      ∀ i j b, motif k i j=some b → (G.Adj (p i) (p j) ↔ b=true) := by
  obtain ⟨p,pv,pu,cp⟩ := label_clique G u v uv sep dv
  obtain ⟨a,b,c,ab,ac,bc,nu,nab,ea,eb⟩ := cubic_two_shape G u du su
  have avail (z : Label) (hz : z∈({a,b,c}:Finset Label)) :
      p.symm z ≠ 0 ∧ p.symm z ≠ 4 := by
    have uz : G.Adj u z := (G.mem_neighborFinset u z).mp (nu.symm ▸ hz)
    constructor
    · intro h; have eq := p.apply_symm_apply z; rw [h,pv] at eq; exact sep (eq.symm ▸ uz)
    · intro h; have eq := p.apply_symm_apply z; rw [h,pu] at eq; exact uz.ne eq
  have avA := avail a (by simp)
  have avB := avail b (by simp)
  have avC := avail c (by simp)
  have bad : ¬(p.symm a∈clique ∧ p.symm b∈clique) := by
    intro h
    have va := (cp _).mpr h.1
    have vb := (cp _).mpr h.2
    rw [p.apply_symm_apply] at va vb
    exact nab (full_neighbors G dv sv va vb ab)
  obtain ⟨k,e,e0,e4,eqc,targets,miss,_⟩ := relabel_diamond
    (fun q => ab (p.symm.injective q)) (fun q => ac (p.symm.injective q))
    (fun q => bc (p.symm.injective q)) avA.1 avA.2 avB.1 avB.2 avC.1 avC.2 bad
  let q := e.trans p
  have qv : q 0=v := by change p (e 0)=v; rw [e0,pv]
  have qu : q 4=u := by change p (e 4)=u; rw [e4,pu]
  have qClique (i : Label) : G.Adj v (q i) ↔ i∈clique := (cp (e i)).trans (eqc i)
  have tar : (diamond k).map q.toEmbedding = {a,b,c} := by
    change (diamond k).map (e.toEmbedding.trans p.toEmbedding) = _
    rw [←Finset.map_map,targets]
    simp
  have miss' : (missing k).map q.toEmbedding = {a,b} := by
    change (missing k).map (e.toEmbedding.trans p.toEmbedding) = _
    rw [←Finset.map_map,miss]
    simp
  have qDiamond (i : Label) : G.Adj u (q i) ↔ i∈diamond k := by
    rw [← G.mem_neighborFinset,nu,←tar]
    exact Finset.mem_map' q.toEmbedding
  refine ⟨k,q,qv,qu,qClique,qDiamond,?_⟩
  intro i j B h
  unfold motif at h
  split at h
  · rename_i hij
    subst j
    cases h
    exact iff_of_false (G.loopless _) (by decide)
  · rename_i ij
    split at h
    · rename_i root; subst i; cases h; rw [qv,qClique]; simp
    split at h
    · rename_i root; subst j; cases h; rw [qv,G.adj_comm,qClique]; simp
    split at h
    · rename_i root; subst i; cases h; rw [qu,qDiamond]; simp
    split at h
    · rename_i root; subst j; cases h; rw [qu,G.adj_comm,qDiamond]; simp
    split at h
    · rename_i both; cases h
      exact iff_of_true (full_neighbors G dv sv
        ((qClique _).mpr both.1) ((qClique _).mpr both.2) (fun ne => ij (q.injective ne))) rfl
    split at h
    · rename_i both; cases h
      have hi : q i ∈ (diamond k).map q.toEmbedding := Finset.mem_map.mpr ⟨i,both.1,rfl⟩
      have hj : q j ∈ (diamond k).map q.toEmbedding := Finset.mem_map.mpr ⟨j,both.2,rfl⟩
      rw [tar] at hi hj
      have C := diamond_local G a b c (q i) (q j) ab ac bc nab ea eb hi hj
        (fun eq => ij (q.injective eq))
      have eq : ({i,j} : Finset Label) ≠ missing k ↔ ({q i,q j} : Finset Label) ≠ {a,b} := by
        have hmap : ({i,j} : Finset Label).map q.toEmbedding = {q i,q j} := by simp
        rw [←miss',←hmap]
        exact not_congr ((Finset.map_injective q.toEmbedding).eq_iff).symm
      exact C.trans (by rw [decide_eq_true_eq,eq])
    · simp at h

end Graffiti384b.T11TenNormalize
#print axioms Graffiti384b.T11TenNormalize.normalize_motif
