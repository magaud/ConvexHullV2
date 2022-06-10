(* ================================ *)
(* ========= CH06_CHID.v ========== *)
(* ================================ *)

Require Export CH05_m1m6.

(* ================================ *)
(* ========== ########## ========== *)
(* ================================ *)

Definition prec_CHID (m:fmap)(d:dart)(x:dart)(t:tag)(p:point)(max:dart) :=
  inv_hmap m /\ inv_gmap m /\ inv_poly m d /\ planar m /\
  is_well_emb m /\ is_neq_point m /\ is_noalign m /\ is_convex m d /\
  exd m d /\ ~ exd m x /\ ~ exd m max /\ x <> nil /\ max <> nil /\ x <> max /\
  (forall (da:dart), exd m da -> fpoint m da <> p) /\
  (forall (da:dart)(db:dart), let pda := fpoint m da in let pdb := fpoint m db in
  exd m da -> exd m db -> pda <> pdb -> ~ align p pda pdb) /\
  ~ expf m d (cA m zero d).

(* ================================ *)

Lemma inv_hmap_CHID :
  forall (md:mapdart)(x:dart)(t:tag)(p:point)(max:dart),
  let m := (fst md) in let d := (snd md) in prec_CHID m d x t p max ->
  inv_hmap (fst (CHID md x t p max)).
Proof.
intros md x t p max m d.
intros [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 H10]]]]]]]]].
destruct H10 as [H11 [H12 [H13 [H14 [H15 [H16 [H17 H18]]]]]]].
unfold CHID; elim eq_dart_dec; intro hl.
(* search_left m d p 0 = nil *)
simpl; unfold prec_I; repeat split; assumption.
(* search_left m d p 0 <> nil *)
apply inv_hmap_m6; assumption.
Qed.

Lemma inv_gmap_CHID :
  forall (md:mapdart)(x:dart)(t:tag)(p:point)(max:dart),
  let m := (fst md) in let d := (snd md) in prec_CHID m d x t p max ->
  inv_gmap (fst (CHID md x t p max)).
Proof.
intros md x t p max m d.
intros [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 H10]]]]]]]]].
destruct H10 as [H11 [H12 [H13 [H14 [H15 [H16 [H17 H18]]]]]]].
unfold CHID; elim eq_dart_dec; intro hl.
(* search_left m d p 0 = nil *)
simpl; fold m; unfold inv_gmap.
intros k x0 Hx0; simpl in *.
elimination Hx0.
subst x0; eqdartdec; trivial.
elim (eq_dart_dec x x0); intro h.
subst x0; eqdartdec; trivial.
elim eq_dart_dec; intro h0.
rewrite h0 in H11.
generalize (exd_cA_cA_1 m k x0 H1 Hx0).
intros [h2 h3]; contradiction.
apply H2; assumption.
(* search_left m d p 0 <> nil *)
apply inv_gmap_m6; assumption.
Qed.

Lemma inv_poly_CHID :
  forall (md:mapdart)(x:dart)(t:tag)(p:point)(max:dart),
  let m := (fst md) in let d := (snd md) in prec_CHID m d x t p max ->
  inv_poly (fst (CHID md x t p max)) (snd (CHID md x t p max)).
Proof.
intros md x t p max m d.
intros [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 H10]]]]]]]]].
destruct H10 as [H11 [H12 [H13 [H14 [H15 [H16 [H17 H18]]]]]]].
unfold CHID; fold m; fold d.
pose (l := (search_left m d p 0)); fold l.
pose (r := (search_right m l p 0)); fold r.
elim eq_dart_dec; intro H.
(* search_left m d p 0 = nil *)
simpl fst; simpl snd.
unfold inv_poly; intros k da H0.
elimination H0; simpl.
destruct H0 as [t1 t2].
rewrite t1 in H9; contradiction.
elim eq_dart_dec; intro h.
subst da; apply eqc_exd_exd in H0.
destruct H0 as [t1 t2]; contradiction.
apply H3; assumption.
(* search_left m d p 0 <> nil *)
apply inv_poly_m6; assumption.
Qed.

Lemma planar_CHID :
  forall (md:mapdart)(x:dart)(t:tag)(p:point)(max:dart),
  let m := (fst md) in let d := (snd md) in
  prec_CHID m d x t p max -> planar (fst (CHID md x t p max)).
Proof.
intros md x t p max m d.
intros [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 H10]]]]]]]]].
destruct H10 as [H11 [H12 [H13 [H14 [H15 [H16 [H17 H18]]]]]]].
unfold CHID; elim eq_dart_dec; intro hl; simpl fst.
(* search_left m d p 0 = nil *)
apply planar_I; try assumption. unfold prec_I; tauto.
(* search_left m d p 0 <> nil *)
apply planar_m6; assumption.
Qed.

Open Scope Z_scope.

Lemma nc_CHID :
  forall (md:mapdart)(x:dart)(t:tag)(p:point)(max:dart),
  let m := (fst md) in let d := (snd md) in 
  let l := (search_left m d p 0) in 
  let r := (search_right m l p 0) in 
  let l0 := (cA m zero l) in
  prec_CHID m d x t p max -> ~ expf m d (cA m zero d) ->
  nc (fst (CHID md x t p max)) = 
  if (eq_dart_dec l nil) then (nc m + 1) else
  if (eq_dart_dec l0 r) then (nc m) else (nc m + 1).
Proof.
intros md x t p max m d l r l0.
intros [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 H10]]]]]]]]].
destruct H10 as [H11 [H12 [H13 [H14 [H15 [H16 [H17 H18]]]]]]].
unfold CHID; fold m d l r l0; intro H0.
elim eq_dart_dec; intro h1. simpl; trivial.
simpl fst; unfold l0, r, l, d, m.
rewrite nc_m6; try assumption.
rewrite nc_m5; try assumption.
rewrite nc_m4; try assumption.
rewrite nc_m3; try assumption.
rewrite nc_m2; try assumption.
rewrite nc_m1; try assumption.
ring_simplify; trivial.
Qed.

Lemma nf_CHID :
  forall (md:mapdart)(x:dart)(t:tag)(p:point)(max:dart),
  let m := (fst md) in let d := (snd md) in
  let l := (search_left m d p 0) in 
  let r := (search_right m l p 0) in 
  let l0 := (cA m zero l) in
  prec_CHID m d x t p max -> ~ expf m d (cA m zero d) ->
  nf (fst (CHID md x t p max)) = 
  if (eq_dart_dec l nil) then (nf m + 1) else
  if (eq_dart_dec l0 r) then (nf m) else (nf m + 1).
Proof.
intros md x t p max m d l r l0.
intros [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 H10]]]]]]]]].
destruct H10 as [H11 [H12 [H13 [H14 [H15 [H16 [H17 H18]]]]]]].
unfold CHID; fold m d l r l0; intro H0.
elim eq_dart_dec; intro h1. simpl; trivial.
simpl fst; unfold l0, r, l, d, m.
rewrite nf_m6; try assumption.
rewrite nf_m5; try assumption.
rewrite nf_m4; try assumption.
rewrite nf_m3; try assumption.
rewrite nf_m2; try assumption.
rewrite nf_m1; try assumption.
elim eq_dart_dec; intro h2.
ring_simplify; trivial.
ring_simplify; trivial.
Qed.

Open Scope nat_scope.

Lemma is_well_emb_CHID :
  forall (md:mapdart)(x:dart)(t:tag)(p:point)(max:dart),
  let m := (fst md) in let d := (snd md) in prec_CHID m d x t p max ->
  is_well_emb (fst (CHID md x t p max)).
Proof.
intros md x t p max m d.
intros [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 H10]]]]]]]]].
destruct H10 as [H11 [H12 [H13 [H14 [H15 [H16 [H17 H18]]]]]]].
unfold CHID; elim eq_dart_dec; intro hl.
simpl fst; fold m; unfold is_well_emb.
intros da db h1 h2 h3; split; simpl.
(* expv *)
intro h4; simpl in h1, h2.
elimination h1. subst da.
elimination h2. contradiction.
assert False; [idtac|tauto].
apply expv_I in h4; try assumption.
elimination h4. tauto.
apply not_exd_not_expv with m x db; try assumption.
elimination h2. subst db.
assert False; [idtac|tauto].
apply expv_I in h4; try assumption.
elimination h4. destruct h4 as [t1 t2].
apply eq_sym in t1; contradiction.
apply not_exd_not_expv with m x da; try assumption.
apply expv_symm; assumption.
elim eq_dart_dec; intro t1.
subst da; contradiction.
elim eq_dart_dec; intro t2.
subst db; contradiction.
apply expv_I in h4; try assumption.
elimination h4. tauto.
generalize (H5 da db h1 h2 h3).
intros [t3 t4]; apply t3; assumption.
(* expe *)
intro h4; simpl in h1, h2.
elimination h1. subst da.
elimination h2. contradiction.
assert False; [idtac|tauto].
apply expe_I in h4; try assumption.
elimination h4. tauto.
apply not_exd_not_expe with m x db; try assumption.
elimination h2. subst db.
assert False; [idtac|tauto].
apply expe_I in h4; try assumption.
elimination h4. destruct h4 as [t1 t2].
apply eq_sym in t1; contradiction.
apply not_exd_not_expe with m x da; try assumption.
apply expe_symm; assumption.
elim eq_dart_dec; intro t1.
subst da; contradiction.
elim eq_dart_dec; intro t2.
subst db; contradiction.
apply expe_I in h4; try assumption.
elimination h4. tauto.
generalize (H5 da db h1 h2 h3).
intros [t3 t4]; apply t4; assumption.
(* well_emb m6 *)
apply is_well_emb_m6; assumption.
Qed.

Lemma is_neq_point_CHID :
  forall (md:mapdart)(x:dart)(t:tag)(p:point)(max:dart),
  let m := (fst md) in let d := (snd md) in prec_CHID m d x t p max ->
  is_neq_point (fst (CHID md x t p max)).
Proof.
intros md x t p max m d.
intros [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 H10]]]]]]]]].
destruct H10 as [H11 [H12 [H13 [H14 [H15 [H16 [H17 H18]]]]]]].
unfold CHID; elim eq_dart_dec; intro hl.
(* search_left m d p 0 = nil *)
simpl fst; fold m; unfold is_neq_point.
intros da db h1 h2 h3; simpl in *.
elimination h1. subst da.
elimination h2. subst db.
assert False; [idtac|tauto].
apply h3; apply expv_refl.
simpl; unfold prec_I; tauto.
simpl; left; trivial.
eqdartdec. elim eq_dart_dec; intro h.
intro h0; apply H11; subst db; assumption.
apply not_eq_sym; apply H16; assumption.
elimination h2. subst db.
eqdartdec. elim eq_dart_dec; intro h.
intro h0; apply H11; subst da; assumption.
apply H16; assumption.
elim eq_dart_dec; intro t1.
subst da; contradiction.
elim eq_dart_dec; intro t2.
subst db; contradiction.
apply H6; try assumption.
apply not_expv_I_not_expv in h3; assumption.
(* search_left m d p 0 <> nil *)
apply is_neq_point_m6; assumption.
Qed.

Lemma is_noalign_CHID :
  forall (md:mapdart)(x:dart)(t:tag)(p:point)(max:dart),
  let m := (fst md) in let d := (snd md) in prec_CHID m d x t p max ->
  is_noalign (fst (CHID md x t p max)).
Proof.
intros md x t p max m d.
intros [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 H10]]]]]]]]].
destruct H10 as [H11 [H12 [H13 [H14 [H15 [H16 [H17 H18]]]]]]].
unfold CHID; elim eq_dart_dec; intro hl.
(* search_left m d p 0 = nil *)
simpl fst; fold m; unfold is_noalign.
intros da db dc h1 h2 h3.
elimination h1. subst da.
elimination h2. subst db.
simpl; eqdartdec; tauto.
elimination h3. subst dc.
simpl; eqdartdec; tauto.
elim (eq_dart_dec x db); intro t1.
subst db; simpl; eqdartdec; tauto.
elim (eq_dart_dec x dc); intro t2.
subst dc; simpl; eqdartdec; tauto.
simpl; eqdartdec; intros h4 h5 h6.
apply H17; assumption.
elimination h2. subst db.
elimination h3. subst dc.
simpl; eqdartdec; tauto.
elim (eq_dart_dec x da); intro t1.
subst da; simpl; eqdartdec; tauto.
elim (eq_dart_dec x dc); intro t2.
subst dc; simpl; eqdartdec; tauto.
simpl; eqdartdec; intros h4 h5 h6.
generalize (H17 da dc h1 h3 h5).
auto with myorientation.
elimination h3. subst dc.
elim (eq_dart_dec x da); intro t1.
subst da; simpl; eqdartdec; tauto.
elim (eq_dart_dec x db); intro t2.
subst db; simpl; eqdartdec; tauto.
simpl; eqdartdec; intros h4 h5 h6.
generalize (H17 da db h1 h2 h4).
auto with myorientation.
elim (eq_dart_dec x da); intro t1.
subst da; contradiction.
elim (eq_dart_dec x db); intro t2.
subst db; contradiction.
elim (eq_dart_dec x dc); intro t3.
subst dc; contradiction.
simpl; eqdartdec; apply H7; assumption.
(* search_left m d p 0 <> nil *)
apply is_noalign_m6; assumption.
Qed.

(* ================================ *)

Lemma eq_point_eq :
  forall (p:point)(q:point),
  (eq_point p q) <-> (p = q).
Proof.
intros p q.
unfold eq_point; split.
induction p; induction q.
simpl; intros [H1 H2].
subst a b; trivial.
intro H1; subst p.
tauto.
Qed.

Lemma eq_point_dec_2 :
  forall (p:point)(q:point),
  {p = q} + {p <> q}.
Proof.
intros p q.
generalize (eq_point_eq p q).
intro H; destruct H as [H1 H2].
elim (eq_point_dec p q).
intro H; left; tauto.
intro H; right; tauto.
Qed.

Lemma neq_sym_point :
  forall (p:point)(q:point),
  (p <> q) -> (q <> p).
Proof.
intros p q.
auto with arith.
Qed.

(* ================================ *)

Lemma is_convex_CHID :
  forall (md:mapdart)(x:dart)(t:tag)(p:point)(max:dart),
  let m := (fst md) in let d := (snd md) in prec_CHID m d x t p max ->
  is_convex (fst (CHID md x t p max)) (snd (CHID md x t p max)).
Proof.
intros md x t p max m d.
intros [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 H10]]]]]]]]].
destruct H10 as [H11 [H12 [H13 [H14 [H15 [H16 [H17 H18]]]]]]].
unfold CHID; fold m; fold d.
elim eq_dart_dec; intro hl.
(* search_left m d p 0 = nil *)
simpl fst; simpl snd.
unfold is_convex; intros da y h1 h2 h3 h4.
apply expf_I in h1; try assumption.
assert (t1: x <> da).
 apply expf_symm in h1; unfold expf, MF.expo in h1.
 destruct h1 as [ha [hb hc]].
 intro h; apply H11; rewrite h; apply hb.
assert (t2: x <> cA m zero da).
 apply expf_symm in h1; unfold expf, MF.expo in h1.
 destruct h1 as [ha [hb hc]].
 intro h; apply H11; rewrite h.
 apply exd_cA; try assumption.
generalize h3 h4; clear h3 h4; simpl; eqdartdec.
elim (eq_dart_dec x y); intro t3.
(* x = y *)
intros h3 h4; clear h2 t3.
apply left_nil_all_invisible with d; assumption.
(* x <> y *)
intros h3 h4; apply H8; try assumption.
simpl in h2; elimination h2; tauto.
(**)
unfold prec_I; split; assumption.
intro h; apply H11; rewrite h; apply H9.
(* search_left m d p 0 <> nil *)
set (l := search_left m d p 0).
set (r := search_right m l p 0).
set (l0 := cA m zero l).
set (r0 := cA_1 m zero r).
assert (hr: (search_right m l p 0) <> nil).
apply exd_left_dart_exd_right_dart; assumption.
set (m1 := Split m zero l l0).
set (m2 := if (eq_dart_dec l0 r) then m1 else Split m1 zero r0 r).
set (m3 := (I (I m2 x t p) max t p)).
set (m4 := Merge m3 one max x).
set (m5 := Merge m4 zero l max).
set (m6 := Merge m5 zero x r).
simpl fst; simpl snd.
unfold is_convex; intros da y.
(* da = x *)
elim (eq_dart_dec da x); intros heq1 h1. subst da.
unfold m6, m5, m4, m3, m2, m1, r0, l0, r, l, d, m.
rewrite cA_m6_zero_x; try assumption.
fold m d l r l0 r0. fold m1. fold m2.
repeat rewrite <- exd_Merge.
repeat rewrite fpoint_Merge.
intro h2; simpl exd in h2.
elimination h2. subst y.
simpl fpoint; eqdartdec; tauto.
elimination h2. subst y.
simpl fpoint; eqdartdec; tauto.
apply exd_m2 in h2; apply exd_m1 in h2.
assert (e1: r <> x).
intro h; apply H11; rewrite <- h.
apply exd_right; assumption.
assert (e2: r <> max).
intro h; apply H12; rewrite <- h.
apply exd_right; assumption.
assert (e3: y <> x).
intro h; rewrite h in h2; contradiction.
assert (e4: y <> max).
intro h; rewrite h in h2; contradiction.
simpl; eqdartdec.
assert (t1: fpoint m2 y = fpoint m y).
unfold m2; elim eq_dart_dec; intro h0.
unfold m1; rewrite fpoint_Split; trivial.
unfold m1; do 2 rewrite fpoint_Split; trivial.
assert (t2: fpoint m2 r = fpoint m r).
unfold m2; elim eq_dart_dec; intro h0.
unfold m1; rewrite fpoint_Split; trivial.
unfold m1; do 2 rewrite fpoint_Split; trivial.
rewrite t1; rewrite t2; intros h3 h4; clear t1 t2.
(**)
elim (eq_point_dec_2 (fpoint m y) (fpoint m (cA m zero (cA m one r)))).
intro h5; rewrite h5; do 2 apply ccw_axiom_1.
assert (h: exd m l). apply exd_left; assumption.
generalize (invisibleright m l p 0 H1 h hr).
unfold invisible_pred. fold r. unfold cF_1.
rewrite cA_1_cA; try assumption.
rewrite cA_one_fpoint; try intuition.
apply exd_right; assumption.
apply exd_cA; try assumption.
apply exd_right; assumption.
intro h5.
(**)
elim (eq_point_dec_2 (fpoint m y) (fpoint m (cA m zero r))).
intro h6; rewrite h6; do 2 apply ccw_axiom_1.
assert (h: exd m l). apply exd_left; assumption.
generalize (visibleright m l p 0 H1 h hr).
unfold visible_pred. fold r.
rewrite (eq_cA_cA_1 m zero r); try intuition.
intro h6.
(**)
elim (eq_point_dec_2 (fpoint m (cA m zero r)) (fpoint m (cA m zero (cA m one r)))).
intro h7; assert False; [idtac|tauto].
assert (t1: expf m d r0).
 apply expf_trans with l.
 apply expfleft; assumption.
 apply expfright; try assumption.
 apply exd_left; assumption.
assert (t2: fpoint m r0 <> fpoint m y).
 apply not_eq_sym. unfold r0.
 rewrite <- eq_cA_cA_1; assumption.
assert (t3: fpoint m (cA m zero r0) <> fpoint m y).
 unfold r0, r, l, m, d.
 rewrite cA_m_zero_r0; assumption.
generalize (H8 r0 y t1 h2 t2 t3). intro f1.
unfold r0, r, l, m, d in f1.
rewrite cA_m_zero_r0 in f1; try assumption.
fold d m l r r0 in f1.
assert (t4: expf m d (cA m one r)).
 apply expf_trans with l.
 apply expfleft; assumption.
 apply expf_trans with r0.
 apply expfright; try assumption.
 apply exd_left; assumption.
 unfold r0. rewrite <- eq_cA_cA_1; try assumption.
 apply expf_cA_cA; try assumption.
 apply exd_right; assumption.
assert (t5: fpoint m (cA m one r) = fpoint m r).
 apply cA_one_fpoint; try assumption.
 apply exd_right; assumption.
assert (t6: fpoint m (cA m one r) <> fpoint m y).
 rewrite t5; assumption.
assert (t7: fpoint m (cA m zero (cA m one r)) <> fpoint m y).
 apply not_eq_sym; rewrite <- h7; assumption.
generalize (H8 (cA m one r) y t4 h2 t6 t7). intro f2.
rewrite t5 in f2; rewrite <- h7 in f2.
rewrite eq_cA_cA_1 in f2; try assumption.
fold r0 in f2. apply ccw_axiom_1 in f2.
apply ccw_axiom_2 in f2. contradiction.
intro h7.
(**)
do 2 apply ccw_axiom_1.
apply (ccw_axiom_5 (fpoint m y) (fpoint m (cA_1 m zero r))
 p (fpoint m (cF_1 m r)) (fpoint m r)).
(**)
assert (t1: fpoint m r = fpoint m (cA m one r)).
rewrite <- (cA_one_fpoint m r); try assumption.
trivial. apply exd_right; assumption.
rewrite t1; unfold cF_1.
apply H8; try assumption.
apply expf_trans with l.
apply expfleft; assumption.
apply expf_trans with (cA_1 m zero r).
apply expfright; try assumption.
apply exd_left; assumption.
rewrite <- eq_cA_cA_1; try assumption.
apply expf_cA_cA; try assumption.
apply exd_right; assumption.
rewrite <- t1; assumption.
apply neq_sym_point; assumption.
(**)
apply ccw_axiom_1.
generalize (H8 (cA_1 m zero r) (cF_1 m r)).
simpl. rewrite cA_cA_1; try assumption.
intro t0; apply t0; clear t0.
apply expf_trans with l.
apply expfleft; assumption.
apply expfright; try assumption.
apply exd_left; assumption.
apply -> exd_cF_1; try assumption.
apply exd_right; assumption.
rewrite <- eq_cA_cA_1; try assumption.
unfold cF_1. apply not_eq_sym.
rewrite <- (cA_one_fpoint m r); try assumption.
apply cA_zero_fpoint; try assumption.
unfold inv_poly. intros k x0 hx0. apply H3.
apply eqc_trans with (cA m one r); try assumption.
apply eqc_trans with r. apply eqc_trans with l.
apply eqcleft; assumption.
apply eqcright; try assumption.
apply exd_left; try assumption.
apply eqc_eqc_cA; try assumption.
apply eqc_refl. apply exd_right; try assumption.
apply exd_cA; try assumption.
apply exd_right; try assumption.
apply exd_right; try assumption.
apply exd_right; try assumption.
(**)
assert (h: exd m l). apply exd_left; assumption.
generalize (invisibleright m l p 0 H1 h hr).
unfold invisible_pred. fold r. unfold cF_1.
rewrite cA_1_cA; try assumption.
rewrite cA_one_fpoint; try intuition.
apply exd_right; assumption.
apply exd_cA; try assumption.
apply exd_right; assumption.
(**)
apply ccw_axiom_1.
generalize (H8 (cA_1 m zero r) y).
simpl. rewrite cA_cA_1; try assumption.
intro t0; apply t0; clear t0; try tauto.
apply expf_trans with l.
apply expfleft; assumption.
apply expfright; try assumption.
apply exd_left; assumption.
rewrite <- eq_cA_cA_1; try assumption.
apply not_eq_sym; assumption.
apply exd_right; assumption.
(**)
do 2 apply ccw_axiom_1.
assert (h: exd m l). apply exd_left; assumption.
generalize (visibleright m l p 0 H1 h hr).
unfold visible_pred. fold r. trivial.
(* da = l *)
elim (eq_dart_dec da l); intro heq2. subst da.
unfold m6, m5, m4, m3, m2, m1, r0, l0, r, l, d, m.
rewrite cA_m6_zero_da; try assumption.
rewrite cA_m5_zero_l; try assumption.
fold m d l r l0 r0. fold m1. fold m2.
repeat rewrite <- exd_Merge.
repeat rewrite fpoint_Merge.
intro h2; simpl exd in h2.
elimination h2. subst y.
simpl fpoint; eqdartdec; tauto.
elimination h2. subst y.
simpl fpoint; eqdartdec; tauto.
apply exd_m2 in h2; apply exd_m1 in h2.
assert (e1: l <> x).
intro h; apply H11; rewrite <- h.
apply exd_left; assumption.
assert (e2: l <> max).
intro h; apply H12; rewrite <- h.
apply exd_left; assumption.
assert (e3: y <> x).
intro h; rewrite h in h2; contradiction.
assert (e4: y <> max).
intro h; rewrite h in h2; contradiction.
simpl; eqdartdec.
assert (tp1: fpoint m2 l = fpoint m l).
unfold m2; elim eq_dart_dec; intro h0.
unfold m1; rewrite fpoint_Split; trivial.
unfold m1; do 2 rewrite fpoint_Split; trivial.
assert (tp2: fpoint m2 y = fpoint m y).
unfold m2; elim eq_dart_dec; intro h0.
unfold m1; rewrite fpoint_Split; trivial.
unfold m1; do 2 rewrite fpoint_Split; trivial.
rewrite tp1; rewrite tp2; intros h3 h4; clear tp1 tp2.
(**)
elim (eq_point_dec_2 (fpoint m y) (fpoint m (cA m zero l))).
intro h5; rewrite h5.
generalize (visibleleft m d p 0 H1 H9 hl).
unfold visible_succ. fold l. trivial.
intro h5.
(**)
elim (eq_point_dec_2 (fpoint m y) (fpoint m (cA m zero (cA m one l)))).
intro h6; rewrite h6; apply ccw_axiom_1.
generalize (invisibleleft m d p 0 H1 H9 hl).
unfold invisible_succ. fold l. unfold cF_1.
rewrite (eq_cA_cA_1 m zero (cA m one l)) at 2.
rewrite cA_cA_1; try assumption.
rewrite cA_one_fpoint; try intuition.
apply exd_left; assumption.
apply exd_cA; try assumption.
apply exd_left; assumption.
assumption. assumption.
intro h6.
(**)
elim (eq_point_dec_2 (fpoint m (cA m zero l)) (fpoint m (cA m zero (cA m one l)))).
intro h7; assert False; [idtac|tauto].
assert (t1: expf m d l).
 apply expfleft; assumption.
assert (t3: fpoint m (cA m zero l) <> fpoint m y).
 apply not_eq_sym; assumption.
generalize (H8 l y t1 h2 h3 t3). intro f1. fold l0 in f1.
assert (t4: expf m d (cA m zero (cA m one l))).
 fold (cF_1 m l). apply expf_trans with l.
 apply expfleft; assumption.
 generalize (expf_Iter_cF_1 m l 1).
 simpl. intro h; apply h; try assumption.
 apply exd_left; assumption.
assert (t5: fpoint m (cA m zero (cA m one l)) <> fpoint m y).
 rewrite <- h7. assumption.
assert (t6: fpoint m (cA m zero (cA m zero (cA m one l))) <> fpoint m y).
 rewrite H2. rewrite cA_one_fpoint; try assumption.
 apply exd_left; assumption. apply exd_cA; try assumption.
 apply exd_left; assumption.
generalize (H8 (cA m zero (cA m one l)) y t4 h2 t5 t6). intro f2.
rewrite <- h7 in f2. fold l0 in f2.
assert (tt: fpoint m (cA m zero (cA m zero (cA m one l))) = fpoint m l).
 rewrite H2. apply cA_one_fpoint; try assumption.
 apply exd_left; assumption. apply exd_cA; try assumption.
 apply exd_left; assumption. rewrite tt in f2.
apply ccw_axiom_1 in f2. apply ccw_axiom_2 in f2. contradiction.
intro h7.
(**)
apply (ccw_axiom_5_bis p (fpoint m (cA m zero l)) (fpoint m y) (fpoint m (cA m zero (cA m one l))) (fpoint m l)).
(**)
generalize (invisibleleft m d p 0 H1 H9 hl).
unfold invisible_succ. fold l. unfold cF_1.
rewrite (eq_cA_cA_1 m zero (cA m one l)) at 2.
rewrite cA_cA_1; try assumption.
rewrite cA_one_fpoint; try intuition.
apply exd_left; assumption.
apply exd_cA; try assumption.
apply exd_left; assumption.
assumption. assumption.
(**)
do 2 apply ccw_axiom_1.
generalize (H8 l (cA m zero (cA m one l))).
intro t0; apply t0; try assumption; clear t0.
apply expfleft; assumption.
apply exd_cA; try assumption.
apply exd_cA; try assumption.
apply exd_left; assumption.
rewrite <- (cA_one_fpoint m l); try assumption.
apply not_eq_sym.
apply cA_zero_fpoint; try assumption.
unfold inv_poly. intros k x0 hx0. apply H3.
apply eqc_trans with (cA m one l); try assumption.
apply eqc_trans with l.
apply eqcleft; assumption.
apply eqc_eqc_cA; try assumption.
apply eqc_refl. apply exd_left; try assumption.
apply exd_cA; try assumption.
apply exd_left; try assumption.
apply exd_left; try assumption.
(**)
pose (pl := (cA m zero (cA m one l))). fold pl.
assert (hp: fpoint m l = fpoint m (cA m zero pl)).
rewrite eq_cA_cA_1; try assumption.
unfold pl; rewrite cA_1_cA; try assumption.
apply eq_sym; apply cA_one_fpoint; try assumption.
apply exd_left; assumption.
apply exd_cA; try assumption.
apply exd_left; assumption.
rewrite hp. apply H8; try assumption.
apply expf_trans with l.
apply expfleft; assumption.
apply expf_symm.
unfold expf, MF.expo, MF.f, McF.f.
split; [assumption|split].
apply exd_cA; try assumption.
apply exd_cA; try assumption.
apply exd_left; assumption.
exists 1; simpl; unfold cF, pl.
rewrite cA_1_cA; try assumption.
rewrite cA_1_cA; try tauto.
apply exd_left; assumption.
apply exd_cA; try assumption.
apply exd_left; assumption.
unfold pl; apply not_eq_sym; assumption.
rewrite <- hp; assumption.
(**)
generalize (visibleleft m d p 0 H1 H9 hl).
unfold visible_succ. fold l. trivial.
(**)
apply H8; try assumption.
apply expfleft; assumption.
apply not_eq_sym; assumption.
(**)
do 3 apply exd_Merge; simpl; right; right.
elim eq_dart_dec; intro h0.
apply exd_Split; apply exd_left; assumption.
do 2 apply exd_Split; apply exd_left; assumption.
apply neq_left_right; try tauto.
(* da = da *)
unfold m6, m5, m4, m3.
repeat rewrite <- exd_Merge.
repeat rewrite fpoint_Merge.
intro h2; simpl exd in h2.
assert (t3: da <> max).
intro h. unfold m2, r0, l0, r, l, d, m.
apply (not_expf_m6_max_x md x t p max); try assumption.
apply expf_symm. rewrite h in h1.
unfold m6, m5, m4, m3, m2, r0, l0, r, l, d, m in h1.
exact h1.
assert (t4: da <> r).
intro h. unfold m2, r0, l0, r, l, d, m.
apply (not_expf_m6_x_r md x t p max); try assumption.
rewrite h in h1. unfold m6, m5, m4, m3, m2, r0, l0, r, l, d, m in h1.
exact h1.
assert (t5: da <> l0).
elim (eq_dart_dec l0 r); intro heq.
rewrite heq; assumption.
intro h. apply (not_eqc_m6_r_r0 md x t p max); try assumption.
apply eqc_trans with x. apply eqc_trans with max.
apply eqc_symm. apply expf_eqc. apply inv_hmap_m6; assumption.
apply expf_m6_max_r; assumption.
apply eqc_m6_max_x; assumption.
apply eqc_trans with l0. apply expf_eqc.
apply inv_hmap_m6; assumption.
rewrite h in h1. unfold m6, m5, m4, m3, m2, r0, l0, r, l, d, m in h1.
apply h1.
apply expf_eqc. apply inv_hmap_m6; assumption.
apply expf_m6_l0_r0; assumption.
assert (t6: da <> r0).
elim (eq_dart_dec l0 r); intro heq.
apply eq_l0_r_r0_l in heq; try assumption.
unfold r0, l0, r, l, d, m.
rewrite heq; assumption.
intro h. apply (not_eqc_m6_r_r0 md x t p max); try assumption.
apply eqc_trans with x. apply eqc_trans with max.
apply eqc_symm. apply expf_eqc. apply inv_hmap_m6; assumption.
apply expf_m6_max_r; assumption.
apply eqc_m6_max_x; assumption.
rewrite h in h1.
apply expf_eqc. apply inv_hmap_m6; assumption.
unfold m6, m5, m4, m3, m2, r0, l0, r, l, d, m in h1. apply h1.
assert (t7: expf m d da).
unfold m6, m5, m4, m3, m2, r0, l0, r, l, d, m in h1.
apply expf_m6_x_da_expf_m_d_da in h1; try assumption.
elimination h1. contradiction. apply h1.
assert (t8: exd m da).
apply expf_symm in t7.
unfold expf, MF.expo in t7; tauto.
unfold m2, r0, l0, r, l, d, m.
rewrite cA_m6_zero_da; try assumption.
rewrite cA_m5_zero_da; try assumption.
rewrite cA_m4_zero_da; try assumption.
rewrite cA_m3_zero_da; try assumption.
rewrite cA_m2_zero_da; try assumption.
rewrite cA_m1_zero_da; try assumption.
fold m d l r l0 r0. fold m1. fold m2.
assert (e1: cA m zero da <> x).
intro h0; apply H11; rewrite <- h0.
apply exd_cA; assumption.
assert (e2: cA m zero da <> max).
intro h0; apply H12; rewrite <- h0.
apply exd_cA; assumption.
elimination h2. subst y.
simpl; eqdartdec.
assert (tp1: fpoint m2 da = fpoint m da).
unfold m2; elim eq_dart_dec; intro h0.
unfold m1; rewrite fpoint_Split; trivial.
unfold m1; do 2 rewrite fpoint_Split; trivial.
assert (tp2: fpoint m2 (cA m zero da) = fpoint m (cA m zero da)).
unfold m2; elim eq_dart_dec; intro h0.
unfold m1; rewrite fpoint_Split; trivial.
unfold m1; do 2 rewrite fpoint_Split; trivial.
rewrite tp1; rewrite tp2; intros h3 h4; clear tp1 tp2.
unfold m6, m5, m4, m3, m2, r0, l0, r, l, d, m in h1.
apply expf_m6_x_da_betweenf_m6_r1_da_l in h1; try assumption.
elimination h1. contradiction.
apply betweenf_m6_m_r1_da_l with (x:=x) (max:=max) in h1; try assumption.
apply betweenf_m_r1_cF_1_m_l with (x:=x) (max:=max) in h1; try assumption.
apply betweenf_m_r1_l_invisible_succ_m_p with (x:=x) (max:=max) in h1; try assumption.
unfold invisible_succ in h1.
fold m d l r in h1.
elimination h2. subst y.
simpl; eqdartdec.
assert (tp1: fpoint m2 da = fpoint m da).
unfold m2; elim eq_dart_dec; intro h0.
unfold m1; rewrite fpoint_Split; trivial.
unfold m1; do 2 rewrite fpoint_Split; trivial.
assert (tp2: fpoint m2 (cA m zero da) = fpoint m (cA m zero da)).
unfold m2; elim eq_dart_dec; intro h0.
unfold m1; rewrite fpoint_Split; trivial.
unfold m1; do 2 rewrite fpoint_Split; trivial.
rewrite tp1; rewrite tp2; intros h3 h4; clear tp1 tp2.
unfold m6, m5, m4, m3, m2, r0, l0, r, l, d, m in h1.
apply expf_m6_x_da_betweenf_m6_r1_da_l in h1; try assumption.
elimination h1. contradiction.
apply betweenf_m6_m_r1_da_l with (x:=x) (max:=max)in h1; try assumption.
apply betweenf_m_r1_cF_1_m_l with (x:=x) (max:=max)in h1; try assumption.
apply betweenf_m_r1_l_invisible_succ_m_p with (x:=x) (max:=max) in h1; try assumption.
unfold invisible_succ in h1.
fold m d l r in h1.
apply exd_m2 in h2; apply exd_m1 in h2.
assert (e3: y <> x).
intro h; rewrite h in h2; contradiction.
assert (e4: y <> max).
intro h; rewrite h in h2; contradiction.
simpl; eqdartdec.
assert (tp1: fpoint m2 da = fpoint m da).
unfold m2; elim eq_dart_dec; intro h0.
unfold m1; rewrite fpoint_Split; trivial.
unfold m1; do 2 rewrite fpoint_Split; trivial.
assert (tp2: fpoint m2 (cA m zero da) = fpoint m (cA m zero da)).
unfold m2; elim eq_dart_dec; intro h0.
unfold m1; rewrite fpoint_Split; trivial.
unfold m1; do 2 rewrite fpoint_Split; trivial.
assert (tp3: fpoint m2 y = fpoint m y).
unfold m2; elim eq_dart_dec; intro h0.
unfold m1; rewrite fpoint_Split; trivial.
unfold m1; do 2 rewrite fpoint_Split; trivial.
rewrite tp1; rewrite tp2; rewrite tp3.
intros h3 h4; clear tp1 tp2 tp3.
apply (H8 da y); try assumption.
apply -> exd_m1; tauto.
apply -> exd_m2; apply -> exd_m1; tauto.
apply exd_m3_2; apply -> exd_m2; apply -> exd_m1; tauto.
apply -> exd_m4; apply exd_m3_2; apply -> exd_m2; apply -> exd_m1; tauto.
apply -> exd_m5; apply -> exd_m4; apply exd_m3_2; apply -> exd_m2; apply -> exd_m1; tauto.
do 3 apply exd_Merge. apply exd_m3_2; apply -> exd_m2; apply -> exd_m1; tauto.
Qed.

(* ================================ *)
(* ========== ########## ========== *)
(* ================================ *)

Fixpoint linkless (m:fmap) {struct m} : Prop :=
  match m with
    V => True
  | I m0 _ _ _ => linkless m0
  | L _ _ _ _ => False
  end.

(* ================================ *)

Lemma not_exd_CHID :
  forall (md:mapdart)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  ~ exd (fst md) d -> d <> x -> d <> max ->
  ~ exd (fst (CHID md x tx px max)) d.
Proof.
intros md x t p max d H1 H2 H3.
unfold CHID.
elim eq_dart_dec; intro h0.
(* l = nil *)
simpl; intro h.
elimination h.
apply H2; rewrite h; trivial.
apply H1; assumption.
(* l <> nil *)
simpl fst.
do 3 rewrite <- exd_Merge.
simpl; intro h.
elimination h.
apply H3; rewrite h; trivial.
elimination h.
apply H2; rewrite h; trivial.
generalize h; clear h.
elim eq_dart_dec; intro h1.
rewrite <- exd_Split. exact H1.
do 2 rewrite <- exd_Split. exact H1.
Qed.

Lemma exd_CHID_exd_m_or_x_or_max :
  forall (md:mapdart)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  exd (fst (CHID md x tx px max)) d -> exd (fst md) d \/ d = x \/ d = max.
Proof.
intros md x t p max d.
unfold CHID.
elim eq_dart_dec; intro h0.
(* l = nil *)
simpl; intro h.
elimination h; try subst x; tauto.
(* l <> nil *)
simpl fst.
do 3 rewrite <- exd_Merge.
simpl; intro h.
elimination h.
subst max; tauto.
elimination h.
subst x; tauto.
generalize h; clear h.
elim eq_dart_dec; intro h1.
rewrite <- exd_Split; tauto.
do 2 rewrite <- exd_Split; tauto.
Qed.

Lemma inv_fpoint_CHID :
  forall (md:mapdart)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  d <> x -> d <> max ->
  fpoint (fst md) d = fpoint (fst (CHID md x tx px max)) d.
Proof.
intros md x t p max d H1 H2.
unfold CHID.
elim eq_dart_dec; intro h0.
(* l = nil *)
simpl.
elim eq_dart_dec; try trivial.
intro h; subst x; tauto.
(* l <> nil *)
simpl fst.
do 3 rewrite fpoint_Merge.
simpl.
elim eq_dart_dec; intro h2.
subst max; tauto.
elim eq_dart_dec; intro h3.
subst x; tauto.
elim eq_dart_dec; intro h1.
rewrite fpoint_Split; trivial.
do 2 rewrite fpoint_Split; trivial.
Qed.

Lemma fpoint_x :
  forall (md:mapdart)(x:dart)(tx:tag)(px:point)(max:dart),
  ~ exd (fst md) x -> fpoint (fst (CHID md x tx px max)) x = px.
Proof.
intros md x t p max H1.
unfold CHID.
elim eq_dart_dec; intro h0.
(* l = nil *)
simpl; eqdartdec; trivial.
(* l <> nil *)
simpl fst.
do 3 rewrite fpoint_Merge.
simpl.
elim eq_dart_dec; trivial.
eqdartdec; trivial.
Qed.

Lemma fpoint_max :
  forall (md:mapdart)(x:dart)(tx:tag)(px:point)(max:dart),
  ~ exd (fst md) max -> exd (fst (CHID md x tx px max)) max ->
  fpoint (fst (CHID md x tx px max)) max = px.
Proof.
intros md x t p max H1.
unfold CHID.
elim eq_dart_dec; intro h0.
(* l = nil *)
simpl; intro h.
elimination h.
destruct (eq_dart_dec x max); tauto.
contradiction.
(* l <> nil *)
simpl fst.
do 3 rewrite <- exd_Merge.
do 3 rewrite fpoint_Merge.
simpl; intro h.
destruct (eq_dart_dec max max); trivial.
contradiction. 
Qed.

Lemma snd_CHID :
  forall (md:mapdart)(x:dart)(t:tag)(p:point)(max:dart),
  (snd (CHID md x t p max)) =
  if (eq_dart_dec (search_left (fst md) (snd md) p 0) nil)
  then (snd md) else x.
Proof.
intros md x t p max; unfold CHID.
elim eq_dart_dec; intro h; simpl snd; trivial.
Qed.

Lemma exd_CHID_fst_snd :
  forall (md:mapdart)(x:dart)(t:tag)(p:point)(max:dart),
  exd (fst md) (snd md) ->
  exd (fst (CHID md x t p max)) (snd (CHID md x t p max)).
Proof.
intros md x t p max H.
rewrite snd_CHID.
elim eq_dart_dec; intro h.
unfold CHID.
elim eq_dart_dec; intro h0.
simpl; right; assumption.
contradiction.
unfold CHID.
elim eq_dart_dec; intro h0.
contradiction.
simpl fst.
do 3 apply -> exd_Merge.
simpl; right; left; trivial.
Qed.

(* ================================ *)

Lemma is_neq_point_I :
  forall (m:fmap)(d:dart)(t:tag)(p:point),
  inv_hmap m -> ~ exd m d ->
  is_neq_point (I m d t p) -> is_neq_point m.
Proof.
intros m d t p h1 h2 H x y hx hy he.
assert (t1: d <> x).
intro h; apply h2; rewrite h; exact hx.
assert (t2: d <> y).
intro h; apply h2; rewrite h; exact hy.
generalize (H x y); clear H.
simpl. destruct (eq_dart_dec d x); trivial.
contradiction.
destruct (eq_dart_dec d y); trivial.
contradiction.
unfold he; intro h. intro h'; apply h; clear h; try tauto.
apply not_expv_I; try assumption.
intro h; subst x. apply h'.
apply expv_refl; assumption.
Qed.

Lemma is_noalign_I :
  forall (m:fmap)(d:dart)(t:tag)(p:point),
  inv_hmap m -> ~ exd m d ->
  is_noalign (I m d t p) -> is_noalign m.
Proof.
intros m d t p h1 h2 H x y z hx hy hz hp1 hp2 hp3.
assert (t1: d <> x).
intro h; apply h2; rewrite h; exact hx.
assert (t2: d <> y).
intro h; apply h2; rewrite h; exact hy.
assert (t3: d <> z).
intro h; apply h2; rewrite h; exact hz.
generalize (H x y z); clear H.
simpl. eqdartdec.
intro h; apply h; clear h; try tauto.
Qed.

(* ================================ *)

Lemma inv_hmap_inv_gmap_inv_poly_planar_well_emb_convex_CHI :
  forall (m1:fmap)(m2:mapdart)(max:dart),
  let m := (fst m2) in let d := (snd m2) in exd m d ->
  inv_hmap m1 -> linkless m1 -> is_neq_point m1 -> is_noalign m1 ->
  inv_hmap m -> inv_gmap m -> inv_poly m d -> planar m ->
  is_well_emb m -> is_neq_point m -> is_noalign m -> is_convex m d ->
  ~ expf m d (cA m zero d) ->
  (forall (da:dart), max <= da -> da <> nil) ->
  (forall (da:dart), exd m1 da -> ~ exd m da) ->
  (forall (da:dart), max <= da -> ~ exd m1 da /\ ~ exd m da) ->
  (forall (d1:dart)(d2:dart), exd m1 d1 -> exd m d2 -> (fpoint m1 d1) <> (fpoint m d2)) ->
  (forall (d1:dart)(d2:dart)(d3:dart), exd m1 d1 -> exd m1 d2 -> exd m d3 ->
   (fpoint m1 d1) <> (fpoint m1 d2) -> ~ align (fpoint m1 d1) (fpoint m1 d2) (fpoint m d3)) ->
  (forall (d1:dart)(d2:dart)(d3:dart), exd m1 d1 -> exd m d2 -> exd m d3 ->
   (fpoint m d2) <> (fpoint m d3) -> ~ align (fpoint m1 d1) (fpoint m d2) (fpoint m d3)) ->
  inv_hmap (fst (CHI m1 m2 max)) /\ inv_gmap (fst (CHI m1 m2 max)) /\ inv_poly (fst (CHI m1 m2 max)) (snd (CHI m1 m2 max)) /\ planar (fst (CHI m1 m2 max)) /\
  is_well_emb (fst (CHI m1 m2 max)) /\ is_neq_point (fst (CHI m1 m2 max)) /\ is_noalign (fst (CHI m1 m2 max)) /\ is_convex (fst (CHI m1 m2 max)) (snd (CHI m1 m2 max)).
Proof.
induction m1.
 (* Case 1 : m = V *)
 intros m2 max m d myH Hm11 Hm12 Hm13 Hm14 Hm21 Hm22 Hm23 Hm24 Hm25 Hm26 Hm27 Hm28 Hexpf Hw0 Hw1 Hw2 Hp1 Hp2 Hp3.
 simpl in *; intuition.
 (* Case 2 : m = I *)
 intros m2 max m x myH Hm11 Hm12 Hm13 Hm14 Hm21 Hm22 Hm23 Hm24 Hm25 Hm26 Hm27 Hm28 Hexpf Hw0 Hw1 Hw2 Hp1 Hp2 Hp3.
 simpl in *; unfold prec_I in *.
 destruct Hm11 as [Hm11 [Hneq Hexd]].
(**)
assert (Hw3 : forall (da:dart), d = da \/ exd m1 da -> da < max).
 intros da Hda.
 elimination Hda; try subst d.
  elim (le_lt_dec max da); intro H; try assumption.
   generalize (Hw2 da H); intuition.
  elim (le_lt_dec max da); intro H; try assumption.
   generalize (Hw2 da H); intuition.
assert (Hw4 : forall (da:dart), exd m da -> ~ exd m1 da).
 intros da Hda; elim (exd_dec m1 da).
  intro H; generalize (Hw1 da); intuition.
  intro H; assumption.
assert (Hw5 : forall (da:dart), exd m da -> da < max).
 intros da Hda; elim (le_lt_dec max da).
  intro H; generalize (Hw2 da H); intuition.
  intro H; assumption.
(**)
assert (Hp4 : forall (da:dart), exd m1 da -> fpoint m1 da <> p).
 intros da Hda.
 assert (t1: d <> da).
  intro h; apply Hexd; subst d; assumption.
 generalize (Hm13 da d); simpl; eqdartdec.
 intro h; apply h; clear h; try tauto.
 apply not_expv_I; try assumption.
 apply not_eq_sym; assumption.
 intro h; apply expv_symm in h; try assumption.
 apply not_exd_not_expv with m1 d da; assumption.
(**)
assert (H0: prec_CHID (fst m2) (snd m2) d t p max).
 unfold prec_CHID; fold m x; repeat split; try assumption.
 generalize (Hm25 x0 y H H0 H1); intros [t1 t2]; exact t1.
 generalize (Hm25 x0 y H H0 H1); intros [t1 t2]; exact t2.
 apply Hw1; tauto.
 assert (t0: max <= max). lia.
 generalize (Hw2 max t0). tauto.
 apply Hw0; lia.
 assert (t0: d < max). apply Hw3; tauto. lia.
 intros da hda; apply not_eq_sym.
 generalize (Hp1 d da); eqdartdec.
 intro h; apply h; tauto.
 intros da db ha hb hp.
 generalize (Hp3 d da db); eqdartdec.
 intro h; apply h; tauto.
(**)
 apply IHm1; clear IHm1; try assumption.
 (* exd (fst CHID) (snd CHID) *)
 apply exd_CHID_fst_snd; assumption.
 (* is_neq_point m1 *)
 apply is_neq_point_I with d t p; assumption.
 (* noalign m1 *)
 apply is_noalign_I with d t p; assumption.
 (* inv_hmap CHID *)
 apply inv_hmap_CHID; try assumption.
 (* inv_gmap CHID *)
 apply inv_gmap_CHID; try assumption.
 (* inv_poly CHID *)
 apply inv_poly_CHID; try assumption.
 (* planar CHID *)
 apply planar_CHID; try assumption.
 (* is_well_emb CHID *)
 apply is_well_emb_CHID; try assumption.
 (* is_neq_point CHID *)
 apply is_neq_point_CHID; try assumption.
 (* is_noalign CHID *)
 apply is_noalign_CHID; try assumption.
 (* is_convex CHID *)
 apply is_convex_CHID; try assumption.
 (* expf *)
 unfold CHID. fold m x.
 elim eq_dart_dec; intro h0.
 simpl fst; simpl snd.
 simpl cA. elim (eq_dart_dec d x); intro h.
 assert False; [idtac|tauto].
 apply Hw1 with d. left; tauto. rewrite h; exact myH.
 intro hx; apply expf_I in hx; try assumption.
 apply Hexpf; exact hx. unfold prec_I; split.
 exact Hneq. apply Hw1; left; tauto.
 simpl fst; simpl snd.
 unfold m, x; rewrite cA_m6_zero_x; try assumption.
 apply not_expf_m6_x_r; try assumption.
 apply Hw1; left; tauto.
 assert (H: max <= max). lia.
 generalize (Hw2 max H). tauto.
 apply Hw0; lia.
 assert (H: d = d \/ exd m1 d). left; tauto.
 generalize (Hw3 d H). lia.
 intros da db; simpl; intros hda hdb hp.
 generalize (Hp3 d da db); eqdartdec.
 intro h; apply h; tauto.
 apply Hw1; left; tauto.
 assert (H: max <= max). lia.
 generalize (Hw2 max H). tauto.
 apply Hw0; lia.
 assert (H: d = d \/ exd m1 d). left; tauto.
 generalize (Hw3 d H). lia.
 (* Hw0 *)
 intros d0 Hd0; apply Hw0; lia.
 (* Hw1 *)
 intros da Hda; apply not_exd_CHID.
  apply Hw1; right; assumption.
  intro h; subst da; contradiction.
  assert (t0: da < max).
  apply Hw3; tauto. lia.
 (* Hw2 *)
 intros da Hda; split.
  assert (H : max <= da); [lia|idtac].
  generalize (Hw2 da H); intuition.
  apply not_exd_CHID; try lia.
  assert (H : max <= da); [lia|idtac].
  generalize (Hw2 da H); intuition.
  assert (H : max <= da); [lia|idtac].
  generalize (Hw2 da H); intuition.
 (* Hp1 *)
 intros da db Hda Hdb.
 generalize Hdb; intro Hdb2.
 apply exd_CHID_exd_m_or_x_or_max in Hdb.
 assert (t0: d <> da).
  intro h; subst d; contradiction.
 elimination Hdb.
  assert (t1: db <> d).
   intro h; subst db; apply Hw1 with d; tauto.
  assert (t2: db <> max).
   intro h; subst db; generalize (Hw5 max Hdb); lia.
  rewrite <- inv_fpoint_CHID; try assumption.
  generalize (Hp1 da db). eqdartdec.
  intro h; apply h; try tauto; clear h.
 elimination Hdb; subst db.
  rewrite fpoint_x; try assumption.
  apply Hp4; assumption.
  apply Hw1; left; trivial.
  rewrite fpoint_max; try assumption.
  apply Hp4; assumption.
  generalize (Hw2 max (le_refl max)); intuition.
 (* Hp2 *)
 intros da db dc Hda Hdb Hdc Hp0.
 generalize Hdc; intro Hdc2.
 apply exd_CHID_exd_m_or_x_or_max in Hdc2.
 assert (ta: d <> da).
  intro h; subst d; contradiction.
 assert (tb: d <> db).
  intro h; subst d; contradiction.
 elimination Hdc2.
  assert (t1: dc <> d).
   intro h; subst dc; apply Hw1 with d; tauto.
  assert (t2: dc <> max).
   intro h; subst dc; generalize (Hw5 max Hdc2); lia.
  rewrite <- inv_fpoint_CHID; try assumption.
  generalize (Hp2 da db dc). eqdartdec.
  intro h; apply h; try tauto; clear h.
 elimination Hdc2; subst dc.
  rewrite fpoint_x; try assumption.
  assert (H01 : exd (I m1 d t p) da); [simpl;tauto|idtac].
  assert (H02 : exd (I m1 d t p) db); [simpl;tauto|idtac].
  assert (H03 : exd (I m1 d t p) d); [simpl;tauto|idtac].
  generalize (Hm14 da db d H01 H02 H03); clear H01 H02 H03.
  simpl; eqdartdec.
  intro h; apply h; try assumption; clear h.
  apply Hp4; assumption.
  apply Hp4; assumption.
  apply Hw1; left; trivial.
  rewrite fpoint_max; try assumption.
  assert (H01 : exd (I m1 d t p) da); [simpl;tauto|idtac].
  assert (H02 : exd (I m1 d t p) db); [simpl;tauto|idtac].
  assert (H03 : exd (I m1 d t p) d); [simpl;tauto|idtac].
  generalize (Hm14 da db d H01 H02 H03); clear H01 H02 H03.
  simpl; eqdartdec.
  intro h; apply h; try assumption; clear h.
  apply Hp4; assumption.
  apply Hp4; assumption.
  generalize (Hw2 max (le_refl max)); intuition.
 (* Hp3 *)
 intros d1 d2 d3 Hd1 Hd2 Hd3 Hp0.
 generalize Hd2; intro Hd20.
 apply exd_CHID_exd_m_or_x_or_max in Hd20.
 assert (t1: d <> d1).
  intro h; subst d; contradiction.
 elimination Hd20.
  assert (ta: d2 <> d).
   intro h; subst d2; apply Hw1 with d; tauto.
  assert (tb: d2 <> max).
   intro h; subst d2; generalize (Hw5 max Hd20); lia.
 assert (H1 : fpoint (fst m2) d2 = fpoint (fst (CHID m2 d t p max)) d2).
  apply inv_fpoint_CHID; try assumption.
 rewrite <- H1 in *.
 generalize Hd3; intro Hd30.
 apply exd_CHID_exd_m_or_x_or_max in Hd30.
 elimination Hd30.
  assert (tc: d3 <> d).
   intro h; subst d3; apply Hw1 with d; tauto.
  assert (td: d3 <> max).
   intro h; subst d3; generalize (Hw5 max Hd30); lia.
 assert (H2 : fpoint (fst m2) d3 = fpoint (fst (CHID m2 d t p max)) d3).
  apply inv_fpoint_CHID; try assumption.
 rewrite <- H2 in *.
 generalize (Hp3 d1 d2 d3). eqdartdec.
 intro h; apply h; try tauto; clear h.
 elimination Hd30; subst d3.
 assert (H2 : fpoint (fst (CHID m2 d t p max)) d = p).
  apply fpoint_x; try assumption.
  apply Hw1; left; trivial.
 rewrite H2 in *. intro h0.
 generalize (Hp2 d1 d d2). eqdartdec.
 intro h; apply h; try tauto; clear h.
 apply Hp4; assumption.
 auto with myorientation.
 assert (H2 : fpoint (fst (CHID m2 d t p max)) max = p).
  apply fpoint_max; try assumption.
  generalize (Hw2 max (le_refl max)); intuition.
 rewrite H2 in *. intro h0.
 generalize (Hp2 d1 d d2). eqdartdec.
 intro h; apply h; try tauto; clear h.
 apply Hp4; assumption.
 auto with myorientation.
 elimination Hd20; subst d2.
 assert (H1 : fpoint (fst (CHID m2 d t p max)) d = p).
  apply fpoint_x; try assumption.
  apply Hw1; left; trivial.
 rewrite H1 in *.
 generalize Hd3; intro Hd30.
 apply exd_CHID_exd_m_or_x_or_max in Hd30.
 elimination Hd30.
  assert (tc: d3 <> d).
   intro h; subst d3; apply Hw1 with d; tauto.
  assert (td: d3 <> max).
   intro h; subst d3; generalize (Hw5 max Hd30); lia.
 assert (H2 : fpoint (fst m2) d3 = fpoint (fst (CHID m2 d t p max)) d3).
  apply inv_fpoint_CHID; try assumption.
 rewrite <- H2 in *.
 generalize (Hp2 d1 d d3). eqdartdec.
 intro h; apply h; try tauto; clear h.
 apply Hp4; assumption.
 elimination Hd30; subst d3.
 assert (H2 : fpoint (fst (CHID m2 d t p max)) d = p).
  apply fpoint_x; try assumption.
  apply Hw1; left; trivial.
 rewrite H2 in *; tauto.
 assert (H2 : fpoint (fst (CHID m2 d t p max)) max = p).
  apply fpoint_max; try assumption.
  generalize (Hw2 max (le_refl max)); intuition.
 rewrite H2 in *; tauto.
 assert (H1 : fpoint (fst (CHID m2 d t p max)) max = p).
  apply fpoint_max; try assumption.
   generalize (Hw2 max (le_refl max)); intuition.
 rewrite H1 in *.
 generalize Hd3; intro Hd30.
 apply exd_CHID_exd_m_or_x_or_max in Hd30.
 elimination Hd30.
  assert (tc: d3 <> d).
   intro h; subst d3; apply Hw1 with d; tauto.
  assert (td: d3 <> max).
   intro h; subst d3; generalize (Hw5 max Hd30); lia.
 assert (H2 : fpoint (fst m2) d3 = fpoint (fst (CHID m2 d t p max)) d3).
  apply inv_fpoint_CHID; try assumption.
 rewrite <- H2 in *.
 generalize (Hp2 d1 d d3). eqdartdec.
 intro h; apply h; try tauto; clear h.
 apply Hp4; assumption.
 elimination Hd30; subst d3.
 assert (H2 : fpoint (fst (CHID m2 d t p max)) d = p).
  apply fpoint_x; try assumption.
  apply Hw1; left; trivial.
 rewrite H2 in *; tauto.
 assert (H2 : fpoint (fst (CHID m2 d t p max)) max = p).
  apply fpoint_max; try assumption.
  generalize (Hw2 max (le_refl max)); intuition.
 rewrite H2 in *; tauto.
 (* Case 3 : m = L *)
 intros m2 max m x myH Hm11 Hm12 Hm13 Hm14 Hm21 Hm22 Hm23 Hm24 Hm25 Hm26 Hm27 Hm28 Hw0 Hw1 Hw2 Hp1 Hp2 Hp3.
 simpl in *; intuition.
Qed.
