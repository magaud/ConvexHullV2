(* ================================ *)
(* ======= CH04_leftright.v ======= *)
(* ================================ *)

Require Export CH03_lemma.

(* ================================ *)
(* ========== ########## ========== *)
(* ================================ *)

Lemma invisible_not_visible_succ :
  forall (m:fmap)(d:dart)(p:point),
  invisible_succ m d p -> ~ visible_succ m d p.
Proof.
intros m d p.
unfold invisible_succ, visible_succ.
auto with myorientation.
Qed.

Lemma visible_not_invisible_succ :
  forall (m:fmap)(d:dart)(p:point),
  visible_succ m d p -> ~ invisible_succ m d p.
Proof.
intros m d p.
unfold invisible_succ, visible_succ.
auto with myorientation.
Qed.

Lemma invisible_not_visible_pred :
  forall (m:fmap)(d:dart)(p:point),
  invisible_pred m d p -> ~ visible_pred m d p.
Proof.
intros m d p.
unfold invisible_pred, visible_pred.
auto with myorientation.
Qed.

Lemma visible_not_invisible_pred :
  forall (m:fmap)(d:dart)(p:point),
  visible_pred m d p -> ~ invisible_pred m d p.
Proof.
intros m d p.
unfold invisible_pred, visible_pred.
auto with myorientation.
Qed.

(* ================================ *)

Lemma invisible_succ_pred : forall (m:fmap)(d:dart)(p:point),
  inv_hmap m -> exd m d -> invisible_succ m d p ->
  invisible_pred m (cA m zero d) p.
Proof.
intros m d p H1 H2 H.
unfold invisible_succ, invisible_pred in *.
rewrite cA_1_cA; assumption.
Qed.

Lemma invisible_pred_succ : forall (m:fmap)(d:dart)(p:point),
  inv_hmap m -> exd m d -> invisible_pred m d p ->
  invisible_succ m (cA_1 m zero d) p.
Proof.
intros m d p H1 H2 H.
unfold invisible_succ, invisible_pred in *.
rewrite cA_cA_1; assumption.
Qed.

Lemma visible_succ_pred : forall (m:fmap)(d:dart)(p:point),
  inv_hmap m -> exd m d -> visible_succ m d p ->
  visible_pred m (cA m zero d) p.
Proof.
intros m d p H1 H2 H.
unfold visible_succ, visible_pred in *.
rewrite cA_1_cA; assumption.
Qed.

Lemma visible_pred_succ : forall (m:fmap)(d:dart)(p:point),
  inv_hmap m -> exd m d -> visible_pred m d p ->
  visible_succ m (cA_1 m zero d) p.
Proof.
intros m d p H1 H2 H.
unfold visible_succ, visible_pred in *.
rewrite cA_cA_1; assumption.
Qed.

(* ================================ *)

Lemma invisible_succ_visible_pred :
  forall (m:fmap)(d:dart)(p:point),
  cA m zero d = cA_1 m zero d ->
  (invisible_succ m d p <-> visible_pred m d p).
Proof.
intros m d p H.
unfold invisible_succ, visible_pred in *.
rewrite H; split; auto with myorientation.
Qed.

Lemma invisible_pred_visible_succ :
  forall (m:fmap)(d:dart)(p:point),
  cA m zero d = cA_1 m zero d ->
  (invisible_pred m d p <-> visible_succ m d p).
Proof.
intros m d p H.
unfold invisible_pred, visible_succ in *.
rewrite H; split; auto with myorientation.
Qed.

(* ================================ *)
(* ========== ########## ========== *)
(* ================================ *)

Lemma expfleft : forall (m:fmap)(d:dart)(p:point)(i:nat),
  inv_hmap m -> exd m d -> (search_left m d p i) <> nil ->
  expf m d (search_left m d p i).
Proof.
intros m d p.
set (P := fun (i:nat)(res:dart) =>
  inv_hmap m -> exd m d -> res <> nil -> expf m d res).
apply (search_left_ind m d p P).
intros i h1 h2; unfold P; tauto.
intros i h1 h2 di h3 h4; unfold P.
intros hmap hexd hneq; unfold expf; split; try assumption.
 unfold MF.expo; split; try assumption.
 unfold MF.f, McF.f, di. exists i. trivial.
intros i h1 h2 di h3 h4; unfold P.
intros H H0 H1 H2; apply H; assumption.
Qed.

Lemma exdleft : forall (m:fmap)(d:dart)(p:point)(i:nat),
  inv_hmap m -> exd m d -> (search_left m d p i) <> nil ->
  exd m (search_left m d p i).
Proof.
intros m d p i H1 H2 H3.
generalize (expfleft m d p i H1 H2 H3).
intro h; apply expf_symm in h.
unfold expf in h; unfold MF.expo in h; tauto.
Qed.

Lemma eqcleft : forall (m:fmap)(d:dart)(p:point)(i:nat),
  inv_hmap m -> exd m d -> (search_left m d p i) <> nil ->
  eqc m d (search_left m d p i).
Proof.
intros m d p i H1 H2 H3.
generalize (expfleft m d p i H1 H2 H3).
intro h; unfold expf in h.
apply expf_eqc; intuition.
Qed.

(* ===== *)

Lemma visibleleft : forall (m:fmap)(d:dart)(p:point)(i:nat),
  inv_hmap m -> exd m d -> (search_left m d p i) <> nil ->
  visible_succ m (search_left m d p i) p.
Proof.
intros m d p.
set (P := fun (i:nat)(res:dart) =>
  inv_hmap m -> exd m d -> res <> nil -> visible_succ m res p).
apply (search_left_ind m d p P).
intros i h1 h2; unfold P; tauto.
intros i h1 h2 di h3 h4; unfold P.
intros hmap hexd hneq; clear P h2 h4.
unfold left_dart in h3; tauto.
intros i h1 h2 di h3 h4; unfold P.
intros H H0 H1 H2; apply H; assumption.
Qed.

Lemma invisibleleft : forall (m:fmap)(d:dart)(p:point)(i:nat),
  inv_hmap m -> exd m d -> (search_left m d p i) <> nil ->
  invisible_succ m (cF_1 m (search_left m d p i)) p.
Proof.
intros m d p.
set (P := fun (i:nat)(res:dart) =>
  inv_hmap m -> exd m d -> res <> nil -> invisible_succ m (cF_1 m res) p).
apply (search_left_ind m d p P).
intros i h1 h2; unfold P; tauto.
intros i h1 h2 di h3 h4; unfold P.
intros hmap hexd hneq; clear P h2 h4.
unfold left_dart in h3; tauto.
intros i h1 h2 di h3 h4; unfold P.
intros H H0 H1 H2; apply H; assumption.
Qed.

(* ===== *)

Lemma left_neq_nil_exists_left : forall (m:fmap)(d:dart)(p:point)(i:nat),
  inv_hmap m -> exd m d -> (search_left m d p i) <> nil ->
  exists j:nat, (j < degreef m d) /\ (left_dart m (Iter (cF m) j d) p).
Proof.
intros m d p.
set (P := fun (i:nat)(res:dart) => inv_hmap m -> exd m d -> res <> nil ->
  exists j:nat, (j < degreef m d) /\ (left_dart m (Iter (cF m) j d) p)).
apply (search_left_ind m d p P).
intros i h1 h2; unfold P; tauto.
intros i h1 h2 di h3 h4; unfold P.
intros hmap hexd hneq; clear P h2 h4.
exists i; split; assumption.
intros i h1 h2 di h3 h4; unfold P.
intros H H0 H1 H2; apply H; assumption.
Qed.

Lemma all_not_left_left_eq_nil : forall (m:fmap)(d:dart)(p:point)(i:nat),
  inv_hmap m -> exd m d -> (forall (j:nat), ~ (left_dart m (Iter (cF m) j d) p)) ->
  (search_left m d p i) = nil.
Proof.
intros m d p i h1 h2 h3.
elim (eq_dart_dec (search_left m d p i) nil).
trivial. intro h.
assert False; [idtac|tauto].
generalize (left_neq_nil_exists_left m d p i h1 h2 h).
intro h0; elim h0; clear h0.
intros j [hj1 hj2].
apply h3 with j; assumption.
Qed.

Lemma left_eq_nil_all_not_left : forall (m:fmap)(d:dart)(p:point)(i:nat),
  inv_hmap m -> exd m d -> (search_left m d p i) = nil ->
  (forall (j:nat), (i <= j < degreef m d) -> ~ (left_dart m (Iter (cF m) j d) p)).
Proof.
intros m d p.
set (P := fun (i:nat)(res:dart) => inv_hmap m -> exd m d -> res = nil ->
  (forall (j:nat), (i <= j < degreef m d) -> ~ (left_dart m (Iter (cF m) j d) p))).
apply (search_left_ind m d p P).
intros i h1 h2; unfold P.
intros hmap hexd heq j hj; lia.
intros i h1 h2 di h3 h4; unfold P.
intros hmap hexd heq; clear P h2 h4.
assert False; [idtac|tauto].
apply exd_not_nil with m di; try assumption.
apply exd_Iter_cF; assumption.
intros i h1 h2 di h3 h4; unfold P.
intros H hmap hexd heq j hj; clear P h2 h4.
elim (eq_nat_dec i j).
intro h; subst j; apply h3.
intro h; apply H; try assumption. lia.
Qed.

Lemma exists_left_left_neq_nil : forall (m:fmap)(d:dart)(p:point)(i:nat),
  inv_hmap m -> exd m d ->
  (exists j:nat, (i <= j < degreef m d) /\ (left_dart m (Iter (cF m) j d) p)) ->
  (search_left m d p i) <> nil.
Proof.
intros m d p i h1 h2 h3.
elim h3; clear h3; intros j [ha hb].
elim (eq_dart_dec (search_left m d p i) nil).
intro h. assert False; [idtac|tauto].
generalize (left_eq_nil_all_not_left m d p i h1 h2 h).
intro h0. apply h0 with j.
assumption. assumption. trivial.
Qed.

(* ================================ *)

Lemma expfright : forall (m:fmap)(d:dart)(p:point)(i:nat),
  inv_hmap m -> exd m d -> (search_right m d p i) <> nil ->
  expf m d (cA_1 m zero (search_right m d p i)).
Proof.
intros m d p.
set (P := fun (i:nat)(res:dart) =>
  inv_hmap m -> exd m d -> res <> nil -> expf m d (cA_1 m zero res)).
apply (search_right_ind m d p P).
intros i h1 h2; unfold P; tauto.
intros i h1 h2 di di0 h3 h4; unfold P.
intros hmap hexd hneq; unfold expf; split; try assumption.
 unfold MF.expo; split; try assumption.
 unfold MF.f, McF.f, di0, di.
 exists i; rewrite cA_1_cA; trivial.
 apply exd_Iter_cF; assumption.
intros i h1 h2 di di0 h3 h4; unfold P.
intros H H0 H1 H2; apply H; assumption.
Qed.

Lemma exdright : forall (m:fmap)(d:dart)(p:point)(i:nat),
  inv_hmap m -> exd m d -> (search_right m d p i) <> nil ->
  exd m (search_right m d p i).
Proof.
intros m d p i H1 H2 H3.
generalize (expfright m d p i H1 H2 H3).
intro h; apply expf_symm in h.
unfold expf in h; unfold MF.expo in h.
destruct h as [h1 [h2 h3]].
apply exd_cA_1 in h2; assumption.
Qed.

Lemma eqcright : forall (m:fmap)(d:dart)(p:point)(i:nat),
  inv_hmap m -> exd m d -> (search_right m d p i) <> nil ->
  eqc m d (search_right m d p i).
Proof.
intros m d p i H1 H2 H3.
pose (u := (search_right m d p i)).
apply eqc_trans with (cA_1 m zero u).
generalize (expfright m d p i H1 H2 H3).
intro h; unfold expf in h.
apply expf_eqc; intuition.
apply eqc_symm; apply eqc_eqc_cA_1. assumption.
apply eqc_refl; apply exdright; assumption.
Qed.

(* ===== *)

Lemma visibleright : forall (m:fmap)(d:dart)(p:point)(i:nat),
  inv_hmap m -> exd m d -> (search_right m d p i) <> nil ->
  visible_pred m (search_right m d p i) p.
Proof.
intros m d p.
set (P := fun (i:nat)(res:dart) =>
  inv_hmap m -> exd m d -> res <> nil -> visible_pred m res p).
apply (search_right_ind m d p P).
intros i h1 h2; unfold P; tauto.
intros i h1 h2 di di0 h3 h4; unfold P.
intros hmap hexd hneq; clear P h2 h4.
unfold right_dart in h3; tauto.
intros i h1 h2 di di0 h3 h4; unfold P.
intros H H0 H1 H2; apply H; assumption.
Qed.

Lemma invisibleright : forall (m:fmap)(d:dart)(p:point)(i:nat),
  inv_hmap m -> exd m d -> (search_right m d p i) <> nil ->
  invisible_pred m (cF_1 m (search_right m d p i)) p.
Proof.
intros m d p.
set (P := fun (i:nat)(res:dart) =>
  inv_hmap m -> exd m d -> res <> nil -> invisible_pred m (cF_1 m res) p).
apply (search_right_ind m d p P).
intros i h1 h2; unfold P; tauto.
intros i h1 h2 di di0 h3 h4; unfold P.
intros hmap hexd hneq; clear P h2 h4.
unfold right_dart in h3; tauto.
intros i h1 h2 di di0 h3 h4; unfold P.
intros H H0 H1 H2; apply H; assumption.
Qed.

(* ===== *)

Lemma right_neq_nil_exists_right : forall (m:fmap)(d:dart)(p:point)(i:nat),
  inv_hmap m -> exd m d -> (search_right m d p i) <> nil ->
  exists j:nat, (j < degreef m d) /\ (right_dart m (cA m zero (Iter (cF m) j d)) p).
Proof.
intros m d p.
set (P := fun (i:nat)(res:dart) => inv_hmap m -> exd m d -> res <> nil ->
  exists j:nat, (j < degreef m d) /\ (right_dart m (cA m zero (Iter (cF m) j d)) p)).
apply (search_right_ind m d p P).
intros i h1 h2; unfold P; tauto.
intros i h1 h2 di di0 h3 h4; unfold P.
intros hmap hexd hneq; clear P h2 h4.
exists i; split; assumption.
intros i h1 h2 di di0 h3 h4; unfold P.
intros H H0 H1 H2; apply H; assumption.
Qed.

Lemma all_not_right_right_eq_nil : forall (m:fmap)(d:dart)(p:point)(i:nat),
  inv_hmap m -> exd m d -> (forall (j:nat), ~ (right_dart m (cA m zero (Iter (cF m) j d)) p)) ->
  (search_right m d p i) = nil.
Proof.
intros m d p i h1 h2 h3.
elim (eq_dart_dec (search_right m d p i) nil).
trivial. intro h.
assert False; [idtac|tauto].
generalize (right_neq_nil_exists_right m d p i h1 h2 h).
intro h0; elim h0; clear h0.
intros j [hj1 hj2].
apply h3 with j; assumption.
Qed.

Lemma right_eq_nil_all_not_right : forall (m:fmap)(d:dart)(p:point)(i:nat),
  inv_hmap m -> exd m d -> (search_right m d p i) = nil ->
  (forall (j:nat), (i <= j < degreef m d) -> ~ (right_dart m (cA m zero (Iter (cF m) j d)) p)).
Proof.
intros m d p.
set (P := fun (i:nat)(res:dart) => inv_hmap m -> exd m d -> res = nil ->
  (forall (j:nat), (i <= j < degreef m d) -> ~ (right_dart m (cA m zero (Iter (cF m) j d)) p))).
apply (search_right_ind m d p P).
intros i h1 h2; unfold P.
intros hmap hexd heq j hj; lia.
intros i h1 h2 di di0 h3 h4; unfold P.
intros hmap hexd heq; clear P h2 h4.
assert False; [idtac|tauto].
apply exd_not_nil with m di0; try assumption.
apply exd_cA; try assumption.
apply exd_Iter_cF; assumption.
intros i h1 h2 di di0 h3 h4; unfold P.
intros H hmap hexd heq j hj; clear P h2 h4.
elim (eq_nat_dec i j).
intro h; subst j; apply h3.
intro h; apply H; try assumption. lia.
Qed.

Lemma exists_right_r_neq_nil : forall (m:fmap)(d:dart)(p:point)(i:nat),
  inv_hmap m -> exd m d ->
  (exists j:nat, (i <= j < degreef m d) /\ (right_dart m (cA m zero (Iter (cF m) j d)) p)) ->
  (search_right m d p i) <> nil.
Proof.
intros m d p i h1 h2 h3.
elim h3; clear h3; intros j [ha hb].
elim (eq_dart_dec (search_right m d p i) nil).
intro h. assert False; [idtac|tauto].
generalize (right_eq_nil_all_not_right m d p i h1 h2 h).
intro h0. apply h0 with j.
assumption. assumption. trivial.
Qed.

(* ================================ *)
(* ========== ########## ========== *)
(* ================================ *)

Lemma P_Iter_cF_expf :
  forall (m:fmap)(d:dart)(x:dart)(p:point)(P:fmap->dart->point->Prop),
  inv_hmap m -> exd m d -> expf m d x ->
  (forall (i:nat), (0 <= i < degreef m d) -> P m (Iter (cF m) i d) p) ->
  P m x p.
Proof.
intros m d x p P h1 h2 h3 h4.
assert (t0: exists i:nat, Iter (cF m) i d = x).
unfold expf, MF.expo, MF.f, McF.f in h3; tauto.
elim t0; intros i hi.
elim (le_lt_dec (degreef m d) i); intro h0.
generalize (MF.expo_expo1 m d x h1).
unfold MF.expo, MF.expo1, MF.f, McF.f.
intros [t1 t2]; clear t2.
generalize (t1 (conj h2 t0)); clear t0 t1.
intros [t1 t2]; elim t2; clear t1 t2.
intros j [j1 j2]; rewrite <- j2; apply h4.
rewrite <- MF.upb_eq_degree; try assumption.
lia. rewrite <- hi; apply h4; lia.
Qed.

(* ================================ *)

Section leftright_sec.

Variables (m:fmap)(d:dart)(p:point).

Let l := search_left m d p 0.
Let r := search_right m l p 0.

Let l0 := cA m zero l.
Let r0 := cA_1 m zero r.

Let l1 := cA m one l.
Let r1 := cA m one r.

Hypothesis Hd : exd m d.

Hypothesis H1 : inv_hmap m.
Hypothesis H2 : inv_gmap m.
Hypothesis H3 : inv_poly m d.
Hypothesis H4 : planar m.

Hypothesis H5 : is_well_emb m.
Hypothesis H6 : is_neq_point m.
Hypothesis H7 : is_noalign m.
Hypothesis H8 : is_convex m d.

Hypothesis H9 : forall (da:dart), exd m da -> fpoint m da <> p.
Hypothesis H10 : forall (da:dart)(db:dart),
  let pda := fpoint m da in let pdb := fpoint m db in
  exd m da -> exd m db -> pda <> pdb -> ~ align p pda pdb.

Hypothesis H0 : ~ expf m d (cA m zero d).

(* ================================ *)

Lemma neq_left_right : l <> nil \/ r <> nil -> l <> r.
Proof.
elim (eq_dart_dec l r); try trivial.
intros h0 h; elimination h.
assert (h1: exd m l).
apply exdleft; assumption.
assert (h2: r <> nil).
rewrite h0 in h; assumption.
generalize (visibleleft m d p 0 H1 Hd h).
intro h3; fold l in h3.
generalize (visibleright m l p 0 H1 h1 h2).
intro h4; fold r in h4.
apply visible_not_invisible_succ in h3.
apply <- invisible_succ_visible_pred in h4.
rewrite h0 in h3; contradiction.
apply eq_cA_cA_1; assumption.
assert (h1: l <> nil).
rewrite <- h0 in h; assumption.
assert (h2: exd m l).
apply exdleft; try assumption.
generalize (visibleleft m d p 0 H1 Hd h1).
intro h3; fold l in h3.
generalize (visibleright m l p 0 H1 h2 h).
intro h4; fold r in h4.
apply visible_not_invisible_succ in h3.
apply <- invisible_succ_visible_pred in h4.
rewrite h0 in h3; contradiction.
apply eq_cA_cA_1; assumption.
Qed.

(* ================================ *)

Theorem left_uniqueness : forall (x:dart)(y:dart),
  exd m x -> exd m y -> expf m d x -> expf m d y ->
  (forall (k:dim), ~ expf m (cA m k x) y) ->
  left_dart m x p -> left_dart m y p -> x = y.
Proof.
intros x y hx hy hdx hdy hk [hx1 hx2] [hy1 hy2].
elim (eq_dart_dec x y); intro heq; try trivial.
assert False; [idtac|tauto].
(* == == == *)
assert (t1: exd m (cA m one x)).
 apply exd_cA; assumption.
assert (t2: exd m (cA m one y)).
 apply exd_cA; assumption.
assert (t3: exd m (cA m zero x)).
 apply exd_cA; assumption.
assert (t4: exd m (cA m zero y)).
 apply exd_cA; assumption.
assert (t5: exd m (cA m zero (cA m one x))).
 apply exd_cA; assumption.
assert (t6: exd m (cA m zero (cA m one y))).
 apply exd_cA; assumption.
(* == == == *)
unfold invisible_succ in hx1, hy1.
unfold visible_succ in hx2, hy2.
unfold cF_1 in hx1, hy1.
rewrite H2 in hx1; try assumption.
rewrite H2 in hy1; try assumption.
(* == == == *)
assert (px1: fpoint m (cA m one x) = fpoint m x).
 apply cA_one_fpoint; assumption.
assert (py1: fpoint m (cA m one y) = fpoint m y).
 apply cA_one_fpoint; assumption.
rewrite px1 in hx1; rewrite py1 in hy1.
(**)
assert (px2: fpoint m x <> fpoint m (cA m zero x)).
 intro h; rewrite h in hx2. apply ccw_axiom_1 in hx2.
 apply axiom_orientation_5 in hx2. apply hx2.
 unfold align, det; ring.
assert (px3: fpoint m x <> fpoint m (cA m zero (cA m one x))).
 intro h; rewrite h in hx1. apply ccw_axiom_1 in hx1.
 apply axiom_orientation_5 in hx1. apply hx1.
 unfold align, det; ring.
assert (py2: fpoint m y <> fpoint m (cA m zero y)).
 intro h; rewrite h in hy2. apply ccw_axiom_1 in hy2.
 apply axiom_orientation_5 in hy2. apply hy2.
 unfold align, det; ring.
assert (py3: fpoint m y <> fpoint m (cA m zero (cA m one y))).
 intro h; rewrite h in hy1. apply ccw_axiom_1 in hy1.
 apply axiom_orientation_5 in hy1. apply hy1.
 unfold align, det; ring.
(**)
assert (hp0: fpoint m x <> fpoint m y).
 apply H6; try assumption. intro h.
 apply expv_x_y_eq_x_cA_m_one_x in h; try assumption.
 elimination h. contradiction.
 apply hk with one; rewrite h.
 apply expf_refl; assumption.
assert (hp1: fpoint m x <> fpoint m (cA m zero y)).
 apply H6; try assumption. intro h.
 apply expv_x_y_eq_x_cA_m_one_x in h; try assumption.
 elimination h. apply hk with one; rewrite h.
 rewrite eq_cA_cA_1; try assumption.
 rewrite eq_cA_cA_1; try assumption.
 fold (cF m y); apply expf_symm.
 unfold expf, MF.expo; repeat split; try assumption.
 exists 1; simpl; tauto.
 rewrite h in px1; rewrite px1 in hy2.
 rewrite h in hx1; rewrite H2 in hx1; try assumption.
 apply ccw_axiom_2 in hx1; contradiction.
assert (hp2: fpoint m x <> fpoint m (cA m zero (cA m one y))).
 apply H6; try assumption. intro h.
 apply expv_x_y_eq_x_cA_m_one_x in h; try assumption.
 elimination h.
 rewrite <- h in hy1; rewrite h in hx2 at 2.
 rewrite H2 in hx2; try assumption. rewrite py1 in hx2.
 apply ccw_axiom_2 in hx2; contradiction.
 rewrite h in px1; rewrite px1 in hy1.
 rewrite h in hx1; rewrite H2 in hx1; try assumption.
 rewrite py1 in hx1. apply ccw_axiom_1 in hy1.
 apply ccw_axiom_2 in hx1; contradiction.
assert (hp3: fpoint m y <> fpoint m (cA m zero x)).
 apply H6; try assumption. intro h.
 apply expv_x_y_eq_x_cA_m_one_x in h; try assumption.
 elimination h. apply hk with one; rewrite h.
 apply expf_symm; apply expf_cA_cA; assumption.
 rewrite h in py1; rewrite py1 in hx2.
 rewrite h in hy1; rewrite H2 in hy1; try assumption.
 apply ccw_axiom_2 in hy1; contradiction.
assert (hp4: fpoint m y <> fpoint m (cA m zero (cA m one x))).
 apply H6; try assumption. intro h.
 apply expv_x_y_eq_x_cA_m_one_x in h; try assumption.
 elimination h. rewrite h in hy2.
 rewrite H2 in hy2; try assumption. rewrite px1 in hy2.
 apply ccw_axiom_2 in hy2; contradiction.
 rewrite h in py1; rewrite py1 in hx1.
 rewrite h in hy1; rewrite H2 in hy1; try assumption.
 rewrite px1 in hy1. apply ccw_axiom_1 in hx1.
 apply ccw_axiom_2 in hy1; contradiction.
(**)
assert (px4: fpoint m (cA m zero x) <> fpoint m (cA m zero (cA m one x))).
 intro h. apply not_eq_sym in hp3.
 generalize (H8 x y hdx hy hp0 hp3).
 intro h0; apply ccw_axiom_2 in h0; apply h0.
 rewrite h; apply ccw_axiom_1; clear h h0.
 assert (t7: (cA m one x) = (cA m zero (cA m zero (cA m one x)))).
  rewrite H2; try assumption. tauto.
 rewrite t7 in px1; rewrite <- px1.
 assert (t8: expf m d (cA m zero (cA m one x))).
  apply expf_trans with x. apply hdx. fold (cF_1 m x).
  generalize (expf_Iter_cF_1 m x 1 H1 hx); simpl Iter; tauto.
 unfold is_convex in H8; apply H8; try assumption.
 apply not_eq_sym; exact hp4. rewrite px1; exact hp0.
assert (py4: fpoint m (cA m zero y) <> fpoint m (cA m zero (cA m one y))).
 intro h. apply not_eq_sym in hp1. apply not_eq_sym in hp0.
 generalize (H8 y x hdy hx hp0 hp1).
 intro h0; apply ccw_axiom_2 in h0; apply h0.
 rewrite h; apply ccw_axiom_1; clear h h0.
 assert (t7: (cA m one y) = (cA m zero (cA m zero (cA m one y)))).
  rewrite H2; try assumption. tauto.
 rewrite t7 in py1; rewrite <- py1.
 assert (t8: expf m d (cA m zero (cA m one y))).
  apply expf_trans with y. apply hdy. fold (cF_1 m y).
  generalize (expf_Iter_cF_1 m y 1 H1 hy); simpl Iter; tauto.
 unfold is_convex in H8; apply H8; try assumption.
 apply not_eq_sym; exact hp2. rewrite py1; exact hp0.
(* == == == *)
assert (h1: ccw (fpoint m x) p (fpoint m y)).
 apply ccw_axiom_5_bis with (fpoint m (cA m zero x))
 (fpoint m (cA m zero (cA m one x))); try assumption.
 do 2 apply ccw_axiom_1; apply H8; assumption.
 assert (t7: (cA m one x) = (cA m zero (cA m zero (cA m one x)))).
  rewrite H2; try assumption. tauto.
 rewrite t7 in px1; rewrite <- px1.
 assert (t8: expf m d (cA m zero (cA m one x))).
  apply expf_trans with x. apply hdx. fold (cF_1 m x).
  generalize (expf_Iter_cF_1 m x 1 H1 hx); simpl Iter; tauto.
 unfold is_convex in H8; apply H8; try assumption.
 apply not_eq_sym; exact hp4. rewrite px1; exact hp0.
 apply H8; try assumption. apply not_eq_sym; exact hp3.
assert (h2: ccw (fpoint m y) p (fpoint m x)).
 apply ccw_axiom_5_bis with (fpoint m (cA m zero y))
 (fpoint m (cA m zero (cA m one y))); try assumption.
 do 2 apply ccw_axiom_1; apply H8; assumption.
 assert (t7: (cA m one y) = (cA m zero (cA m zero (cA m one y)))).
  rewrite H2; try assumption. tauto.
 rewrite t7 in py1; rewrite <- py1.
 assert (t8: expf m d (cA m zero (cA m one y))).
  apply expf_trans with y. apply hdy. fold (cF_1 m y).
  generalize (expf_Iter_cF_1 m y 1 H1 hy); simpl Iter; tauto.
 unfold is_convex in H8; apply H8; try assumption.
 apply not_eq_sym; exact hp2.
 rewrite py1; apply not_eq_sym; exact hp0.
 apply H8; try assumption.
 apply not_eq_sym; exact hp0. apply not_eq_sym; exact hp1.
(* == == *)
do 2 apply ccw_axiom_1 in h2.
apply ccw_axiom_2 in h2; contradiction.
Qed.

(* ================================ *)

Lemma not_invisible_visible_succ :
  forall (x:dart), eqc m d x ->
  ~ invisible_succ m x p -> visible_succ m x p.
Proof.
intros x hx H.
unfold visible_succ.
unfold invisible_succ in H.
apply axiom_orientation_7 in H.
elimination H. assumption.
assert False; [idtac|tauto].
apply H10 with x (cA m zero x).
apply eqc_exd_exd in hx; tauto.
apply exd_cA; apply eqc_exd_exd in hx; tauto.
generalize (H5 x (cA m zero x)).
intro h; destruct h as [h1 h2].
apply eqc_exd_exd in hx; tauto.
apply exd_cA; apply eqc_exd_exd in hx; tauto.
apply H3; assumption. apply h2.
unfold expe, MA0.MfcA.expo; split.
apply eqc_exd_exd in hx; tauto.
exists 1; simpl; trivial.
auto with myorientation.
Qed.

Lemma not_visible_invisible_succ :
  forall (x:dart), eqc m d x ->
  ~ visible_succ m x p -> invisible_succ m x p.
Proof.
intros x hx H.
unfold invisible_succ.
unfold visible_succ in H.
apply axiom_orientation_7 in H.
elimination H. assumption.
assert False; [idtac|tauto].
apply H10 with x (cA m zero x).
apply eqc_exd_exd in hx; tauto.
apply exd_cA; apply eqc_exd_exd in hx; tauto.
generalize (H5 x (cA m zero x)).
intro h; destruct h as [h1 h2].
apply eqc_exd_exd in hx; tauto.
apply exd_cA; apply eqc_exd_exd in hx; tauto.
apply H3; assumption. apply h2.
unfold expe, MA0.MfcA.expo; split.
apply eqc_exd_exd in hx; tauto.
exists 1; simpl; trivial.
auto with myorientation.
Qed.

(* ================================ *)

Definition Pnotleft (m0:fmap)(d0:dart)(p0:point) :=
  ~ left_dart m0 d0 p0.

Lemma search_left_nil_v1P : l = nil ->
  (forall (x:dart), expf m d x -> Pnotleft m x p).
Proof.
intros h x hx.
apply P_Iter_cF_expf with d; try assumption.
intros i hi; unfold Pnotleft.
apply left_eq_nil_all_not_left with 0; intuition.
Qed.

Lemma search_left_nil_v1 : l = nil ->
  (forall (x:dart), expf m d x -> ~ left_dart m x p).
Proof.
apply search_left_nil_v1P.
Qed.

(* ===== *)

Lemma not_left_dart_until_i_invisible_i : 
  forall (x:dart)(i:nat), expf m d x -> invisible_succ m x p ->
  (forall (j:nat), j <= i -> ~ (left_dart m (Iter (cF m) j x) p)) ->
  invisible_succ m (Iter (cF m) i x) p.
Proof.
intros x i Hf Hinv H.
induction i.
 (* Cas 1 = 0 *)
 simpl in *; assumption.
 (* Cas 2 = S i *)
 assert (h1: ~ left_dart m (Iter (cF m) (S i) x) p).
  apply H; lia.
 assert (h2: invisible_succ m (Iter (cF m) i x) p).
  apply IHi; intros j hj; apply H; lia.
 unfold left_dart in h1; simpl in *; clear H IHi.
 pose (xi := Iter (cF m) i x). fold xi; fold xi in h1, h2.
 elim (invisible_succ_dec m (cF m xi) p); try trivial.
 intro h; assert False; [idtac|tauto].
 apply h1; clear h1; split.
 rewrite cF_1_cF; try assumption.
 apply exd_Iter_cF; try assumption.
 apply expf_symm in Hf.
 unfold expf, MF.expo in Hf; tauto.
 apply not_invisible_visible_succ; try assumption.
 apply eqc_trans with x.
 apply expf_eqc; try assumption.
 unfold expf in Hf; tauto.
 apply eqc_eqc_cF; try assumption.
 apply eqc_Iter_cF; try assumption.
 apply expf_symm in Hf.
 unfold expf, MF.expo in Hf; tauto.
Qed.

Lemma not_left_dart_until_i_visible_i : 
  forall (x:dart)(i:nat), expf m d x -> visible_succ m x p ->
  (forall (j:nat), j <= i -> ~ (left_dart m (Iter (cF_1 m) j x) p)) ->
  visible_succ m (Iter (cF_1 m) i x) p.
Proof.
intros x i Hf Hinv H.
induction i.
 (* Cas 1 = 0 *)
 simpl in *; assumption.
 (* Cas 2 = S i *)
 assert (h1: ~ left_dart m (Iter (cF_1 m) i x) p).
  apply H; lia.
 assert (h2: visible_succ m (Iter (cF_1 m) i x) p).
  apply IHi; intros j hj; apply H; lia.
 unfold left_dart in h1; simpl in *; clear H IHi.
 pose (xi := Iter (cF_1 m) i x). fold xi; fold xi in h1, h2.
 elim (visible_succ_dec m (cF_1 m xi) p); try trivial.
 intro h; assert False; [idtac|tauto].
 apply h1; clear h1; split; try assumption.
 apply not_visible_invisible_succ; try assumption.
 apply eqc_trans with x.
 apply expf_eqc; try assumption.
 unfold expf in Hf; tauto.
 assert (H: cF_1 m xi = Iter (cF_1 m) (S i) x).
 simpl; trivial. rewrite H; clear H.
 apply eqc_Iter_cF_1; try assumption.
 apply expf_symm in Hf.
 unfold expf, MF.expo in Hf; tauto.
Qed.

(* ===== *)

Lemma search_left_nil_v2 : l = nil ->
  (forall (x:dart), expf m d x -> invisible_succ m x p) \/
  (forall (x:dart), expf m d x -> visible_succ m x p).
Proof.
intro h.
elim (invisible_succ_dec m d p);
intro h0; [left|right]; intros x hx.
assert (t0: exists i:nat, Iter (cF m) i d = x).
unfold expf, MF.expo, MF.f, McF.f in hx; tauto.
elim t0; clear t0; intros i hi; rewrite <- hi.
apply not_left_dart_until_i_invisible_i.
apply expf_refl; assumption. assumption.
intros j hj.
pose (dj := Iter (cF m) j d). fold dj.
apply search_left_nil_v1; try assumption.
unfold dj.
unfold expf; split; try assumption.
unfold MF.expo, MF.f, McF.f; split.
assumption. exists j; trivial.
apply not_invisible_visible_succ in h0.
assert (t0: exists i:nat, Iter (cF_1 m) i d = x).
apply expf_symm in hx.
unfold expf, MF.expo, MF.f, McF.f in hx.
destruct hx as [h1 [h2 h3]]; elim h3; clear h3.
intros i hi; rewrite <- hi; exists i.
apply Iter_cF_1_Iter_cF; assumption.
elim t0; clear t0; intros i hi; rewrite <- hi.
apply not_left_dart_until_i_visible_i.
apply expf_refl; assumption. assumption.
intros j hj.
pose (dj := Iter (cF_1 m) j d). fold dj.
apply search_left_nil_v1; try assumption.
apply expf_Iter_cF_1; assumption.
apply eqc_refl; assumption.
Qed.

(* ===== *)

Lemma not_all_visible_in_face_bis :
  ~ (forall (i:nat), i < degreef m d -> visible_succ m (Iter (cF m) i d) p).
Proof. intro h.
(**)
elim (eq_dart_dec (degreef m d) 1); intro hd.
assert (t0: 0 < degreef m d). lia.
generalize (h 0 t0); clear t0; simpl.
unfold visible_succ; intro h1.
generalize (MF.degree_per m d H1 Hd).
replace MF.degree with degreef; try tauto.
unfold MF.f, McF.f, cF; rewrite hd; simpl.
rewrite <- eq_cA_cA_1; try assumption.
rewrite <- eq_cA_cA_1; try assumption.
replace (fpoint m (cA m zero d)) with
 (fpoint m (cA m one (cA m zero d))) in h1.
intro h2; rewrite h2 in h1.
apply axiom_orientation_5 in h1.
apply h1; unfold align, det; ring.
apply cA_one_fpoint; try assumption.
apply exd_cA; assumption.
(**)
assert (h0: forall (da:dart)(i:nat), 0 < i -> expf m d da ->
 ccw (fpoint m da) p (fpoint m (Iter (cF m) i da))).
intros da i hi hda; induction i.
assert False; [lia|tauto].
elim (eq_dart_dec i 0).
intro heq. subst i; simpl; clear hi IHi.
unfold expf in hda; destruct hda as [h1 h2].
apply MF.expo_expo1 in h2; try assumption.
unfold MF.expo1 in h2; destruct h2 as [h2 h3].
elim h3; clear h3; intros j [h3 h4].
unfold MF.f, McF.f in h4.
rewrite MF.upb_eq_degree in h3; try assumption.
replace MF.degree with degreef in h3; try tauto.
generalize (h j h3); rewrite h4.
unfold visible_succ; unfold cF.
rewrite <- eq_cA_cA_1; try assumption.
rewrite <- eq_cA_cA_1; try assumption.
replace (fpoint m (cA m zero da)) with
 (fpoint m (cA m one (cA m zero da))).
tauto. apply cA_one_fpoint; try assumption.
apply exd_cA; try assumption.
rewrite <- h4; apply exd_Iter_cF; assumption.
intro heq. assert (t0: 0 < i). lia. clear hi heq.
generalize (IHi t0); clear IHi t0; intro h0.
simpl. set (di := (Iter (cF m) i da)). fold di in h0.
assert (t1: exd m da). apply expf_symm in hda.
unfold expf, MF.expo in hda; tauto.
assert (t2: exd m di). unfold di.
apply exd_Iter_cF; try assumption.
do 2 apply ccw_axiom_1; apply ccw_axiom_4 with (fpoint m di).
(**)
replace (fpoint m (cF m di)) with (fpoint m (cA m zero di)).
apply H8; try assumption.
apply expf_trans with da. exact hda.
unfold expf, MF.expo; repeat split; try assumption.
exists i; unfold MF.f, McF.f; tauto.
intro t0; rewrite t0 in h0.
apply axiom_orientation_5 in h0.
apply h0; unfold align, det; ring.
apply H6; try assumption.
apply exd_cA; assumption.
intro t0; apply expv_x_y_eq_x_cA_m_one_x in t0; try assumption.
elimination t0. apply H0.
apply expf_trans with da. exact hda.
rewrite <- t0; apply expf_d0_x0; try assumption.
apply expf_symm; apply expf_trans with da. exact hda.
unfold expf, MF.expo; repeat split; try assumption.
exists i; unfold MF.f, McF.f; tauto.
rewrite <- t0 in h0.
replace (fpoint m (cA m one (cA m zero di))) with
 (fpoint m (cA m zero di)) in h0.
assert (ti: expf m d di).
apply expf_trans with da. exact hda.
unfold expf, MF.expo; repeat split; try assumption.
exists i; unfold MF.f, McF.f; tauto.
unfold expf in ti; destruct ti as [h1 h2].
apply MF.expo_expo1 in h2; try assumption.
unfold MF.expo1 in h2; destruct h2 as [h2 h3].
elim h3; clear h3; intros j [h3 h4].
unfold MF.f, McF.f in h4.
rewrite MF.upb_eq_degree in h3; try assumption.
replace MF.degree with degreef in h3; try tauto.
generalize (h j h3); rewrite h4.
unfold visible_succ; intro h5.
do 2 apply ccw_axiom_1 in h5.
apply ccw_axiom_2 in h5. contradiction.
apply eq_sym; apply cA_one_fpoint; try assumption.
apply exd_cA; try assumption. unfold cF.
rewrite <- eq_cA_cA_1; try assumption.
rewrite <- eq_cA_cA_1; try assumption.
apply eq_sym; apply cA_one_fpoint; try assumption.
apply exd_cA; try assumption.
(**)
apply ccw_axiom_1; exact h0.
(**)
assert (ti: expf m d di).
apply expf_trans with da. exact hda.
unfold expf, MF.expo; repeat split; try assumption.
exists i; unfold MF.f, McF.f; tauto.
unfold expf in ti; destruct ti as [h1 h2].
apply MF.expo_expo1 in h2; try assumption.
unfold MF.expo1 in h2; destruct h2 as [h2 h3].
elim h3; clear h3; intros j [h3 h4].
unfold MF.f, McF.f in h4.
rewrite MF.upb_eq_degree in h3; try assumption.
replace MF.degree with degreef in h3; try tauto.
generalize (h j h3); rewrite h4.
unfold visible_succ; intro h5.
apply ccw_axiom_1 in h5. unfold cF.
rewrite <- eq_cA_cA_1; try assumption.
rewrite <- eq_cA_cA_1; try assumption.
rewrite cA_one_fpoint; try assumption.
apply exd_cA; try assumption.
(**)
assert (t1: 0 < (degreef m d) - 1).
generalize (MF.degree_pos m d Hd).
replace MF.degree with degreef; try tauto. lia.
assert (t2: expf m d d). apply expf_refl; assumption.
generalize (h0 d ((degreef m d) - 1) t1 t2).
replace (Iter (cF m) (degreef m d - 1) d) with (cF_1 m d).
unfold cF_1; intro h1.
assert (t3: 0 < 1). lia.
assert (t4: expf m d (cF_1 m d)).
generalize (expf_Iter_cF_1 m d 1 H1 Hd); simpl; tauto.
generalize (h0 (cF_1 m d) 1 t3 t4).
simpl; rewrite cF_cF_1; try assumption.
unfold cF_1; intro h2.
do 2 apply ccw_axiom_1 in h2.
apply ccw_axiom_2 in h2. contradiction.
rewrite <- MF.Iter_f_f_1; try assumption.
simpl; unfold MF.f_1, McF.f_1.
rewrite MF.degree_per; try assumption.
tauto. lia.
Qed.

Lemma not_all_visible_in_face :
  ~ (forall (x:dart), expf m d x -> visible_succ m x p).
Proof.
intro h. apply not_all_visible_in_face_bis.
intros i hi; apply h.
unfold expf, MF.expo; repeat split; try assumption.
exists i; unfold MF.f, McF.f; tauto.
Qed.

Theorem left_nil_all_invisible : l = nil ->
  (forall (da:dart), expf m d da -> invisible_succ m da p).
Proof.
intros h x hx; apply search_left_nil_v2 in h.
elimination h. apply h; assumption.
assert False; [idtac|tauto].
apply not_all_visible_in_face; assumption.
Qed.

(* ================================ *)

Lemma not_right_dart_until_i_visible_i : 
  forall (x:dart)(i:nat), expf m d x -> visible_succ m x p ->
  (forall (j:nat), j <= i -> ~ (right_dart m (cA m zero (Iter (cF m) j x)) p)) ->
  visible_succ m (Iter (cF m) i x) p.
Proof.
intros x i Hf Hvis H.
induction i.
 (* Cas 1 = 0 *)
 simpl in *; assumption.
 (* Cas 2 = S i *)
 assert (h1: ~ right_dart m (cA m zero (Iter (cF m) i x)) p).
  apply H; lia.
 assert (h2: visible_succ m (Iter (cF m) i x) p).
  apply IHi; intros j hj; apply H; lia.
 clear H IHi.
 unfold right_dart in h1; simpl in *.
 elim (visible_succ_dec m (cF m (Iter (cF m) i x)) p); try trivial.
 intro h; assert False; [idtac|tauto].
 apply h1; clear h1; split.
 apply visible_succ_pred; try assumption.
 apply exd_Iter_cF; try assumption.
 apply expf_symm in Hf.
 unfold expf, MF.expo in Hf; tauto.
 unfold cF_1.
 (*pattern (cA m zero).*)
 rewrite (eq_cA_cA_1 m one (cA m zero (Iter (cF m) i x))); try assumption.
 rewrite (eq_cA_cA_1 m zero (Iter (cF m) i x)); try assumption.
(* pattern (cA m zero); rewrite eq_cA_cA_1' with (k:=zero); try assumption.
pattern (cA m zero); repeat rewrite eq_cA_cA_1; try assumption.*)
fold (cF m (Iter (cF m) i x)).

 apply invisible_succ_pred; try assumption.
 apply -> exd_cF; try assumption.
 apply exd_Iter_cF; try assumption.
 apply expf_symm in Hf.
 unfold expf, MF.expo in Hf; tauto.
 apply not_visible_invisible_succ; try assumption.
 cut (expf m d (cF m (Iter (cF m) i x))).
 intros [ha hb]. apply expf_eqc; try assumption.
 apply expf_trans with (Iter (cF m) i x).
 apply expf_trans with x; try assumption.
 unfold expf, MF.expo, MF.f, McF.f.
 repeat split; try assumption.
 apply expf_symm in Hf.
 unfold expf, MF.expo in Hf; tauto.
 exists i; trivial.
 unfold expf, MF.expo, MF.f, McF.f.
 repeat split; try assumption.
 apply exd_Iter_cF; try assumption.
 apply expf_symm in Hf.
 unfold expf, MF.expo in Hf; tauto.
 exists 1; simpl; trivial.
Qed.

(* ===== *)

Definition prop_dec (m0:fmap)(d0:dart)(p0:point)(P:fmap->dart->point->nat->Prop) :=
  forall (i:nat), {P m0 d0 p0 i} + {~ P m0 d0 p0 i}.

Lemma exist_forall_i :
  forall (m0:fmap)(d0:dart)(p0:point)(P:fmap->dart->point->nat->Prop)(k:nat),
  prop_dec m0 d0 p0 P -> {exists i:nat, (i < k) /\ P m0 d0 p0 i} + {forall i:nat, ~(i < k) \/ ~ P m0 d0 p0 i}.
Proof.
intros m0 d0 p0 P k Hdec.
induction k.
right; intro i; left; lia.
elim IHk; clear IHk.
intro IHk; left.
elim IHk; clear IHk; intros x0 IHk.
exists x0; split; [lia|tauto].
intro IHk.
generalize (Hdec k); clear Hdec.
intro H; elim H; clear H.
intro H; left.
exists k; split; [lia|tauto].
intro H; right; intro i.
elim (eq_nat_dec i k); intro Heq.
rewrite Heq in *; tauto.
generalize (IHk i); intro h0; elim h0.
intro h; left; lia.
intro h; right; assumption.
Qed.

Definition right_dart_cF (m0:fmap)(d0:dart)(p0:point)(i:nat) : Prop :=
  right_dart m0 (cA m0 zero (Iter (cF m0) i d0)) p0.

Lemma right_dart_cF_dec : forall (m0:fmap)(d0:dart)(p0:point),
  prop_dec m0 d0 p0 right_dart_cF. 
Proof.
unfold prop_dec, right_dart_cF.
intros m0 d0 p0 i; apply right_dart_dec.
Qed.

(* ===== *)

Lemma exd_left_dart_exd_right_dart_i :
  l <> nil ->
  exists i:nat, i < (MF.Iter_upb m l) /\ right_dart m (cA m zero (Iter (cF m) i l)) p.
Proof.
intro Hleft.
generalize (exist_forall_i m l p right_dart_cF (MF.Iter_upb m l) (right_dart_cF_dec m l p)).
intro H; elim H; clear H; intro H; unfold right_dart_cF in *; [intuition|idtac].
assert False; [idtac|tauto].
cut (expf m d l). cut (visible_succ m l p). intros t1 t2.
generalize (not_right_dart_until_i_visible_i l ((MF.Iter_upb m l) - 1) t2 t1).
intro h0; simpl in *.
assert (H01 : Iter (cF m) ((MF.Iter_upb m l) - 1) l = cF_1 m l).
 rewrite <- MF.Iter_f_f_1; try assumption.
 rewrite MF.Iter_upb_period; try assumption.
 simpl in *; tauto.
 apply exdleft; assumption.
 apply exdleft; assumption.
 assert (0 < (MF.Iter_upb m l)); [idtac|lia].
  apply MF.upb_pos; apply exdleft; assumption.
rewrite H01 in h0; clear H01.
cut (visible_succ m (cF_1 m l) p).
generalize (invisibleleft m d p 0 H1 Hd Hleft).
intro h. apply invisible_not_visible_succ in h.
unfold l; contradiction.
apply h0; intros j Hj; generalize (H j); clear H h0.
intro H; elim H; clear H; intro H; try assumption.
assert (0 < (MF.Iter_upb m l)); [idtac|lia].
 apply MF.upb_pos; apply exdleft; assumption.
apply visibleleft; assumption.
apply expfleft; assumption.
Qed.

Theorem exd_left_dart_exd_right_dart :
  l <> nil -> r <> nil.
Proof.
intro h. generalize h; intro h0.
apply exd_left_dart_exd_right_dart_i in h.
elim h; clear h; intros i [h1 h2].
apply exists_right_r_neq_nil; try assumption.
apply exdleft; try assumption.
exists i; split; try assumption.
split. lia.
rewrite <- MF.upb_eq_degree; try assumption.
apply exdleft; assumption.
Qed.

(* ================================ *)

(* ================================ *)

(*
Lemma exd_left_right : l <> nil <-> r <> nil.
Proof. split.
apply exd_left_dart_exd_right_dart.
apply exd_right_dart_exd_left_dart.
Qed.
*)

End leftright_sec.
