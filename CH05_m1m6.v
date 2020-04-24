(* ================================ *)
(* ========= CH05_m1m6.v ========== *)
(* ================================ *)

Require Export CH04_leftright.
Require Import Psatz.
(* *** In this section, we assume : (l <> nil) *** *)

Section CHID_sec.

Variables (md:mapdart)(x:dart)(t:tag)(p:point)(max:dart).

Let m := fst md.
Let d := snd md.
Let l := search_left m d p 0.
Let r := search_right m l p 0.

Let l0 := cA m zero l.
Let r0 := cA_1 m zero r.

Let l1 := cA m one l.
Let r1 := cA m one r.

Let m1 := Split m zero l l0.
Let m2 := if (eq_dart_dec l0 r) then m1 else Split m1 zero r0 r.
Let m3 := (I (I m2 x t p) max t p).
Let m4 := Merge m3 one max x.
Let m5 := Merge m4 zero l max.
Let m6 := Merge m5 zero x r.

Hypothesis H1 : inv_hmap m.
Hypothesis H2 : inv_gmap m.
Hypothesis H3 : inv_poly m d.
Hypothesis H4 : planar m.

Hypothesis H5 : is_well_emb m.
Hypothesis H6 : is_neq_point m.
Hypothesis H7 : is_noalign m.
Hypothesis H8 : is_convex m d.

Hypothesis H9 : exd m d.
Hypothesis H10 : l <> nil.

Hypothesis H11 : ~ exd m x.
Hypothesis H12 : ~ exd m max.
Hypothesis H13 : x <> nil.
Hypothesis H14 : max <> nil.
Hypothesis H15 : x <> max.

Hypothesis H16 : forall (da:dart), exd m da -> fpoint m da <> p.
Hypothesis H17 : forall (da:dart)(db:dart),
  let pda := fpoint m da in let pdb := fpoint m db in
  exd m da -> exd m db -> pda <> pdb -> ~ align p pda pdb.

Hypothesis H0 : ~ expf m d (cA m zero d).

(* ================================ *)

Lemma expf_expof : forall (m0:fmap)(x0:dart)(y0:dart),
  expf m0 x0 y0 <-> inv_hmap m0 /\ expof m0 x0 y0.
Proof.
intros m0 x0 y0; split; intro h.
unfold expf in h; split; tauto.
unfold expf; unfold expof in h; exact h.
Qed.

(* ================================ *)
(* ========== ########## ========== *)
(* ================================ *)

Lemma exd_left : exd m l.
Proof.
apply exdleft; assumption.
Qed.

Lemma exd_right : exd m r.
Proof.
apply exdright; try assumption. apply exd_left.
apply exd_left_dart_exd_right_dart; assumption.
Qed.

Lemma exd_l1 : exd m l1.
Proof.
apply exd_cA. exact H1. apply exd_left.
Qed.

Lemma exd_r1 : exd m r1.
Proof.
apply exd_cA. exact H1. apply exd_right.
Qed.

(* ===== *)

Lemma neq_l_l0 : l <> l0.
Proof.
unfold l0; apply H3.
apply eqcleft; assumption.
Qed.

Lemma neq_r_r0 : r <> r0.
Proof.
unfold r0; rewrite <- eq_cA_cA_1; try assumption.
apply H3; apply eqc_trans with l.
apply eqcleft; assumption.
apply eqcright; try assumption. apply exd_left.
apply exd_left_dart_exd_right_dart; assumption.
Qed.

Lemma neq_l0_r0 : l0 <> r0.
Proof.
unfold l0, r0.
rewrite <- eq_cA_cA_1; try assumption.
apply -> bij_neq_cA; try assumption.
apply neq_left_right; try tauto.
apply exd_right. apply exd_left.
Qed.

Lemma eq_l0_r_r0_l : l0 = r <-> r0 = l.
Proof.
unfold l0, r0; split; intro h.
rewrite <- h; rewrite cA_1_cA; try tauto.
apply exd_left.
rewrite <- h; rewrite cA_cA_1; try tauto.
apply exd_right.
Qed.

Lemma neq_l_l1 : l <> l1.
Proof.
unfold l1; apply H3.
apply eqcleft; assumption.
Qed.

Lemma neq_r_r1 : r <> r1.
Proof.
unfold r1; apply H3; apply eqc_trans with l.
apply eqcleft; assumption.
apply eqcright; try assumption. apply exd_left.
apply exd_left_dart_exd_right_dart; assumption.
Qed.

Lemma neq_l_r1 : l <> r1.
Proof.
intro h.
generalize (visibleleft m d p 0 H1 H9 H10).
fold l; unfold visible_succ; intro h1.
assert (t1: exd m l). apply exd_left.
assert (t2: r <> nil).
 apply exd_left_dart_exd_right_dart; assumption.
generalize (invisibleright m l p 0 H1 t1 t2).
fold r; unfold invisible_pred; intro h2.
unfold cF_1 in h2; fold r1 in h2.
rewrite cA_1_cA in h2; try assumption.
rewrite h in h1. apply ccw_axiom_2 in h1.
contradiction. apply exd_r1.
Qed.

Lemma neq_r_l1 : r <> l1.
Proof.
intro h.
generalize (invisibleleft m d p 0 H1 H9 H10).
fold l; unfold invisible_succ; intro h1.
unfold cF_1 in h1; fold l1 in h1.
rewrite H2 in h1; try assumption.
assert (t1: exd m l). apply exd_left.
assert (t2: r <> nil).
 apply exd_left_dart_exd_right_dart; assumption.
generalize (visibleright m l p 0 H1 t1 t2).
fold r; unfold visible_pred; intro h2.
rewrite <- eq_cA_cA_1 in h2; try assumption.
rewrite h in h2. apply ccw_axiom_2 in h1.
contradiction. apply exd_l1.
Qed.

Lemma neq_l1_r1 : l1 <> r1.
Proof.
intro h.
generalize (invisibleleft m d p 0 H1 H9 H10).
fold l; unfold invisible_succ; intro h1.
unfold cF_1 in h1; fold l1 in h1.
rewrite H2 in h1; try assumption.
assert (t1: exd m l). apply exd_left.
assert (t2: r <> nil).
 apply exd_left_dart_exd_right_dart; assumption.
generalize (invisibleright m l p 0 H1 t1 t2).
fold r; unfold invisible_pred; intro h2.
unfold cF_1 in h2; fold r1 in h2.
rewrite cA_1_cA in h2; try assumption.
rewrite h in h1; apply ccw_axiom_1 in h1.
apply ccw_axiom_2 in h1. contradiction.
apply exd_r1. apply exd_l1.
Qed.

(* ===== *)

Lemma cA_m_zero_l0 : cA m zero l0 = l.
Proof.
unfold l0; rewrite H2; trivial. apply exd_left.
Qed.

Lemma cA_m_zero_r0 : cA m zero r0 = r.
Proof.
unfold r0; rewrite cA_cA_1; trivial. apply exd_right.
Qed.

(* ================================ *)

Lemma not_expf_m_l_l0 : ~ expf m l l0.
Proof.
intro h; apply H0.
apply expf_trans with l.
apply expfleft; assumption.
apply expf_trans with l0.
assumption. unfold l0.
apply expf_d0_x0; try assumption.
apply expf_symm; apply expfleft; assumption.
Qed.

Lemma not_expf_m_r_r0 : ~ expf m r r0.
Proof.
intro h; apply not_expf_m_l_l0.
apply expf_trans with r0.
apply expfright; try assumption. apply exd_left.
apply exd_left_dart_exd_right_dart; assumption.
apply expf_trans with r.
apply expf_symm; assumption.
rewrite <- cA_m_zero_r0; unfold l0.
apply expf_d0_x0; try assumption.
apply expf_symm; apply expfright.
assumption. apply exd_left.
apply exd_left_dart_exd_right_dart; assumption.
Qed.

(* ===== *)

Lemma expf_m_l_cA_m_one_l0 : expf m l (cA m one l0).
Proof.
rewrite <- cA_m_zero_l0; apply expf_cA_cA; try assumption.
apply exd_cA; try assumption. apply exd_left.
Qed.

Lemma not_expf_m_l0_cA_m_one_l0 : ~ expf m l0 (cA m one l0).
Proof.
intro h; apply not_expf_m_l_l0.
apply expf_trans with (cA m one l0).
apply expf_m_l_cA_m_one_l0.
apply expf_symm; assumption.
Qed.

(* ===== *)

Lemma cracke_m_l_l0 : cracke m l l0.
Proof.
unfold cracke, MA0.crack. split.
apply neq_l_l0. unfold MA0.MfcA.expo. split.
apply exd_left. unfold MA0.MfcA.f, MA0.McAMd.f, Md0.kd.
exists 1; simpl. unfold l0. trivial.
Qed.

Lemma not_expe_m_l_r0 : l0 <> r -> ~ expe m l r0.
Proof. intro h.
unfold expe, MA0.MfcA.expo. intros [h1 h2].
elim h2; clear h2; intros i h2.
assert (h0: forall (i:nat), Iter (MA0.MfcA.f m) i l = l \/ Iter (MA0.MfcA.f m) i l = l0).
intro i0; induction i0.
unfold MA0.MfcA.f, MA0.McAMd.f, Md0.kd. simpl. left; trivial.
simpl. elimination IHi0; rewrite IHi0.
unfold MA0.MfcA.f, MA0.McAMd.f, Md0.kd. right; unfold l0; trivial.
unfold MA0.MfcA.f, MA0.McAMd.f, Md0.kd. left. unfold l0.
apply H2. apply exd_left.
generalize (h0 i); clear h0. intro h0; elimination h0.
rewrite h0 in h2. apply eq_sym in h2.
apply eq_l0_r_r0_l in h2. contradiction.
rewrite h0 in h2. apply neq_l0_r0; assumption.
Qed.

(* ================================ *)
(* ========== ########## ========== *)
(* ================================ *)

Lemma inv_hmap_m1 : inv_hmap m1.
Proof.
unfold m1.
apply inv_hmap_Split.
assumption.
Qed.

Lemma exd_m1 : forall (da:dart),
  exd m da <-> exd m1 da.
Proof.
intro da; split; unfold m1; intro h.
apply -> exd_Split; assumption.
apply <- exd_Split in h; assumption.
Qed.

Lemma cA_m1_zero_l : cA m1 zero l = l.
Proof.
unfold m1.
rewrite cA_Split; try assumption.
simpl; eqdartdec.
apply H2; apply exdleft; assumption.
unfold crack; simpl.
unfold cracke, MA0.crack; split.
apply H3; apply eqcleft; tauto.
unfold MA0.MfcA.expo; split.
apply exdleft; assumption.
unfold MA0.MfcA.f, MA0.McAMd.f, Md0.kd.
exists 1; simpl; trivial.
Qed.

Lemma cA_m1_zero_l0 : cA m1 zero l0 = l0.
Proof.
unfold m1.
rewrite cA_Split; try assumption.
simpl; elim eq_dart_dec; intro h.
assert False; [idtac|tauto].
apply H3 with zero l; try assumption.
apply eqcleft; tauto.
eqdartdec; trivial.
unfold crack; simpl.
unfold cracke, MA0.crack; split.
apply H3; apply eqcleft; tauto.
unfold MA0.MfcA.expo; split.
apply exdleft; assumption.
unfold MA0.MfcA.f, MA0.McAMd.f, Md0.kd.
exists 1; simpl; trivial.
Qed.

Lemma cA_m1_zero_da : forall (da:dart),
  exd m1 da -> da <> l -> da <> l0 ->
  cA m1 zero da = cA m zero da.
Proof.
intros da h1 h2 h3; unfold m1.
rewrite cA_Split; try assumption.
simpl; eqdartdec; trivial.
unfold crack; simpl.
unfold cracke, MA0.crack; split.
apply H3; apply eqcleft; tauto.
unfold MA0.MfcA.expo; split.
apply exdleft; assumption.
unfold MA0.MfcA.f, MA0.McAMd.f, Md0.kd.
exists 1; simpl; trivial.
Qed.

Lemma cA_m1_one_da : forall (da:dart),
  exd m1 da -> cA m1 one da = cA m one da.
Proof.
intros da h1; unfold m1.
rewrite cA_Split; try assumption.
simpl; trivial.
unfold crack; simpl.
unfold cracke, MA0.crack; split.
apply H3; apply eqcleft; tauto.
unfold MA0.MfcA.expo; split.
apply exdleft; assumption.
unfold MA0.MfcA.f, MA0.McAMd.f, Md0.kd.
exists 1; simpl; trivial.
Qed.

Lemma inv_gmap_m1 : inv_gmap m1.
Proof.
unfold inv_gmap; intros k da Hda; induction k.
(* k = zero *)
assert (exd m da). apply <- exd_m1; assumption.
elim (eq_dart_dec da l); intro h1.
subst da; do 2 rewrite cA_m1_zero_l; trivial.
elim (eq_dart_dec da l0); intro h2.
subst da; do 2 rewrite cA_m1_zero_l0; trivial.
rewrite cA_m1_zero_da; try assumption.
rewrite cA_m1_zero_da; try assumption.
apply H2; assumption.
apply -> exd_cA; [exact Hda | apply inv_hmap_m1].
rewrite cA_m1_zero_da; try assumption.
intro h; apply sym_eq in h.
apply subst_cA_cA_1 in h; try assumption.
rewrite <- eq_cA_cA_1 in h; try tauto.
rewrite cA_m1_zero_da; try assumption.
apply -> bij_neq_cA; try assumption.
apply exdleft; assumption.
(* k = one *)
assert (exd m da). apply <- exd_m1; assumption.
rewrite cA_m1_one_da; try assumption.
rewrite cA_m1_one_da; try assumption.
apply H2; try assumption.
apply -> exd_cA; [exact Hda | apply inv_hmap_m1].
Qed.

Lemma planar_m1 : planar m1.
Proof.
unfold m1.
apply planar_Split; try assumption.
apply H3.
apply eqcleft; assumption.
apply succ_or_succ_cA with d; try assumption.
apply eqcleft; intuition.
Qed. 

Open Scope Z_scope.

Lemma nd_m1 : nd m1 = nd m.
Proof.
unfold m1, Split. 
elim succ_dec; intro h1. 
elim succ_dec; intro h2. 
rewrite nd_B; simpl.
rewrite nd_B; tauto.
rewrite nd_B; tauto.
rewrite nd_B; tauto.
Qed.

Lemma ne_m1 : ne m1 = ne m + 1.
Proof.
unfold m1.
apply ne_Split0; try assumption.
unfold cracke, MA0.crack; split.
apply H3; apply eqcleft; tauto.
unfold MA0.MfcA.expo; split.
unfold l; apply exdleft; assumption.
unfold MA0.MfcA.f, MA0.McAMd.f, Md0.kd.
exists 1%nat; simpl; trivial.
Qed.

Lemma nv_m1 : nv m1 = nv m.
Proof.
unfold m1.
apply nv_Split0; try assumption.
unfold cracke, MA0.crack; split.
apply H3; apply eqcleft; tauto.
unfold MA0.MfcA.expo; split.
unfold l; apply exdleft; assumption.
unfold MA0.MfcA.f, MA0.McAMd.f, Md0.kd.
exists 1%nat; simpl; trivial.
Qed.

Lemma nf_m1 : nf m1 = nf m - 1.
Proof.
unfold m1.
rewrite nf_Split0; try assumption.
elim expf_dec; intro h; [idtac|ring].
assert False; [idtac|tauto].
apply H0; clear H0.
unfold l0 in h.
rewrite H2 in h.
apply expf_symm in h.
apply expf_trans with l.
apply expfleft; assumption.
apply expf_trans with (cA m zero l); try assumption.
apply expf_symm; apply expf_d0_x0; try assumption.
apply expfleft; assumption.
unfold l; apply exdleft; assumption.
unfold cracke, MA0.crack; split.
apply H3; apply eqcleft; tauto.
unfold MA0.MfcA.expo; split.
unfold l; apply exdleft; assumption.
unfold MA0.MfcA.f, MA0.McAMd.f, Md0.kd.
exists 1%nat; simpl; trivial.
Qed.

Lemma nc_m1 : nc m1 = nc m.
Proof.
unfold m1.
rewrite planar_nc_Split0; try assumption.
elim expf_dec; intro h; [idtac|ring].
assert False; [idtac|tauto].
apply H0; clear H0.
unfold l0 in h.
rewrite H2 in h.
apply expf_symm in h.
apply expf_trans with l.
apply expfleft; assumption.
apply expf_trans with (cA m zero l); try assumption.
apply expf_symm; apply expf_d0_x0; try assumption.
apply expfleft; assumption.
unfold l; apply exdleft; assumption.
unfold cracke, MA0.crack; split.
apply H3; apply eqcleft; tauto.
unfold MA0.MfcA.expo; split.
unfold l; apply exdleft; assumption.
unfold MA0.MfcA.f, MA0.McAMd.f, Md0.kd.
exists 1%nat; simpl; trivial.
Qed.

Open Scope nat_scope.

Lemma is_well_emb_m1 : is_well_emb m1.
Proof.
unfold is_well_emb; intros da db h1 h2 h3.
apply exd_m1 in h1; apply exd_m1 in h2.
unfold m1; split; intro h4.
(* expv da db *)
do 2 rewrite fpoint_Split.
apply -> expv_Split0 in h4; try assumption.
generalize (H5 da db h1 h2 h3).
intros [h5 h6]; apply h5; assumption.
(* expe da db *)
do 2 rewrite fpoint_Split.
apply expe_Split_expe in h4; try assumption.
generalize (H5 da db h1 h2 h3).
intros [h5 h6]; apply h6; assumption.
Qed.

Lemma is_neq_point_m1 : is_neq_point m1.
Proof.
unfold is_neq_point; intros da db h1 h2 h3.
apply exd_m1 in h1; apply exd_m1 in h2.
unfold m1; do 2 rewrite fpoint_Split.
apply H6; try assumption.
unfold m1 in h3.
rewrite -> expv_Split0 in h3; assumption.
Qed.

Lemma is_noalign_m1 : is_noalign m1.
Proof.
unfold is_noalign.
intros da db dc h1 h2 h3 h4 h5 h6.
apply exd_m1 in h1.
apply exd_m1 in h2.
apply exd_m1 in h3.
unfold m1 in *.
do 3 rewrite fpoint_Split in *.
apply H7; assumption.
Qed.

(* ================================ *)

Lemma expf_m1_l_l0 : expf m1 l l0.
Proof.
unfold m1. apply expf_symm.
unfold l0 at 2; rewrite <- cA_m_zero_l0 at 3.
apply expf_Split0_cracke; try assumption.
apply cracke_m_l_l0. fold l0; rewrite cA_m_zero_l0.
intro h; apply not_expf_m_l_l0.
apply expf_symm; assumption.
Qed.

Lemma expf_m1_d_d0 : expf m1 d (cA m zero d).
Proof.
unfold m1.
unfold expf; split. apply inv_hmap_m1.
apply (expof_Split0_CNS m l l0 d (cA m zero d) H1).
apply cracke_m_l_l0. assumption.
assert (h1: cA_1 m one l0 = cA m one l0).
rewrite eq_cA_cA_1; tauto.
elim expof_dec; intro h0.
assert False; [idtac|tauto].
rewrite h1 in h0; fold l0 in h0.
apply not_expf_m_l0_cA_m_one_l0.
apply expf_expof; split; assumption.
do 2 right; split; apply expf_symm.
apply expf_d0_x0; try assumption.
apply expfleft; assumption.
apply expf_trans with l.
apply expfleft; assumption.
rewrite h1. apply expf_m_l_cA_m_one_l0.
Qed.

Lemma expf_m1_r_r0 : expf m1 r r0.
Proof.
unfold m1.
unfold expf; split. apply inv_hmap_m1.
apply (expof_Split0_CNS m l l0 r r0 H1).
apply cracke_m_l_l0. apply exd_right.
assert (h1: cA_1 m one l0 = cA m one l0).
rewrite eq_cA_cA_1; tauto.
elim expof_dec; intro h0.
assert False; [idtac|tauto].
rewrite h1 in h0; fold l0 in h0.
apply not_expf_m_l0_cA_m_one_l0.
apply expf_expof; split; assumption.
right; left; split; apply expf_symm.
rewrite <- cA_m_zero_r0.
apply expf_d0_x0; try assumption. apply expf_symm.
apply expfright; try assumption. apply exd_left.
apply exd_left_dart_exd_right_dart; assumption.
apply expf_trans with l. apply expf_symm.
apply expfright; try assumption. apply exd_left.
apply exd_left_dart_exd_right_dart; assumption.
rewrite h1. apply expf_m_l_cA_m_one_l0.
Qed.

Lemma expf_m1_d_l : expf m1 d l.
Proof.
unfold m1. apply expf_Split0; try assumption.
apply cracke_m_l_l0. fold l0.
rewrite cA_m_zero_l0; intro h.
apply not_expf_m_l_l0; apply expf_symm; assumption.
apply expfleft; assumption.
Qed.

Lemma expf_m1_l_r0 : expf m1 l r0.
Proof.
unfold m1. apply expf_Split0; try assumption.
apply cracke_m_l_l0. fold l0.
rewrite cA_m_zero_l0; intro h.
apply not_expf_m_l_l0; apply expf_symm; assumption.
apply expfright; try assumption. apply exd_left.
apply exd_left_dart_exd_right_dart; assumption.
Qed.

(* ===== *)

Lemma expf_m1_r_r1 : expf m1 r r1.
Proof.
unfold m1.
unfold expf; split. apply inv_hmap_m1.
apply (expof_Split0_CNS m l l0 r r1 H1).
apply cracke_m_l_l0. apply exd_right.
assert (h1: cA_1 m one l0 = cA m one l0).
rewrite eq_cA_cA_1; tauto.
elim expof_dec; intro h0.
assert False; [idtac|tauto].
rewrite h1 in h0; fold l0 in h0.
apply not_expf_m_l0_cA_m_one_l0.
apply expf_expof; split; assumption.
right; left; split; apply expf_symm.
rewrite <- cA_m_zero_r0.
apply expf_d0_x0; try assumption. apply expf_symm.
apply expfright; try assumption. apply exd_left.
apply exd_left_dart_exd_right_dart; assumption.
apply expf_trans with (cA m zero r). apply expf_symm.
apply expf_cA_cA; try assumption. apply exd_right.
apply expf_trans with (cA m zero l0).
rewrite cA_m_zero_l0. replace (cA m zero r) with (cA_1 m zero r).
apply expf_symm. apply expfright; try assumption. apply exd_left.
apply exd_left_dart_exd_right_dart; assumption.
apply eq_sym; apply eq_cA_cA_1; assumption.
rewrite h1; apply expf_cA_cA; try assumption.
apply exd_cA; try assumption. apply exd_left.
Qed.

Lemma expf_m1_r0_cA_m_one_r0 : expf m1 r0 (cA m one r0).
Proof.
unfold m1.
unfold expf; split. apply inv_hmap_m1.
apply (expof_Split0_CNS m l l0 r0 (cA m one r0) H1).
apply cracke_m_l_l0. apply exd_cA_1. exact H1. apply exd_right.
assert (h1: cA_1 m one l0 = cA m one l0).
rewrite eq_cA_cA_1; tauto.
elim expof_dec; intro h0.
assert False; [idtac|tauto].
rewrite h1 in h0; fold l0 in h0.
apply not_expf_m_l0_cA_m_one_l0.
apply expf_expof; split; assumption.
do 2 right; split.
apply expf_trans with r. rewrite <- cA_m_zero_r0.
apply expf_d0_x0; try assumption.
apply expfright; try assumption. apply exd_left.
apply exd_left_dart_exd_right_dart; assumption.
unfold expf; split; try assumption.
unfold MF.expo. split. apply exd_right.
exists 1; simpl. unfold MF.f, McF.f, cF.
fold r0; rewrite eq_cA_cA_1; trivial.
apply expf_trans with l. apply expf_symm.
unfold expf; split; try assumption.
unfold MF.expo. split. apply exd_left.
exists 1; simpl. unfold MF.f, McF.f, cF.
unfold l0; rewrite eq_cA_cA_1; trivial.
apply expfright; try assumption. apply exd_left.
apply exd_left_dart_exd_right_dart; assumption.
Qed.

(* ===== *)

Lemma cracke_m1_r0_r : l0 <> r -> cracke m1 r0 r.
Proof.
intro h0. unfold cracke, MA0.crack. split.
apply not_eq_sym; apply neq_r_r0.
unfold MA0.MfcA.expo. split.
apply exd_m1; apply exd_cA_1. exact H1. apply exd_right.
unfold MA0.MfcA.f, MA0.McAMd.f, Md0.kd.
exists 1; simpl. rewrite cA_m1_zero_da.
unfold r0; rewrite cA_cA_1; trivial. apply exd_right.
apply exd_m1; apply exd_cA_1. exact H1. apply exd_right.
intro h; apply eq_l0_r_r0_l in h; contradiction.
apply not_eq_sym; apply neq_l0_r0.
Qed.

Lemma expe_m1_r0_r : l0 <> r -> expe m1 r0 r.
Proof.
intro h; unfold m1.
apply expe_Split0_CNS; try assumption.
apply cracke_m_l_l0.
apply exd_cA_1. assumption. apply exd_right.
do 2 right; split.
apply not_expe_m_l_r0; assumption.
unfold expe, MA0.MfcA.expo. split.
apply exd_cA_1. assumption. apply exd_right.
unfold MA0.MfcA.f, MA0.McAMd.f, Md0.kd.
exists 1; simpl. apply cA_m_zero_r0.
Qed.

(* ================================ *)

Lemma exists_i_Iter_cF_m_i_r1_l :
  exists i:nat, i < degreef m r1 /\ Iter (cF m) i r1 = l.
Proof.
assert (t1: exd m l). apply exd_left.
assert (t2: exd m r). apply exd_right.
assert (h: MF.expo1 m r1 l).
 apply MF.expo_expo1; try assumption.
 apply expf_trans with r0.
 apply expf_symm. unfold r0, r1.
 rewrite <- eq_cA_cA_1; try assumption.
 apply expf_cA_cA; try assumption.
 apply expf_symm. apply expfright; try assumption.
 apply exd_left_dart_exd_right_dart; assumption.
destruct h as [h1 [i [h2 h3]]]. exists i; split.
rewrite MF.upb_eq_degree in h2; try assumption.
unfold MF.f, McF.f in h3; assumption.
Qed.

Lemma Iter_cF_m1_i_r1_Iter_cF_m_i_r1 : forall (i:nat)(n:nat),
  i <= n -> (n < degreef m r1) -> (Iter (cF m) n r1 = l) -> 
  Iter (cF m1) i r1 = Iter (cF m) i r1.
Proof.
intros i n hle h1 h2; induction i.
simpl; tauto. simpl; rewrite IHi.
set (cFi := Iter (cF m) i r1).
unfold m1; rewrite cF_Split0; clear IHi.
elim eq_dart_dec; intro h3.
assert False; [idtac|tauto].
assert (t1: expf m l cFi).
 apply expf_trans with r1. apply expf_symm.
 unfold expf, MF.expo. repeat split.
 exact H1. apply exd_cA. exact H1. apply exd_right.
 exists n. unfold MF.f, McF.f. exact h2.
 unfold expf, MF.expo. repeat split.
 exact H1. apply exd_cA. exact H1. apply exd_right.
 exists i. unfold MF.f, McF.f. unfold cFi. tauto.
assert (t2: ~ expf m l l0). apply not_expf_m_l_l0.
unfold l0 in t2; rewrite h3 in t2. contradiction.
elim eq_dart_dec; intro h4.
assert False; [idtac|tauto].
unfold cFi in h4; rewrite cA_m_zero_l0 in h4.
rewrite <- h2 in h4. assert (t0: n = i).
 apply MF.degree_unicity with m r1; try assumption.
 apply exd_cA. exact H1. apply exd_right.
 replace MF.degree with degreef; try tauto. omega.
rewrite t0 in hle; omega. tauto. exact H1.
apply cracke_m_l_l0. apply exd_Iter_cF. exact H1.
apply exd_cA. exact H1. apply exd_right. omega.
Qed.

Lemma eq_i_m_m1_cF_r1_l : forall (i:nat), (i < degreef m r1) ->
  (Iter (cF m) i r1 = l) -> (Iter (cF m1) i r1 = l).
Proof.
intros i h1 h2. rewrite <- h2.
apply Iter_cF_m1_i_r1_Iter_cF_m_i_r1 with i.
omega. exact h1. exact h2.
Qed.

(* ===== *)

Lemma exists_i_Iter_cF_m_i_l1_r :
  exists i:nat, i < degreef m l1 /\ Iter (cF m) i l1 = r.
Proof.
assert (t1: exd m l). apply exd_left.
assert (t2: exd m r). apply exd_right.
assert (h: MF.expo1 m l1 r).
 apply MF.expo_expo1; try assumption.
 apply expf_trans with l0.
 apply expf_symm. unfold l0, l1.
 apply expf_cA_cA; try assumption.
 unfold l0. rewrite <- cA_m_zero_r0.
 apply expf_d0_x0; try assumption.
 apply expfright; try assumption.
 apply exd_left_dart_exd_right_dart; assumption.
destruct h as [h1 [i [h2 h3]]]. exists i; split.
rewrite MF.upb_eq_degree in h2; try assumption.
unfold MF.f, McF.f in h3; assumption.
Qed.

Lemma Iter_cF_m1_i_l1_Iter_cF_m_i_l1 : forall (i:nat)(n:nat),
  i <= n -> (n < degreef m l1) -> (Iter (cF m) n l1 = r) ->
  Iter (cF m1) i l1 = Iter (cF m) i l1.
Proof.
intros i n hle h1 h2; induction i.
simpl; tauto. simpl; rewrite IHi.
set (cFi := Iter (cF m) i l1).
unfold m1; rewrite cF_Split0; clear IHi.
elim eq_dart_dec; intro h3.
assert False; [idtac|tauto].
assert (t1: cF m l0 = l1).
 unfold cF; rewrite <- (eq_cA_cA_1 m zero l0).
 rewrite cA_m_zero_l0. rewrite <- eq_cA_cA_1.
 unfold l1; tauto. exact H1. exact H2. exact H1. exact H2.
fold l0 in h3; rewrite h3 in t1; unfold cFi in t1.
assert (t2: Iter (cF m) (S i) l1 = l1).
 simpl; exact t1.
assert (t3: Iter (cF m) (S i) l1 <> l1).
 apply MF.degree_lub. exact H1.
 apply exd_cA. exact H1. apply exd_left.
 replace MF.degree with degreef; try tauto.
omega. contradiction.
elim eq_dart_dec; intro h4.
assert False; [idtac|tauto].
assert (t1: expf m l1 cFi).
 unfold expf, MF.expo. repeat split.
 exact H1. apply exd_cA. exact H1. apply exd_left.
 exists i. unfold MF.f, McF.f. unfold cFi. tauto.
assert (t2: ~ expf m l1 l).
 intro h. apply not_expf_m_l_l0.
 apply expf_trans with l1.
 apply expf_symm; exact h.
 apply expf_symm; apply expf_cA_cA.
 exact H1. exact H2. apply exd_left.
rewrite cA_m_zero_l0 in h4; rewrite <- h4 in t1.
apply t2; exact t1. tauto. exact H1.
apply cracke_m_l_l0. apply exd_Iter_cF. exact H1.
apply exd_cA. exact H1. apply exd_left. omega.
Qed.

Lemma eq_i_m_m1_cF_l1_r : forall (i:nat), (i < degreef m l1) ->
  (Iter (cF m) i l1 = r) -> (Iter (cF m1) i l1 = r).
Proof.
intros i h1 h2; rewrite <- h2.
apply Iter_cF_m1_i_l1_Iter_cF_m_i_l1 with i.
omega. exact h1. exact h2.
Qed.

(* ===== *)

Lemma betweenf_m1_r1_l_r : betweenf m1 r1 l r.
Proof.
unfold betweenf, MF.between. intros h1 h2.
generalize exists_i_Iter_cF_m_i_r1_l.
intro h; elim h; clear h. intros i [h3 h4].
generalize exists_i_Iter_cF_m_i_l1_r.
intro h; elim h; clear h. intros j [h5 h6].
exists i. exists (j+1+i).
rewrite MF.upb_eq_degree; try assumption.
replace MF.degree with degreef; try tauto.
assert (t1: Iter (MF.f m1) i r1 = l).
 apply eq_i_m_m1_cF_r1_l; assumption.
assert (t2: Iter (MF.f m1) 1 l = l1).
 simpl. unfold MF.f, McF.f, cF.
 rewrite <- eq_cA_cA_1. rewrite <- eq_cA_cA_1.
 rewrite cA_m1_zero_l. rewrite cA_m1_one_da.
 unfold l1; tauto. apply exd_m1; apply exd_left.
 exact h1. apply inv_gmap_m1. exact h1. apply inv_gmap_m1.
assert (t3: Iter (MF.f m1) j l1 = r).
 apply eq_i_m_m1_cF_l1_r; assumption.
assert (t4: Iter (MF.f m1) (j+1+i) r1 = r).
 rewrite (MF.Iter_comp m1 (j+1) i r1). rewrite t1.
 rewrite (MF.Iter_comp m1 j 1 l). rewrite t2. exact t3.
assert (t5: Iter (MF.f m1) (degreef m1 r1) r1 = r1).
 apply MF.degree_per. exact h1. apply exd_m1.
 apply exd_cA. exact H1. apply exd_right.
repeat split; try assumption; try omega.
elim (eq_dart_dec (j + 1 + i) (degreef m1 r1)).
intro h. assert False; [idtac|tauto].
rewrite h in t4; rewrite t4 in t5.
apply neq_r_r1; exact t5. unfold m1.
rewrite (degreef_Split0_merge_summary m l l0 r1 H1).
elim expof_dec; intro t6. assert False; [idtac|tauto].
apply not_expf_m_l_l0. apply expf_trans with r0.
apply expfright. exact H1. apply exd_left.
apply exd_left_dart_exd_right_dart; assumption.
apply expf_trans with r1. unfold r0.
rewrite <- eq_cA_cA_1. apply expf_cA_cA.
exact H1. exact H2. apply exd_right.
exact H1. exact H2. apply expf_symm.
unfold l0. unfold expof in t6.
unfold expf; split. exact H1. exact t6.
elim expof_dec; intro t7. fold l0.
assert (t8: degreef m l0 = degreef m l1).
 apply MF.expo_degree. exact H1.
 apply expf_cA_cA; try assumption. apply exd_left.
assert (t9: degreef m (cA_1 m one l0) = degreef m r1).
 apply MF.expo_degree. exact H1. tauto.
rewrite t8; rewrite t9; intro t0. omega.
assert False; [idtac|tauto].
apply t7. apply expf_trans with l.
rewrite <- eq_cA_cA_1; try assumption.
rewrite <- cA_m_zero_l0. apply expf_symm.
apply expf_cA_cA. exact H1. exact H2.
apply exd_cA. exact H1. apply exd_left.
apply expf_trans with r0. apply expfright.
exact H1. apply exd_left.
apply exd_left_dart_exd_right_dart; assumption.
unfold r0. rewrite <- eq_cA_cA_1; try assumption.
apply expf_cA_cA; try assumption. apply exd_right.
apply cracke_m_l_l0. apply exd_cA. exact H1. apply exd_right.
rewrite <- eq_cA_cA_1; try assumption. fold l0.
intro h. apply not_expf_m_l0_cA_m_one_l0.
unfold expf; split. exact H1. tauto.
Qed.

(* ===== *)

Lemma exists_i_Iter_cF_m_i_cA_m_one_r0_l0 :
  exists i:nat, i < degreef m (cA m one r0) /\
  Iter (cF m) i (cA m one r0) = l0.
Proof.
assert (h: MF.expo1 m (cA m one r0) l0).
 apply MF.expo_expo1; try assumption.
 apply expf_trans with r.
 rewrite <- cA_m_zero_r0. apply expf_symm.
 apply expf_cA_cA; try assumption.
 apply exd_cA_1. exact H1. apply exd_right.
 unfold l0. rewrite <- cA_m_zero_r0.
 apply expf_d0_x0; try assumption. apply expf_symm.
 apply expfright; try assumption. apply exd_left.
 apply exd_left_dart_exd_right_dart; assumption.
destruct h as [h1 [i [h2 h3]]]. exists i; split.
rewrite MF.upb_eq_degree in h2; try assumption.
unfold MF.f, McF.f in h3; assumption.
Qed.

Lemma Iter_cF_m1_i_cA_m_one_r0_Iter_cF_m_i_cA_m_one_r0 :
  forall (i:nat)(n:nat), i <= n ->
  (n < degreef m (cA m one r0)) -> (Iter (cF m) n (cA m one r0) = l0) -> 
  Iter (cF m1) i (cA m one r0) = Iter (cF m) i (cA m one r0).
Proof.
intros i n hle h1 h2; induction i.
simpl; tauto. simpl; rewrite IHi; clear IHi.
set (cFi := Iter (cF m) i (cA m one r0)).
assert (t1: exd m r0).
 apply exd_cA_1. exact H1. apply exd_right.
assert (t2: exd m (cA m one r0)).
 apply exd_cA; assumption.
unfold m1; rewrite cF_Split0; try assumption.
elim eq_dart_dec; intro h3.
assert False; [idtac|tauto].
unfold cFi in h3; fold l0 in h3.
rewrite <- h2 in h3. assert (t0: n = i).
 apply MF.degree_unicity with m (cA m one r0); try assumption.
 replace MF.degree with degreef; try tauto. omega.
rewrite t0 in hle; omega.
elim eq_dart_dec; intro h4.
assert False; [idtac|tauto].
rewrite cA_m_zero_l0 in h4.
apply not_expf_m_r_r0.
apply expf_trans with l. rewrite h4. 
apply expf_trans with (cA m one r0).
rewrite <- cA_m_zero_r0. 
apply expf_cA_cA; try assumption.
unfold expf, MF.expo; repeat split; try assumption.
exists i; unfold MF.f, McF.f; fold cFi; tauto.
apply expfright; try assumption. apply exd_left.
apply exd_left_dart_exd_right_dart; assumption.
tauto. apply cracke_m_l_l0. apply exd_Iter_cF; assumption. omega.
Qed.

Lemma eq_i_m_m1_cF_cA_m_one_r0_l0 :
  forall (i:nat), (i < degreef m (cA m one r0)) ->
  (Iter (cF m) i (cA m one r0) = l0) -> (Iter (cF m1) i (cA m one r0) = l0).
Proof.
intros i h1 h2. rewrite <- h2.
apply Iter_cF_m1_i_cA_m_one_r0_Iter_cF_m_i_cA_m_one_r0 with i.
omega. exact h1. exact h2.
Qed.

(* ===== *)

Lemma exists_i_Iter_cF_m_i_cA_m_one_l0_r0 :
  exists i:nat, i < degreef m (cA m one l0) /\
  Iter (cF m) i (cA m one l0) = r0.
Proof.
assert (h: MF.expo1 m (cA m one l0) r0).
 apply MF.expo_expo1; try assumption.
 apply expf_trans with l.
 rewrite <- cA_m_zero_l0. apply expf_symm.
 apply expf_cA_cA; try assumption.
 apply exd_cA. exact H1. apply exd_left.
 apply expfright; try assumption. apply exd_left.
 apply exd_left_dart_exd_right_dart; assumption.
destruct h as [h1 [i [h2 h3]]]. exists i; split.
rewrite MF.upb_eq_degree in h2; try assumption.
unfold MF.f, McF.f in h3; assumption.
Qed.

Lemma Iter_cF_m1_i_cA_m_one_l0_Iter_cF_m_i_cA_m_one_l0 :
  forall (i:nat)(n:nat), i <= n ->
  (n < degreef m (cA m one l0)) -> (Iter (cF m) n (cA m one l0) = r0) -> 
  Iter (cF m1) i (cA m one l0) = Iter (cF m) i (cA m one l0).
Proof.
intros i n hle h1 h2; induction i.
simpl; tauto. simpl; rewrite IHi; clear IHi.
set (cFi := Iter (cF m) i (cA m one l0)).
assert (t1: exd m l0).
 apply exd_cA. exact H1. apply exd_left.
assert (t2: exd m (cA m one l0)).
 apply exd_cA; assumption.
unfold m1; rewrite cF_Split0; try assumption.
elim eq_dart_dec; intro h3.
assert False; [idtac|tauto].
apply not_expf_m_l_l0.
apply expf_trans with (cA m one l0).
rewrite <- cA_m_zero_l0.
apply expf_cA_cA; try assumption.
unfold l0 at 2; rewrite h3.
unfold expf, MF.expo; repeat split; try assumption.
exists i; unfold MF.f, McF.f; fold cFi; tauto.
elim eq_dart_dec; intro h4.
assert False; [idtac|tauto].
assert (t3: cF m l = cA m one l0).
 unfold cF. rewrite <- eq_cA_cA_1; try assumption.
 rewrite <- eq_cA_cA_1; try assumption. fold l0. tauto.
assert (t4: Iter (cF m) (S i) (cA m one l0) = (cA m one l0)).
 simpl. fold cFi. rewrite <- t3. rewrite <- h4.
 rewrite cA_m_zero_l0. tauto.
assert (t5: Iter (cF m) (S i) (cA m one l0) <> (cA m one l0)).
 apply MF.degree_lub; try assumption.
 replace MF.degree with degreef; try tauto.
omega. contradiction. tauto.
apply cracke_m_l_l0. apply exd_Iter_cF; assumption. omega.
Qed.

Lemma eq_i_m_m1_cF_cA_m_one_l0_r0 :
  forall (i:nat), (i < degreef m (cA m one l0)) ->
  (Iter (cF m) i (cA m one l0) = r0) -> (Iter (cF m1) i (cA m one l0) = r0).
Proof.
intros i h1 h2. rewrite <- h2.
apply Iter_cF_m1_i_cA_m_one_l0_Iter_cF_m_i_cA_m_one_l0 with i.
omega. exact h1. exact h2.
Qed.

(* ===== *)

Lemma betweenf_m1_cA_m_one_r0_l0_r0 : betweenf m1 (cA m one r0) l0 r0.
Proof.
unfold betweenf, MF.between. intros h1 h2.
generalize exists_i_Iter_cF_m_i_cA_m_one_r0_l0.
intro h; elim h; clear h. intros i [h3 h4].
generalize exists_i_Iter_cF_m_i_cA_m_one_l0_r0.
intro h; elim h; clear h. intros j [h5 h6].
exists i. exists (j+1+i).
rewrite MF.upb_eq_degree; try assumption.
replace MF.degree with degreef; try tauto.
assert (t1: Iter (MF.f m1) i (cA m one r0) = l0).
 apply eq_i_m_m1_cF_cA_m_one_r0_l0; assumption.
assert (t2: Iter (MF.f m1) 1 l0 = (cA m one l0)).
 simpl. unfold MF.f, McF.f, cF.
 rewrite <- eq_cA_cA_1. rewrite <- eq_cA_cA_1.
 rewrite cA_m1_zero_l0. rewrite cA_m1_one_da.
 trivial. apply exd_m1; apply exd_cA. exact H1. apply exd_left.
 exact h1. apply inv_gmap_m1. exact h1. apply inv_gmap_m1.
assert (t3: Iter (MF.f m1) j (cA m one l0) = r0).
 apply eq_i_m_m1_cF_cA_m_one_l0_r0; assumption.
assert (t4: Iter (MF.f m1) (j+1+i) (cA m one r0) = r0).
 rewrite (MF.Iter_comp m1 (j+1) i (cA m one r0)). rewrite t1.
 rewrite (MF.Iter_comp m1 j 1 l0). rewrite t2. exact t3.
assert (t5: Iter (MF.f m1) (degreef m1 (cA m one r0)) (cA m one r0) = (cA m one r0)).
 apply MF.degree_per. exact h1. apply exd_m1.
 apply exd_cA. exact H1. apply exd_cA_1. exact H1. apply exd_right.
repeat split; try assumption; try omega.
elim (eq_dart_dec (j + 1 + i) (degreef m1 (cA m one r0))).
intro h. assert False; [idtac|tauto].
rewrite h in t4; rewrite t4 in t5.
apply H3 with one r0; try assumption.
apply eqc_trans with l. apply eqcleft; assumption.
apply expf_eqc; try assumption. apply expfright.
exact H1. apply exd_left.
apply exd_left_dart_exd_right_dart; assumption. unfold m1.
rewrite (degreef_Split0_merge_summary m l l0 (cA m one r0) H1).
elim expof_dec; intro t6.
assert (t8: degreef m (cA m one r0) = degreef m (cA m zero l)).
 apply MF.expo_degree. exact H1.
 apply expf_symm. split. exact H1. apply t6.
assert (t9: degreef m (cA_1 m one l0) = degreef m (cA m one l0)).
 rewrite eq_cA_cA_1; try assumption. tauto.
rewrite <- t8; rewrite t9; intro t0. omega.
assert False; [idtac|tauto]. apply t6.
apply expf_symm; try assumption. fold l0.
unfold expf, MF.expo; repeat split; try assumption.
apply exd_cA; try assumption.
apply exd_cA_1; try assumption. apply exd_right.
exists i; assumption.
apply cracke_m_l_l0. apply exd_cA. exact H1.
apply exd_cA_1. exact H1. apply exd_right.
rewrite <- eq_cA_cA_1; try assumption. fold l0.
intro h; apply not_expf_m_l0_cA_m_one_l0.
unfold expf; split. exact H1. tauto.
Qed.

(* ===== *)

Lemma betweenf_m1_r1_l1_r : betweenf m1 r1 l1 r.
Proof.
unfold betweenf, MF.between. intros h1 h2.
generalize exists_i_Iter_cF_m_i_r1_l.
intro h; elim h; clear h. intros i [h3 h4].
generalize exists_i_Iter_cF_m_i_l1_r.
intro h; elim h; clear h. intros j [h5 h6].
exists (1+i). exists (j+1+i).
rewrite MF.upb_eq_degree; try assumption.
replace MF.degree with degreef; try tauto.
assert (t1: Iter (MF.f m1) i r1 = l).
 apply eq_i_m_m1_cF_r1_l; assumption.
assert (t2: Iter (MF.f m1) 1 l = l1).
 simpl. unfold MF.f, McF.f, cF.
 rewrite <- eq_cA_cA_1. rewrite <- eq_cA_cA_1.
 rewrite cA_m1_zero_l. rewrite cA_m1_one_da.
 unfold l1; tauto. apply exd_m1; apply exd_left.
 exact h1. apply inv_gmap_m1. exact h1. apply inv_gmap_m1.
assert (t3: Iter (MF.f m1) j l1 = r).
 apply eq_i_m_m1_cF_l1_r; assumption.
assert (t0: Iter (MF.f m1) (1+i) r1 = l1).
 rewrite (MF.Iter_comp m1 1 i r1). rewrite t1. exact t2.
assert (t4: Iter (MF.f m1) (j+1+i) r1 = r).
 rewrite (MF.Iter_comp m1 (j+1) i r1). rewrite t1.
 rewrite (MF.Iter_comp m1 j 1 l). rewrite t2. exact t3.
assert (t5: Iter (MF.f m1) (degreef m1 r1) r1 = r1).
 apply MF.degree_per. exact h1. apply exd_m1.
 apply exd_cA. exact H1. apply exd_right.
repeat split; try assumption; try omega.
elim (eq_dart_dec (j + 1 + i) (degreef m1 r1)).
intro h. assert False; [idtac|tauto].
rewrite h in t4; rewrite t4 in t5.
apply neq_r_r1; exact t5. unfold m1.
rewrite (degreef_Split0_merge_summary m l l0 r1 H1).
elim expof_dec; intro t6. assert False; [idtac|tauto].
apply not_expf_m_l_l0. apply expf_trans with r0.
apply expfright. exact H1. apply exd_left.
apply exd_left_dart_exd_right_dart; assumption.
apply expf_trans with r1. unfold r0.
rewrite <- eq_cA_cA_1. apply expf_cA_cA.
exact H1. exact H2. apply exd_right.
exact H1. exact H2. apply expf_symm.
unfold l0. unfold expof in t6.
unfold expf; split. exact H1. exact t6.
elim expof_dec; intro t7. fold l0.
assert (t8: degreef m l0 = degreef m l1).
 apply MF.expo_degree. exact H1.
 apply expf_cA_cA; try assumption. apply exd_left.
assert (t9: degreef m (cA_1 m one l0) = degreef m r1).
 apply MF.expo_degree. exact H1. tauto.
rewrite t8; rewrite t9; intro td. omega.
assert False; [idtac|tauto].
apply t7. apply expf_trans with l.
rewrite <- eq_cA_cA_1; try assumption.
rewrite <- cA_m_zero_l0. apply expf_symm.
apply expf_cA_cA. exact H1. exact H2.
apply exd_cA. exact H1. apply exd_left.
apply expf_trans with r0. apply expfright.
exact H1. apply exd_left.
apply exd_left_dart_exd_right_dart; assumption.
unfold r0. rewrite <- eq_cA_cA_1; try assumption.
apply expf_cA_cA; try assumption. apply exd_right.
apply cracke_m_l_l0. apply exd_cA. exact H1. apply exd_right.
rewrite <- eq_cA_cA_1; try assumption. fold l0.
intro h. apply not_expf_m_l0_cA_m_one_l0.
unfold expf; split. exact H1. tauto.
Qed.

(* ================================ *)
(* ========== ########## ========== *)
(* ================================ *)

Lemma inv_hmap_m2 : inv_hmap m2.
Proof.
unfold m2.
elim eq_dart_dec; intro h.
apply inv_hmap_m1.
apply inv_hmap_Split.
apply inv_hmap_m1.
Qed.

Lemma exd_m2 : forall (da:dart),
  exd m1 da <-> exd m2 da.
Proof.
intro da; split; unfold m2.
elim eq_dart_dec; intro h1; try trivial.
intro h2; apply -> exd_Split; assumption.
elim eq_dart_dec; intro h1; try trivial.
intro h2; apply <- exd_Split in h2; assumption.
Qed.

Lemma cA_m2_zero_r : cA m2 zero r = r.
Proof.
unfold m2.
elim eq_dart_dec; intro h.
rewrite <- h; apply cA_m1_zero_l0.
rewrite cA_Split; try assumption.
simpl; eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [idtac|tauto].
apply neq_r_r0; apply sym_eq; assumption.
rewrite cA_m1_zero_da.
apply cA_cA_1; try assumption.
apply exd_right.
apply -> exd_m1.
apply -> exd_cA_1; try assumption.
apply exd_right.
intro h2; apply h.
apply eq_l0_r_r0_l; assumption.
apply sym_not_eq; apply neq_l0_r0.
apply inv_hmap_m1.
unfold crack; simpl.
unfold cracke, MA0.crack; split.
apply sym_not_eq; apply neq_r_r0.
unfold MA0.MfcA.expo; split.
apply -> exd_m1.
apply -> exd_cA_1; try assumption.
apply exd_right.
unfold MA0.MfcA.f, MA0.McAMd.f, Md0.kd.
exists 1; simpl.
rewrite cA_m1_zero_da.
apply cA_cA_1; try assumption.
apply exd_right.
apply -> exd_m1.
apply -> exd_cA_1; try assumption.
apply exd_right.
intro h2; apply h.
apply eq_l0_r_r0_l; assumption.
apply sym_not_eq; apply neq_l0_r0.
Qed.

Lemma cA_m2_zero_r0 : cA m2 zero r0 = r0.
Proof.
unfold m2.
elim eq_dart_dec; intro h.
apply eq_l0_r_r0_l in h.
rewrite h; apply cA_m1_zero_l.
rewrite cA_Split; try assumption.
simpl; eqdartdec.
rewrite cA_m1_zero_da.
apply eq_cA_cA_1; assumption.
apply -> exd_m1.
apply exd_right.
apply sym_not_eq; apply neq_left_right; tauto.
apply sym_not_eq; assumption.
apply inv_hmap_m1.
unfold crack; simpl.
unfold cracke, MA0.crack; split.
apply sym_not_eq; apply neq_r_r0.
unfold MA0.MfcA.expo; split.
apply -> exd_m1.
apply -> exd_cA_1; try assumption.
apply exd_right.
unfold MA0.MfcA.f, MA0.McAMd.f, Md0.kd.
exists 1; simpl.
rewrite cA_m1_zero_da.
apply cA_cA_1; try assumption.
apply exd_right.
apply -> exd_m1.
apply -> exd_cA_1; try assumption.
apply exd_right.
intro h2; apply h.
apply eq_l0_r_r0_l; assumption.
apply sym_not_eq; apply neq_l0_r0.
Qed.

Lemma cA_m2_zero_da : forall (da:dart),
  exd m2 da -> da <> r -> da <> r0 ->
  cA m2 zero da = cA m1 zero da.
Proof.
intros da h1 h2 h3.
unfold m2.
elim eq_dart_dec; intro h; try trivial.
rewrite cA_Split; try assumption.
simpl; eqdartdec; trivial.
apply inv_hmap_m1.
unfold crack; simpl.
unfold cracke, MA0.crack; split.
apply sym_not_eq; apply neq_r_r0.
unfold MA0.MfcA.expo; split.
apply -> exd_m1.
apply -> exd_cA_1; try assumption.
apply exd_right.
unfold MA0.MfcA.f, MA0.McAMd.f, Md0.kd.
exists 1; simpl.
rewrite cA_m1_zero_da.
apply cA_cA_1; try assumption.
apply exd_right.
apply -> exd_m1.
apply -> exd_cA_1; try assumption.
apply exd_right.
intro h0; apply h.
apply eq_l0_r_r0_l; assumption.
apply sym_not_eq; apply neq_l0_r0.
Qed.

Lemma cA_m2_zero_l : cA m2 zero l = l.
Proof.
elim (eq_dart_dec l0 r); intro h.
apply eq_l0_r_r0_l in h.
rewrite <- h; apply cA_m2_zero_r0.
rewrite cA_m2_zero_da.
apply cA_m1_zero_l.
apply -> exd_m2; apply -> exd_m1; apply exd_left.
apply neq_left_right; tauto.
intro h0; apply h.
apply eq_l0_r_r0_l; intuition.
Qed.

Lemma cA_m2_zero_l0 : cA m2 zero l0 = l0.
Proof.
elim (eq_dart_dec l0 r); intro h.
rewrite h; apply cA_m2_zero_r.
rewrite cA_m2_zero_da; try tauto.
apply cA_m1_zero_l0.
apply -> exd_m2; apply -> exd_m1;
apply -> exd_cA; try assumption.
apply exd_left.
apply neq_l0_r0.
Qed.

Lemma cA_m2_one_da : forall (da:dart),
  exd m2 da -> cA m2 one da = cA m1 one da.
Proof.
intros da h1; unfold m2.
elim eq_dart_dec; intro h; try trivial.
rewrite cA_Split; simpl; try trivial.
apply inv_hmap_m1.
unfold crack; simpl.
unfold cracke, MA0.crack; split.
apply sym_not_eq; apply neq_r_r0.
unfold MA0.MfcA.expo; split.
apply -> exd_m1.
apply -> exd_cA_1; try assumption.
apply exd_right.
unfold MA0.MfcA.f, MA0.McAMd.f, Md0.kd.
exists 1; simpl.
rewrite cA_m1_zero_da.
apply cA_cA_1; try assumption.
apply exd_right.
apply -> exd_m1.
apply -> exd_cA_1; try assumption.
apply exd_right.
intro h0; apply h.
apply eq_l0_r_r0_l; assumption.
apply sym_not_eq; apply neq_l0_r0.
Qed.

Lemma inv_gmap_m2 : inv_gmap m2.
Proof.
unfold inv_gmap; intros k da Hda; induction k; simpl.
(* k = zero *)
elim (eq_dart_dec da r); intro h1.
subst da; do 2 rewrite cA_m2_zero_r; trivial.
elim (eq_dart_dec da r0); intro h2.
subst da; do 2 rewrite cA_m2_zero_r0; trivial.
elim (eq_dart_dec da l); intro h3.
subst da; do 2 rewrite cA_m2_zero_l; trivial.
elim (eq_dart_dec da l0); intro h4.
subst da; do 2 rewrite cA_m2_zero_l0; trivial.
rewrite cA_m2_zero_da; try assumption.
rewrite cA_m2_zero_da; try assumption.
apply inv_gmap_m1; apply <- exd_m2; assumption.
apply -> exd_cA; [exact Hda | apply inv_hmap_m2].
rewrite cA_m2_zero_da; try assumption.
rewrite cA_m1_zero_da; try assumption.
intro h0; apply sym_eq in h0.
apply subst_cA_cA_1 in h0; try tauto.
apply <- exd_m1; apply <- exd_m2; assumption.
apply <- exd_m2; assumption.
rewrite cA_m2_zero_da; try assumption.
rewrite cA_m1_zero_da; try assumption.
unfold r0; rewrite <- eq_cA_cA_1; try assumption.
apply -> bij_neq_cA; try assumption.
apply exd_right.
apply <- exd_m1; apply <- exd_m2; assumption.
apply <- exd_m2; assumption.
(* k = one *)
rewrite cA_m2_one_da; try assumption.
rewrite cA_m2_one_da; try assumption.
apply inv_gmap_m1; apply <- exd_m2; assumption.
apply -> exd_cA; [exact Hda | apply inv_hmap_m2].
Qed.

Lemma planar_m2 : planar m2.
Proof.
unfold m2.
elim eq_dart_dec; intro h.
apply planar_m1. apply planar_Split.
apply inv_hmap_m1. apply planar_m1.
apply sym_not_eq; apply neq_r_r0.
cut (succ m zero r -> succ m1 zero r). intro h1.
cut (succ m zero r0 -> succ m1 zero r0). intro h2.
cut (succ m zero r \/ succ m zero r0).
intro h0; elimination h0.
right; apply h1; assumption.
left; apply h2; assumption.
(**)
unfold r0; rewrite <- eq_cA_cA_1; try assumption.
apply succ_or_succ_cA with (cA m zero d); try assumption.
unfold inv_poly; intros k0 x0 hx0; apply H3.
apply eqc_trans with (cA m zero d); try assumption.
apply eqc_cA_r; assumption.
apply eqc_trans with d.
apply eqc_symm. apply eqc_cA_r; assumption.
apply eqc_trans with l.
apply eqcleft; assumption.
apply eqcright; try assumption.
apply exd_left.
apply exd_left_dart_exd_right_dart; assumption.
(**)
intro h2; unfold m1; unfold Split.
elim succ_dec; intro t1.
elim succ_dec; intro t2.
assert False; [idtac|tauto].
apply (succ_not_succ_cA m zero d l); try assumption.
unfold succ; rewrite A_B_bis; try assumption.
intro h0; apply h; apply eq_l0_r_r0_l; assumption.
unfold succ; rewrite A_B_bis; try assumption.
apply sym_not_eq; apply neq_l0_r0.
(**)
intro h1; unfold m1; unfold Split.
elim succ_dec; intro t1.
elim succ_dec; intro t2.
assert False; [idtac|tauto].
apply (succ_not_succ_cA m zero d l); try assumption.
unfold succ; rewrite A_B_bis; try assumption.
apply sym_not_eq; apply neq_left_right; try assumption.
left; assumption.
unfold succ; rewrite A_B_bis; try assumption.
apply sym_not_eq; assumption.
Qed.

Open Scope Z_scope.

Lemma nd_m2 : nd m2 = nd m1.
Proof.
unfold m2, Split.
elim eq_dart_dec; intro h; try trivial.
elim succ_dec; intro h1. 
elim succ_dec; intro h2.
rewrite nd_B; simpl.
rewrite nd_B; trivial.
rewrite nd_B; trivial.
rewrite nd_B; trivial.
Qed.

Lemma ne_m2 : ne m2 =
  if (eq_dart_dec l0 r) then ne m1 else ne m1 + 1.
Proof.
unfold m2.
elim eq_dart_dec; intro h; try trivial.
apply ne_Split0; try assumption.
apply inv_hmap_m1.
unfold cracke, MA0.crack; split.
apply sym_not_eq; apply neq_r_r0.
unfold MA0.MfcA.expo; split.
apply -> exd_m1.
apply -> exd_cA_1; try assumption.
apply exd_right.
exists 1%nat.
unfold MA0.MfcA.f, MA0.McAMd.f, Md0.kd.
simpl; rewrite cA_m1_zero_da.
apply cA_cA_1; try assumption.
apply exd_right.
apply -> exd_m1.
apply -> exd_cA_1; try assumption.
apply exd_right.
intro h0; apply h.
apply eq_l0_r_r0_l; assumption.
apply sym_not_eq; apply neq_l0_r0.
Qed.

Lemma nv_m2 : nv m2 = nv m1.
Proof.
unfold m2.
elim eq_dart_dec; intro h; try trivial.
apply nv_Split0; try assumption.
apply inv_hmap_m1.
unfold cracke, MA0.crack; split.
apply sym_not_eq; apply neq_r_r0.
unfold MA0.MfcA.expo; split.
apply -> exd_m1.
apply -> exd_cA_1; try assumption.
apply exd_right.
exists 1%nat.
unfold MA0.MfcA.f, MA0.McAMd.f, Md0.kd.
simpl; rewrite cA_m1_zero_da.
apply cA_cA_1; try assumption.
apply exd_right.
apply -> exd_m1.
apply -> exd_cA_1; try assumption.
apply exd_right.
intro h0; apply h.
apply eq_l0_r_r0_l; assumption.
apply sym_not_eq; apply neq_l0_r0.
Qed.

Lemma nf_m2 : nf m2 =
  if (eq_dart_dec l0 r) then nf m1 else nf m1 + 1.
Proof.
unfold m2.
elim eq_dart_dec; intro h; try trivial.
rewrite nf_Split0; try assumption.
elim expf_dec; intro h1; try trivial.
assert False; [idtac|tauto].
apply h1; clear h1.
rewrite cA_m1_zero_da. rewrite cA_m1_zero_da.
unfold r0; rewrite cA_cA_1; try assumption.
rewrite eq_cA_cA_1; try assumption. fold r0.
(**)
apply expf_trans with l0.
(**)
apply expf_Split0; try assumption.
unfold cracke, MA0.crack; split. apply neq_l_l0.
unfold MA0.MfcA.expo; split.
unfold l; apply exdleft; assumption.
unfold MA0.MfcA.f, MA0.McAMd.f, Md0.kd.
exists 1%nat; simpl; trivial.
fold l0; unfold l0 at 2; rewrite H2.
intro h0; apply H0; clear H0.
apply expf_symm in h0; apply expf_trans with l.
apply expfleft; assumption.
apply expf_trans with l0; try assumption.
apply expf_symm; apply expf_d0_x0; try assumption.
apply expfleft; assumption. apply exd_left.
(**)
unfold l0.
cut (r = cA m zero (cA_1 m zero r)).
intro h0; rewrite h0.
apply expf_d0_x0; try assumption.
apply expf_symm.
apply expfright; try assumption.
apply exd_left.
apply exd_left_dart_exd_right_dart; assumption.
rewrite cA_cA_1; try assumption. trivial.
apply exd_right.
(**)
apply expf_trans with l.
(**)
unfold m1; unfold l0 at 2.
cut (l = cA m zero l0). intro heq; rewrite heq at 3.
apply expf_Split0_cracke; try assumption.
unfold cracke, MA0.crack; split. apply neq_l_l0.
unfold MA0.MfcA.expo; split.
unfold l; apply exdleft; assumption.
unfold MA0.MfcA.f, MA0.McAMd.f, Md0.kd.
exists 1%nat; simpl; trivial.
fold l0; rewrite <- heq.
intro h0; apply H0; clear H0.
apply expf_symm in h0; apply expf_trans with l.
apply expfleft; assumption.
apply expf_trans with l0; try assumption.
apply expf_symm; apply expf_d0_x0; try assumption.
apply expfleft; assumption.
unfold l0; rewrite H2; trivial. apply exd_left.
(**)
apply expf_Split0; try assumption.
unfold cracke, MA0.crack; split. apply neq_l_l0.
unfold MA0.MfcA.expo; split.
unfold l; apply exdleft; assumption.
unfold MA0.MfcA.f, MA0.McAMd.f, Md0.kd.
exists 1%nat; simpl; trivial.
fold l0; unfold l0 at 2; rewrite H2.
intro h0; apply H0; clear H0.
apply expf_symm in h0; apply expf_trans with l.
apply expfleft; assumption.
apply expf_trans with l0; try assumption.
apply expf_symm; apply expf_d0_x0; try assumption.
apply expfleft; assumption. apply exd_left.
apply expf_trans with d.
apply expf_symm; apply expfleft; assumption.
pose (d0 := cA m zero d). cut (d = cA m zero d0).
intro heq; rewrite heq. unfold r0.
rewrite <- eq_cA_cA_1; try assumption.
apply expf_d0_x0; try assumption.
unfold d0.
apply expf_trans with (cA m zero l).
apply expf_d0_x0; try assumption.
apply expfleft; assumption.
cut (r = cA m zero (cA_1 m zero r)).
intro h0; rewrite h0.
apply expf_d0_x0; try assumption.
apply expfright; try assumption.
apply exd_left.
apply exd_left_dart_exd_right_dart; assumption.
rewrite cA_cA_1; try assumption. trivial.
apply exd_right.
unfold d0; rewrite H2; tauto.
(**)
apply exd_right.
apply -> exd_m1; apply exd_right.
apply sym_not_eq; apply neq_left_right; try tauto.
apply sym_not_eq; assumption.
apply -> exd_m1; apply -> exd_cA_1.
apply exd_right. assumption.
intro h0; apply h; apply eq_l0_r_r0_l; assumption.
apply sym_not_eq; apply neq_l0_r0.
apply inv_hmap_m1.
unfold cracke, MA0.crack; split.
apply sym_not_eq; apply neq_r_r0.
unfold MA0.MfcA.expo; split.
apply -> exd_m1; apply -> exd_cA_1.
apply exd_right. assumption.
unfold MA0.MfcA.f, MA0.McAMd.f, Md0.kd.
exists 1%nat; simpl; rewrite cA_m1_zero_da.
unfold r0; rewrite cA_cA_1; try tauto.
apply exd_right.
apply -> exd_m1; apply -> exd_cA_1.
apply exd_right. assumption.
intro h0; apply h; apply eq_l0_r_r0_l; assumption.
apply sym_not_eq; apply neq_l0_r0.
Qed.

Lemma nc_m2 : nc m2 =
  if (eq_dart_dec l0 r) then nc m1 else nc m1 + 1.
Proof.
unfold m2.
elim eq_dart_dec; intro h; try trivial.
rewrite planar_nc_Split0; try assumption.
elim expf_dec; intro h1; try trivial.
assert False; [idtac|tauto].
(**)
apply h1; clear h1.
rewrite cA_m1_zero_da. rewrite cA_m1_zero_da.
unfold r0; rewrite cA_cA_1; try assumption.
rewrite eq_cA_cA_1; try assumption. fold r0.
(**)
apply expf_trans with l0.
(**)
apply expf_Split0; try assumption.
unfold cracke, MA0.crack; split. apply neq_l_l0.
unfold MA0.MfcA.expo; split.
unfold l; apply exdleft; assumption.
unfold MA0.MfcA.f, MA0.McAMd.f, Md0.kd.
exists 1%nat; simpl; trivial.
fold l0; unfold l0 at 2; rewrite H2.
intro h0; apply H0; clear H0.
apply expf_symm in h0; apply expf_trans with l.
apply expfleft; assumption.
apply expf_trans with l0; try assumption.
apply expf_symm; apply expf_d0_x0; try assumption.
apply expfleft; assumption. apply exd_left.
apply expf_trans with (cA m zero d).
apply expf_trans with (cA m zero l).
cut (r = cA m zero (cA_1 m zero r)).
intro h0; rewrite h0.
apply expf_d0_x0; try assumption.
apply expf_symm.
apply expfright; try assumption.
apply exd_left.
apply exd_left_dart_exd_right_dart; assumption.
rewrite cA_cA_1; try assumption. trivial.
apply exd_right.
apply expf_d0_x0; try assumption.
apply expf_symm.
apply expfleft; assumption.
apply expf_d0_x0; try assumption.
apply expfleft; assumption.
(**)
apply expf_trans with l.
(**)
unfold m1; unfold l0 at 2.
cut (l = cA m zero l0). intro heq; rewrite heq at 3.
apply expf_Split0_cracke; try assumption.
unfold cracke, MA0.crack; split. apply neq_l_l0.
unfold MA0.MfcA.expo; split.
unfold l; apply exdleft; assumption.
unfold MA0.MfcA.f, MA0.McAMd.f, Md0.kd.
exists 1%nat; simpl; trivial.
fold l0; rewrite <- heq.
intro h0; apply H0; clear H0.
apply expf_symm in h0; apply expf_trans with l.
apply expfleft; assumption.
apply expf_trans with l0; try assumption.
apply expf_symm; apply expf_d0_x0; try assumption.
apply expfleft; assumption.
unfold l0; rewrite H2; trivial. apply exd_left.
(**)
apply expf_Split0; try assumption.
unfold cracke, MA0.crack; split. apply neq_l_l0.
unfold MA0.MfcA.expo; split.
unfold l; apply exdleft; assumption.
unfold MA0.MfcA.f, MA0.McAMd.f, Md0.kd.
exists 1%nat; simpl; trivial.
fold l0; unfold l0 at 2; rewrite H2.
intro h0; apply H0; clear H0.
apply expf_symm in h0; apply expf_trans with l.
apply expfleft; assumption.
apply expf_trans with l0; try assumption.
apply expf_symm; apply expf_d0_x0; try assumption.
apply expfleft; assumption. apply exd_left.
apply expf_trans with d.
apply expf_symm; apply expfleft; assumption.
pose (d0 := cA m zero d). cut (d = cA m zero d0).
intro heq; rewrite heq. unfold r0.
rewrite <- eq_cA_cA_1; try assumption.
apply expf_d0_x0; try assumption.
unfold d0.
apply expf_trans with (cA m zero l).
apply expf_d0_x0; try assumption.
apply expfleft; assumption.
cut (r = cA m zero (cA_1 m zero r)).
intro h0; rewrite h0.
apply expf_d0_x0; try assumption.
apply expfright; try assumption.
apply exd_left.
apply exd_left_dart_exd_right_dart; assumption.
rewrite cA_cA_1; try assumption. trivial.
apply exd_right.
unfold d0; rewrite H2; tauto.
(**)
apply exd_right.
apply -> exd_m1; apply exd_right.
apply sym_not_eq; apply neq_left_right; try tauto.
apply sym_not_eq; assumption.
apply -> exd_m1; apply -> exd_cA_1.
apply exd_right. assumption.
intro h0; apply h; apply eq_l0_r_r0_l; assumption.
apply sym_not_eq; apply neq_l0_r0.
apply inv_hmap_m1. apply planar_m1.
unfold cracke, MA0.crack; split.
apply sym_not_eq; apply neq_r_r0.
unfold MA0.MfcA.expo; split.
apply -> exd_m1; apply -> exd_cA_1.
apply exd_right. assumption.
unfold MA0.MfcA.f, MA0.McAMd.f, Md0.kd.
exists 1%nat; simpl; rewrite cA_m1_zero_da.
unfold r0; rewrite cA_cA_1; try tauto.
apply exd_right.
apply -> exd_m1; apply -> exd_cA_1.
apply exd_right. assumption.
intro h0; apply h; apply eq_l0_r_r0_l; assumption.
apply sym_not_eq; apply neq_l0_r0.
Qed.

Open Scope nat_scope.

Lemma is_well_emb_m2 : is_well_emb m2.
Proof.
unfold is_well_emb; intros da db h1 h2 h3.
apply exd_m2 in h1; apply exd_m2 in h2.
unfold m2; elim eq_dart_dec; intro h.
apply is_well_emb_m1; assumption.
split; intro h4.
(* expv da db *)
do 2 rewrite fpoint_Split.
apply -> expv_Split0 in h4; try assumption.
generalize (is_well_emb_m1 da db h1 h2 h3).
intros [h5 h6]; apply h5; assumption.
apply inv_hmap_m1.
(* expe da db *)
do 2 rewrite fpoint_Split.
apply expe_Split_expe in h4; try assumption.
generalize (is_well_emb_m1 da db h1 h2 h3).
intros [h5 h6]; apply h6; assumption.
apply inv_hmap_m1.
Qed.

Lemma is_neq_point_m2 : is_neq_point m2.
Proof.
unfold is_neq_point; intros da db h1 h2.
apply exd_m2 in h1; apply exd_m2 in h2.
unfold m2; elim eq_dart_dec; intro h.
apply is_neq_point_m1; assumption.
intro h3; do 2 rewrite fpoint_Split.
rewrite -> expv_Split0 in h3.
apply is_neq_point_m1; assumption.
apply inv_hmap_m1.
Qed.

Lemma is_noalign_m2 : is_noalign m2.
Proof.
unfold is_noalign; intros da db dc h1 h2 h3.
apply exd_m2 in h1; apply exd_m2 in h2; apply exd_m2 in h3.
unfold m2; elim eq_dart_dec; intro h.
apply is_noalign_m1; assumption.
intros h4 h5 h6; do 3 rewrite fpoint_Split in *.
apply is_noalign_m1; assumption.
Qed.

(* ================================ *)

Lemma not_expf_m2_r_r0 : l0 <> r -> ~ expf m2 r r0.
Proof.
intro heq. unfold m2.
elim eq_dart_dec; try tauto; intro h; clear h.
assert (t1: inv_hmap m1). apply inv_hmap_m1.
assert (t2: inv_gmap m1). apply inv_gmap_m1.
intro h; unfold expf in h; destruct h as [h0 h].
rewrite (expof_Split0_CNS m1 r0 r r r0 t1) in h.
assert (t3: cA m1 zero r0 = r).
 rewrite cA_m1_zero_da. apply cA_m_zero_r0.
 apply exd_m1; apply exd_cA_1; try assumption; apply exd_right.
 intro t0; apply heq; apply eq_l0_r_r0_l; assumption.
 apply not_eq_sym; apply neq_l0_r0. rewrite t3 in h.
generalize h; clear h. elim expof_dec; intro h.
intro H. elimination H. destruct H as [h1 h2].
assert (t4: cF m1 r0 = cA_1 m1 one r).
 unfold r0; rewrite <- eq_cA_cA_1; try assumption.
 rewrite <- cA_m1_zero_da. unfold cF.
 rewrite cA_1_cA; try assumption. trivial.
 apply exd_m1; apply exd_right. apply exd_m1; apply exd_right.
 apply not_eq_sym; apply neq_left_right; try assumption.
 left; assumption. apply not_eq_sym; assumption.
unfold betweenf, MF.between in h2; rewrite <- t4 in h2.
assert (t5: exd m1 (cF m1 r0)).
 apply -> exd_cF; try assumption.
 apply exd_m1; apply exd_cA_1. exact H1. apply exd_right.
generalize (h2 t1 t5); clear h2; intro h2.
unfold MF.f, McF.f in h2.
elim h2; clear h2; intros i h2.
elim h2; clear h2; intros j [h2 [h3 h4]].
rewrite MF.upb_eq_degree in h4; try assumption.
replace MF.degree with degreef in h4; try tauto.
assert (t6: degreef m1 (cF m1 r0) = (S i)).
 elim (eq_dart_dec (degreef m1 (cF m1 r0)) (S i)).
 trivial. intro t0. assert False; [idtac|tauto].
 assert (t6: Iter (cF m1) (S i) r0 = r0).
  rewrite MF.Iter_f_Si; try assumption.
  apply exd_m1; apply exd_cA_1. exact H1. apply exd_right.
 assert (t7: 0 < S i < degreef m1 (cF m1 r0)). omega.
 assert (t8: exd m1 r0).
  apply exd_m1; apply exd_cA_1. exact H1. apply exd_right.
 assert (t9: MF.degree m1 r0 = degreef m1 (cF m1 r0)).
  apply MF.expo_degree; try assumption.
  unfold MF.expo; split. assumption.
  exists 1; simpl; trivial. rewrite <- t9 in t7.
 apply (MF.degree_diff m1 r0 t1 t8 (S i)); assumption.
rewrite t6 in h4; apply neq_r_r0. rewrite <- h2, <- h3.
assert (t7: i = j). omega. rewrite t7; trivial.
elimination H; destruct H as [h1 h2].
assert (t4: cF m1 r = cA_1 m1 one r0).
 replace r0 with (cA_1 m1 zero r); unfold cF; trivial.
 rewrite <- eq_cA_cA_1; try assumption. unfold r0.
 rewrite cA_m1_zero_da. rewrite <- eq_cA_cA_1; trivial.
 apply exd_m1; apply exd_right.
 apply not_eq_sym; apply neq_left_right; try assumption.
 left; assumption. apply not_eq_sym; assumption.
unfold betweenf, MF.between in h1; rewrite <- t4 in h1.
assert (t5: exd m1 (cF m1 r)).
 apply -> exd_cF; try assumption.
 apply exd_m1; apply exd_right.
generalize (h1 t1 t5); clear h1; intro h1.
unfold MF.f, McF.f in h1.
elim h1; clear h1; intros i h1.
elim h1; clear h1; intros j [h1 [h3 h4]].
rewrite MF.upb_eq_degree in h4; try assumption.
replace MF.degree with degreef in h4; try tauto.
assert (t6: degreef m1 (cF m1 r) = (S i)).
 elim (eq_dart_dec (degreef m1 (cF m1 r)) (S i)).
 trivial. intro t0. assert False; [idtac|tauto].
 assert (t6: Iter (cF m1) (S i) r = r).
  rewrite MF.Iter_f_Si; try assumption.
  apply exd_m1; apply exd_right.
 assert (t7: 0 < S i < degreef m1 (cF m1 r)). omega.
 assert (t8: exd m1 r).
  apply exd_m1; apply exd_right.
 assert (t9: MF.degree m1 r = degreef m1 (cF m1 r)).
  apply MF.expo_degree; try assumption.
  unfold MF.expo; split. assumption.
  exists 1; simpl; trivial. rewrite <- t9 in t7.
 apply (MF.degree_diff m1 r t1 t8 (S i)); assumption.
assert (t0: r <> cA m1 zero r).
 rewrite cA_m1_zero_da. rewrite eq_cA_cA_1; try assumption.
 fold r0; apply neq_r_r0. apply exd_m1; apply exd_right.
 apply not_eq_sym; apply neq_left_right; try assumption.
 left; assumption. apply not_eq_sym; assumption.
rewrite t6 in h4; apply t0.
rewrite <- h1 at 1; rewrite <- h3.
assert (t7: i = j). omega. rewrite t7; trivial.
apply h1; apply (expf_refl m1 r). assumption.
apply exd_m1; apply exd_right.
intro H; clear H. apply h; clear h.
rewrite <- eq_cA_cA_1; try assumption.
rewrite cA_m1_one_da.
apply expf_m1_r_r1.
apply exd_m1; apply exd_right.
apply cracke_m1_r0_r.
assumption. apply exd_m1; apply exd_right.
Qed.

(* ===== *)

Lemma not_eqc_m2_r_r0 : l0 <> r -> ~ eqc m2 r r0.
Proof.
intro heq. unfold m2.
elim eq_dart_dec; try tauto; intro h; clear h.
assert (t0: r0 = cA m1 zero r).
 rewrite cA_m1_zero_da; try assumption.
 rewrite eq_cA_cA_1; try assumption.
 unfold r0; trivial. apply exd_m1; apply exd_right.
 apply not_eq_sym; apply neq_left_right; try assumption.
 left; assumption. apply not_eq_sym; assumption.
rewrite t0 at 2; apply disconnect_planar_criterion_Split0.
apply inv_hmap_m1. apply planar_m1.
apply expe_m1_r0_r; assumption.
apply not_eq_sym; apply neq_r_r0.
rewrite cA_m1_zero_da. rewrite cA_m_zero_r0.
rewrite <- t0; apply expf_m1_r_r0.
apply exd_m1; apply exd_cA_1. exact H1. apply exd_right.
intro h0; apply heq; apply eq_l0_r_r0_l; assumption.
apply not_eq_sym; apply neq_l0_r0.
Qed.

Lemma not_expf_m2_r_r0_bis : l0 <> r -> ~ expf m2 r r0.
Proof.
intros h0 h.
apply not_eqc_m2_r_r0; try assumption.
apply expf_eqc. apply inv_hmap_m2.
unfold expf in h. tauto.
Qed.

Lemma expf_m2_l_r : expf m2 l r.
Proof.
unfold expf; split. apply inv_hmap_m2.
unfold m2; elim eq_dart_dec; intro h.
apply eq_l0_r_r0_l in h. rewrite <- h.
apply expf_symm. apply expf_m1_r_r0.
assert (t1: inv_hmap m1). apply inv_hmap_m1.
assert (t2: inv_gmap m1). apply inv_gmap_m1.
apply (expof_Split0_CNS m1 r0 r l r t1).
apply cracke_m1_r0_r; assumption.
apply exd_m1; apply exd_left.
assert (t3: cA m1 zero r0 = r).
 rewrite cA_m1_zero_da. apply cA_m_zero_r0.
 apply exd_m1; apply exd_cA_1. exact H1. apply exd_right.
 intro h0; apply h; apply eq_l0_r_r0_l; assumption.
 apply not_eq_sym; apply neq_l0_r0. rewrite t3.
elim expof_dec; intro h0. left; split.
assert (t0: cA_1 m1 one r = r1).
 rewrite <- eq_cA_cA_1; try assumption.
 rewrite cA_m1_one_da. unfold r1; tauto.
 apply exd_m1; apply exd_right.
rewrite t0; apply betweenf_m1_r1_l_r.
apply MF.between_expo_refl_2. exact t1.
apply exd_cA_1. exact t1. apply exd_m1; apply exd_right.
apply MF.expo_expo1; try assumption.
apply MF.expo_symm; assumption.
assert False; [idtac|tauto]. apply h0.
replace (cA_1 m1 one r) with (cA m one r).
apply expf_m1_r_r1.
rewrite <- eq_cA_cA_1; try assumption.
rewrite cA_m1_one_da. trivial.
apply exd_m1; apply exd_right.
Qed.

Lemma expf_m2_l0_r0 : expf m2 l0 r0.
Proof.
unfold expf; split. apply inv_hmap_m2.
unfold m2; elim eq_dart_dec; intro h.
apply eq_l0_r_r0_l in h. rewrite h.
apply expf_symm. apply expf_m1_l_l0.
assert (t1: inv_hmap m1). apply inv_hmap_m1.
assert (t2: inv_gmap m1). apply inv_gmap_m1.
apply (expof_Split0_CNS m1 r0 r l0 r0 t1).
apply cracke_m1_r0_r; assumption.
apply exd_m1; apply exd_cA. exact H1. apply exd_left.
assert (t3: cA m1 zero r0 = r).
 rewrite cA_m1_zero_da. apply cA_m_zero_r0.
 apply exd_m1; apply exd_cA_1. exact H1. apply exd_right.
 intro h0; apply h; apply eq_l0_r_r0_l; assumption.
 apply not_eq_sym; apply neq_l0_r0.
assert (t4: cA m1 zero r = r0).
 rewrite <- t3. apply t2.
 apply exd_m1; apply exd_cA_1. exact H1. apply exd_right.
rewrite t3; rewrite t4.
elim expof_dec; intro h0. right; left; split.
assert (t0: cA_1 m1 one r0 = cA m one r0).
 rewrite <- eq_cA_cA_1; try assumption.
 rewrite cA_m1_one_da. tauto. apply exd_m1.
 apply exd_cA_1. exact H1. apply exd_right.
rewrite t0; apply betweenf_m1_cA_m_one_r0_l0_r0.
apply MF.between_expo_refl_2. exact t1.
apply exd_cA_1. exact t1.
apply exd_m1; apply exd_cA_1. exact H1. apply exd_right.
apply MF.expo_expo1; try assumption.
apply MF.expo_symm; try assumption.
rewrite <- eq_cA_cA_1; try assumption.
rewrite cA_m1_one_da. apply expf_m1_r0_cA_m_one_r0.
apply exd_m1; apply exd_cA_1. exact H1. apply exd_right.
assert False; [idtac|tauto]. apply h0.
replace (cA_1 m1 one r) with (cA m one r).
apply expf_m1_r_r1.
rewrite <- eq_cA_cA_1; try assumption.
rewrite cA_m1_one_da. trivial.
apply exd_m1; apply exd_right.
Qed.

(* ================================ *)
(* ========== ########## ========== *)
(* ================================ *)

Lemma not_exd_m2_x : ~ exd m2 x.
Proof.
intro h; apply H11; apply <- exd_m1; apply <- exd_m2; assumption.
Qed.

Lemma not_exd_m2_max : ~ exd m2 max.
Proof.
intro h; apply H12; apply <- exd_m1; apply <- exd_m2; assumption.
Qed.

(* ================================ *)

Lemma inv_hmap_m3 : inv_hmap m3.
Proof.
unfold m3; simpl; unfold prec_I.
simpl; repeat split; try assumption.
apply inv_hmap_m2. apply not_exd_m2_x.
intro h; elimination h; try contradiction.
apply not_exd_m2_max; assumption.
Qed.

Lemma exd_m3_1 : forall (da:dart),
  exd m3 da -> da = x \/ da = max \/ exd m2 da .
Proof.
intro da; unfold m3; simpl; intuition.
Qed.

Lemma exd_m3_2 : forall (da:dart),
  exd m2 da -> exd m3 da.
Proof.
intro da; unfold m3; simpl; tauto.
Qed.

Lemma cA_m3_zero_x : cA m3 zero x = x.
Proof.
unfold m3; simpl; eqdartdec; trivial.
Qed.

Lemma cA_m3_zero_max : cA m3 zero max = max.
Proof.
unfold m3; simpl; eqdartdec; trivial.
Qed.

Lemma cA_m3_zero_da : forall (da:dart),
  exd m3 da -> da <> x -> da <> max ->
  cA m3 zero da = cA m2 zero da.
Proof.
intros da h1 h2 h3.
unfold m3; simpl; eqdartdec; trivial.
Qed.

Lemma cA_m3_zero_l : cA m3 zero l = l.
Proof.
unfold m3; simpl.
elim eq_dart_dec; intro h1; try trivial.
elim eq_dart_dec; intro h2; try trivial.
apply cA_m2_zero_l.
Qed.

Lemma cA_m3_zero_l0 : cA m3 zero l0 = l0.
Proof.
unfold m3; simpl.
elim eq_dart_dec; intro h1; try trivial.
elim eq_dart_dec; intro h2; try trivial.
apply cA_m2_zero_l0.
Qed.

Lemma cA_m3_zero_r : cA m3 zero r = r.
Proof.
unfold m3; simpl.
elim eq_dart_dec; intro h1; try trivial.
elim eq_dart_dec; intro h2; try trivial.
apply cA_m2_zero_r.
Qed.

Lemma cA_m3_zero_r0 : cA m3 zero r0 = r0.
Proof.
unfold m3; simpl.
elim eq_dart_dec; intro h1; try trivial.
elim eq_dart_dec; intro h2; try trivial.
apply cA_m2_zero_r0.
Qed.

Lemma cA_m3_one_x : cA m3 one x = x.
Proof.
unfold m3; simpl; eqdartdec; trivial.
Qed.

Lemma cA_m3_one_max : cA m3 one max = max.
Proof.
unfold m3; simpl; eqdartdec; trivial.
Qed.

Lemma cA_m3_one_da : forall (da:dart),
  exd m3 da -> da <> x -> da <> max ->
  cA m3 one da = cA m2 one da.
Proof.
intros da h1 h2 h3.
unfold m3; simpl; eqdartdec; trivial.
Qed.

Lemma inv_gmap_m3 : inv_gmap m3.
Proof.
unfold inv_gmap; intros k da Hda; induction k.
(* k = zero *)
elim (eq_dart_dec da x); intro h1.
subst da; do 2 rewrite cA_m3_zero_x; trivial.
elim (eq_dart_dec da max); intro h2.
subst da; do 2 rewrite cA_m3_zero_max; trivial.
rewrite cA_m3_zero_da; try assumption.
rewrite cA_m3_zero_da; try assumption.
apply inv_gmap_m2; apply exd_m3_1 in Hda; intuition.
apply -> exd_cA; [exact Hda | apply inv_hmap_m3].
rewrite cA_m3_zero_da; try assumption.
intro h; apply sym_eq in h.
apply subst_cA_cA_1 in h. rewrite not_exd_cA_1 in h.
apply exd_not_nil with m3 da; try assumption.
apply inv_hmap_m3. apply inv_hmap_m2. apply not_exd_m2_x.
apply inv_hmap_m2. apply exd_m3_1 in Hda; intuition.
rewrite cA_m3_zero_da; try assumption.
intro h; apply sym_eq in h.
apply subst_cA_cA_1 in h. rewrite not_exd_cA_1 in h.
apply exd_not_nil with m3 da; try assumption.
apply inv_hmap_m3. apply inv_hmap_m2. apply not_exd_m2_max.
apply inv_hmap_m2. apply exd_m3_1 in Hda; intuition.
(* k = one *)
elim (eq_dart_dec da x); intro h1.
subst da; do 2 rewrite cA_m3_one_x; trivial.
elim (eq_dart_dec da max); intro h2.
subst da; do 2 rewrite cA_m3_one_max; trivial.
rewrite cA_m3_one_da; try assumption.
rewrite cA_m3_one_da; try assumption.
apply inv_gmap_m2; apply exd_m3_1 in Hda; intuition.
apply -> exd_cA; [exact Hda | apply inv_hmap_m3].
rewrite cA_m3_one_da; try assumption.
intro h; apply sym_eq in h.
apply subst_cA_cA_1 in h. rewrite not_exd_cA_1 in h.
apply exd_not_nil with m3 da; try assumption.
apply inv_hmap_m3. apply inv_hmap_m2.  apply not_exd_m2_x.
apply inv_hmap_m2. apply exd_m3_1 in Hda; intuition.
rewrite cA_m3_one_da; try assumption.
intro h; apply sym_eq in h.
apply subst_cA_cA_1 in h. rewrite not_exd_cA_1 in h.
apply exd_not_nil with m3 da; try assumption.
apply inv_hmap_m3. apply inv_hmap_m2. apply not_exd_m2_max.
apply inv_hmap_m2. apply exd_m3_1 in Hda; intuition.
Qed.

Lemma planar_m3 : planar m3.
Proof.
unfold m3; apply planar_I; try apply planar_I;
simpl; unfold prec_I; simpl; repeat split; try assumption.
apply inv_hmap_m2. apply not_exd_m2_x.
apply inv_hmap_m2. apply planar_m2. apply not_exd_m2_x.
intro h; elimination h; try contradiction.
apply not_exd_m2_max; assumption.
Qed.

Open Scope Z_scope.

Lemma nd_m3 : nd m3 = nd m2 + 2.
Proof.
unfold m3; simpl; ring.
Qed.

Lemma ne_m3 : ne m3 = ne m2 + 2.
Proof.
unfold m3; simpl; ring.
Qed.

Lemma nv_m3 : nv m3 = nv m2 + 2.
Proof.
unfold m3; simpl; ring.
Qed.

Lemma nf_m3 : nf m3 = nf m2 + 2.
Proof.
unfold m3; simpl; ring.
Qed.

Lemma nc_m3 : nc m3 = nc m2 + 2.
Proof.
unfold m3; simpl; ring.
Qed.

Open Scope nat_scope.

Lemma is_well_emb_m3 : is_well_emb m3.
Proof.
unfold is_well_emb; intros da db h1 h2 h3.
unfold m3; simpl; split; intro h; clear h1 h2.
(* expv da db *)
apply expv_I in h. elimination h.
destruct h as [h1 h2]; subst da; subst db; tauto.
apply expv_I in h. elimination h.
destruct h as [h1 h2]; subst da; subst db; tauto.
assert (h1: exd m2 da).
unfold expv, MA1.MfcA.expo in h; tauto.
assert (h2: exd m2 db).
apply expv_symm in h; try apply inv_hmap_m2.
unfold expv, MA1.MfcA.expo in h; tauto.
assert (t1: da <> x).
intro h0; subst da; apply not_exd_m2_x; assumption.
assert (t2: da <> max).
intro h0; subst da; apply not_exd_m2_max; assumption.
assert (t3: db <> x).
intro h0; subst db; apply not_exd_m2_x; assumption.
assert (t4: db <> max).
intro h0; subst db; apply not_exd_m2_max; assumption.
eqdartdec; generalize (is_well_emb_m2 da db h1 h2 h3).
intros [h4 h5]; apply h4; assumption.
apply inv_hmap_m2. apply not_exd_m2_x.
simpl; unfold prec_I; simpl; repeat split; try assumption.
apply inv_hmap_m2. apply not_exd_m2_x.
intro h0; elimination h0; try contradiction.
apply not_exd_m2_max; assumption.
(* expe da db *)
apply expe_I in h. elimination h.
destruct h as [h1 h2]; subst da; subst db; tauto.
apply expe_I in h. elimination h.
destruct h as [h1 h2]; subst da; subst db; tauto.
assert (h1: exd m2 da).
unfold expe, MA0.MfcA.expo in h; tauto.
assert (h2: exd m2 db).
apply expe_symm in h; try apply inv_hmap_m2.
unfold expe, MA0.MfcA.expo in h; tauto.
assert (t1: da <> x).
intro h0; subst da; apply not_exd_m2_x; assumption.
assert (t2: da <> max).
intro h0; subst da; apply not_exd_m2_max; assumption.
assert (t3: db <> x).
intro h0; subst db; apply not_exd_m2_x; assumption.
assert (t4: db <> max).
intro h0; subst db; apply not_exd_m2_max; assumption.
eqdartdec; generalize (is_well_emb_m2 da db h1 h2 h3).
intros [h4 h5]; apply h5; assumption.
apply inv_hmap_m2. apply not_exd_m2_x.
simpl; unfold prec_I; simpl; repeat split; try assumption.
apply inv_hmap_m2. apply not_exd_m2_x.
intro h0; elimination h0; try contradiction.
apply not_exd_m2_max; assumption.
Qed.

Lemma is_noalign_m3 : is_noalign m3.
Proof.
unfold is_noalign; intros da db dc h1 h2 h3.
unfold m3; simpl fpoint.
elim (eq_dart_dec max da); intro e1; try subst da.
elim (eq_dart_dec max db); [tauto|idtac].
elim (eq_dart_dec x db); [tauto|idtac].
elim (eq_dart_dec max dc); [tauto|idtac].
elim (eq_dart_dec x dc); [tauto|idtac].
intros t1 t2 t3 t4.
apply exd_m3_1 in h2.
elimination h2.
apply eq_sym in h2; contradiction.
elimination h2.
apply eq_sym in h2; contradiction.
apply exd_m2 in h2; apply exd_m1 in h2.
apply exd_m3_1 in h3.
elimination h3.
apply eq_sym in h3; contradiction.
elimination h3.
apply eq_sym in h3; contradiction.
apply exd_m2 in h3; apply exd_m1 in h3.
unfold m2.
elim eq_dart_dec; intro t0.
unfold m1.
do 2 rewrite fpoint_Split.
intros t5 t6.
apply H17; assumption.
do 2 rewrite fpoint_Split.
unfold m1.
do 2 rewrite fpoint_Split.
intros t5 t6.
apply H17; assumption.
elim (eq_dart_dec x da); intro e2; try subst da.
elim (eq_dart_dec max db); [tauto|idtac].
elim (eq_dart_dec x db); [tauto|idtac].
elim (eq_dart_dec max dc); [tauto|idtac].
elim (eq_dart_dec x dc); [tauto|idtac].
intros t1 t2 t3 t4.
apply exd_m3_1 in h2.
elimination h2.
apply eq_sym in h2; contradiction.
elimination h2.
apply eq_sym in h2; contradiction.
apply exd_m2 in h2; apply exd_m1 in h2.
apply exd_m3_1 in h3.
elimination h3.
apply eq_sym in h3; contradiction.
elimination h3.
apply eq_sym in h3; contradiction.
apply exd_m2 in h3; apply exd_m1 in h3.
unfold m2.
elim eq_dart_dec; intro t0.
unfold m1.
do 2 rewrite fpoint_Split.
intros t5 t6.
apply H17; assumption.
do 2 rewrite fpoint_Split.
unfold m1.
do 2 rewrite fpoint_Split.
intros t5 t6.
apply H17; assumption.
elim (eq_dart_dec max db); intro e3; try subst db.
elim (eq_dart_dec max dc); [tauto|idtac].
elim (eq_dart_dec x dc); [tauto|idtac].
intros t1 t2.
apply exd_m3_1 in h1.
elimination h1.
apply eq_sym in h1; contradiction.
elimination h1.
apply eq_sym in h1; contradiction.
apply exd_m2 in h1; apply exd_m1 in h1.
apply exd_m3_1 in h3.
elimination h3.
apply eq_sym in h3; contradiction.
elimination h3.
apply eq_sym in h3; contradiction.
apply exd_m2 in h3; apply exd_m1 in h3.
unfold m2.
elim eq_dart_dec; intro t0.
unfold m1.
do 2 rewrite fpoint_Split.
intros t3 t4 t5 t6.
unfold not in H17.
apply H17 with da dc; try assumption.
auto with myorientation.
do 2 rewrite fpoint_Split.
unfold m1.
do 2 rewrite fpoint_Split.
intros t3 t4 t5 t6.
unfold not in H17.
apply H17 with da dc; try assumption.
auto with myorientation.
elim (eq_dart_dec x db); intro e4; try subst db.
elim (eq_dart_dec max dc); [tauto|idtac].
elim (eq_dart_dec x dc); [tauto|idtac].
intros t1 t2.
apply exd_m3_1 in h1.
elimination h1.
apply eq_sym in h1; contradiction.
elimination h1.
apply eq_sym in h1; contradiction.
apply exd_m2 in h1; apply exd_m1 in h1.
apply exd_m3_1 in h3.
elimination h3.
apply eq_sym in h3; contradiction.
elimination h3.
apply eq_sym in h3; contradiction.
apply exd_m2 in h3; apply exd_m1 in h3.
unfold m2.
elim eq_dart_dec; intro t0.
unfold m1.
do 2 rewrite fpoint_Split.
intros t3 t4 t5 t6.
unfold not in H17.
apply H17 with da dc; try assumption.
auto with myorientation.
do 2 rewrite fpoint_Split.
unfold m1.
do 2 rewrite fpoint_Split.
intros t3 t4 t5 t6.
unfold not in H17.
apply H17 with da dc; try assumption.
auto with myorientation.
elim (eq_dart_dec max dc); intro e5; try subst dc.
apply exd_m3_1 in h1.
elimination h1.
apply eq_sym in h1; contradiction.
elimination h1.
apply eq_sym in h1; contradiction.
apply exd_m2 in h1; apply exd_m1 in h1.
apply exd_m3_1 in h2.
elimination h2.
apply eq_sym in h2; contradiction.
elimination h2.
apply eq_sym in h2; contradiction.
apply exd_m2 in h2; apply exd_m1 in h2.
unfold m2.
elim eq_dart_dec; intro t0.
unfold m1.
do 2 rewrite fpoint_Split.
intros t3 t4 t5 t6.
unfold not in H17.
apply H17 with da db; try assumption.
auto with myorientation.
do 2 rewrite fpoint_Split.
unfold m1.
do 2 rewrite fpoint_Split.
intros t3 t4 t5 t6.
unfold not in H17.
apply H17 with da db; try assumption.
auto with myorientation.
elim (eq_dart_dec x dc); intro e6; try subst dc.
apply exd_m3_1 in h1.
elimination h1.
apply eq_sym in h1; contradiction.
elimination h1.
apply eq_sym in h1; contradiction.
apply exd_m2 in h1; apply exd_m1 in h1.
apply exd_m3_1 in h2.
elimination h2.
apply eq_sym in h2; contradiction.
elimination h2.
apply eq_sym in h2; contradiction.
apply exd_m2 in h2; apply exd_m1 in h2.
unfold m2.
elim eq_dart_dec; intro t0.
unfold m1.
do 2 rewrite fpoint_Split.
intros t3 t4 t5 t6.
unfold not in H17.
apply H17 with da db; try assumption.
auto with myorientation.
do 2 rewrite fpoint_Split.
unfold m1.
do 2 rewrite fpoint_Split.
intros t3 t4 t5 t6.
unfold not in H17.
apply H17 with da db; try assumption.
auto with myorientation.
apply exd_m3_1 in h1.
elimination h1.
apply eq_sym in h1; contradiction.
elimination h1.
apply eq_sym in h1; contradiction.
apply exd_m3_1 in h2.
elimination h2.
apply eq_sym in h2; contradiction.
elimination h2.
apply eq_sym in h2; contradiction.
apply exd_m3_1 in h3.
elimination h3.
apply eq_sym in h3; contradiction.
elimination h3.
apply eq_sym in h3; contradiction.
apply is_noalign_m2; assumption.
Qed.

(* ================================ *)

Lemma not_eqc_m3_x_max : ~ eqc m3 x max.
Proof.
unfold m3; simpl eqc; intro h.
elimination h. destruct h as [h1 h2].
apply H15; assumption.
elimination h. destruct h as [h1 h2].
apply H15; rewrite h2; trivial.
apply eqc_exd_exd in h.
destruct h as [h1 h2].
apply not_exd_m2_x; assumption.
Qed.

Lemma not_eqc_m3_x_l : ~ eqc m3 x l.
Proof.
unfold m3; simpl eqc; intro h.
elimination h. destruct h as [h1 h2].
apply H15; assumption.
elimination h. destruct h as [h1 h2].
apply H11; rewrite <- h2; apply exd_left.
apply eqc_exd_exd in h.
destruct h as [h1 h2].
apply not_exd_m2_x; assumption.
Qed.

Lemma not_eqc_m3_x_l0 : ~ eqc m3 x l0.
Proof.
unfold m3; simpl eqc; intro h.
elimination h. destruct h as [h1 h2].
apply H15; assumption.
elimination h. destruct h as [h1 h2].
apply H11; rewrite <- h2.
apply exd_cA. exact H1. apply exd_left.
apply eqc_exd_exd in h.
destruct h as [h1 h2].
apply not_exd_m2_x; assumption.
Qed.

Lemma not_eqc_m3_max_l : ~ eqc m3 max l.
Proof.
unfold m3; simpl eqc; intro h.
elimination h. destruct h as [h1 h2].
apply H12; rewrite <- h2; apply exd_left.
elimination h. destruct h as [h1 h2].
apply H15; rewrite h1; trivial.
apply eqc_exd_exd in h.
destruct h as [h1 h2].
apply not_exd_m2_max; assumption.
Qed.

Lemma not_eqc_m3_max_l0 : ~ eqc m3 max l0.
Proof.
unfold m3; simpl eqc; intro h.
elimination h. destruct h as [h1 h2].
apply H12; rewrite <- h2.
apply exd_cA. exact H1. apply exd_left.
elimination h. destruct h as [h1 h2].
apply H15; rewrite h1; trivial.
apply eqc_exd_exd in h.
destruct h as [h1 h2].
apply not_exd_m2_max; assumption.
Qed.

Lemma not_eqc_m3_r_r0 : l0 <> r -> ~ eqc m3 r r0.
Proof.
intro h0; unfold m3; simpl eqc; intro h.
elimination h. destruct h as [h1 h2].
apply H12; rewrite <- h1; apply exd_right.
elimination h. destruct h as [h1 h2].
apply H11; rewrite <- h1; apply exd_right.
apply not_eqc_m2_r_r0; assumption.
Qed.

Lemma expf_m3_l_r : expf m3 l r.
Proof.
unfold m3; apply expf_I.
simpl; split. apply inv_hmap_m2.
unfold prec_I; split.
assumption. apply not_exd_m2_x.
unfold prec_I; split. assumption.
intro h; simpl in h; elimination h.
apply H15; assumption.
apply not_exd_m2_max; assumption.
simpl; right; apply exd_m2; apply exd_m1; apply exd_left.
intro h; apply H12; rewrite h; apply exd_left.
apply expf_I. apply inv_hmap_m2.
unfold prec_I; split.
assumption. apply not_exd_m2_x.
apply exd_m2; apply exd_m1; apply exd_left.
intro h; apply H11; rewrite h; apply exd_left.
apply expf_m2_l_r.
Qed.

Lemma expf_m3_l0_r0 : expf m3 l0 r0.
Proof.
unfold m3; apply expf_I.
simpl; split. apply inv_hmap_m2.
unfold prec_I; split.
assumption. apply not_exd_m2_x.
unfold prec_I; split. assumption.
intro h; simpl in h; elimination h.
apply H15; assumption.
apply not_exd_m2_max; assumption.
simpl; right; apply exd_m2; apply exd_m1.
apply exd_cA. assumption. apply exd_left.
intro h; apply H12; rewrite h.
apply exd_cA. assumption. apply exd_left.
apply expf_I. apply inv_hmap_m2.
unfold prec_I; split.
assumption. apply not_exd_m2_x.
apply exd_m2; apply exd_m1.
apply exd_cA. assumption. apply exd_left.
intro h; apply H11; rewrite h.
apply exd_cA. assumption. apply exd_left.
apply expf_m2_l0_r0.
Qed.

(* ===== *)

Lemma not_expv_m3_max_x : ~ expv m3 max x.
Proof.
unfold m3; apply not_expv_I; try apply not_expv_I; simpl.
unfold prec_I; repeat split; try assumption.
apply inv_hmap_m2. apply not_exd_m2_x.
intro h; elimination h; try contradiction.
apply not_exd_m2_max; assumption. intuition.
apply inv_hmap_m2. apply not_exd_m2_x. intuition.
apply not_exd_not_expv. apply not_exd_m2_max; assumption.
Qed.

(* ================================ *)
(* ========== ########## ========== *)
(* ================================ *)

Lemma inv_hmap_m4 : inv_hmap m4.
Proof.
unfold m4; apply inv_hmap_Merge1.
apply inv_hmap_m3.
unfold m3; simpl; tauto.
unfold m3; simpl; tauto.
apply not_expv_m3_max_x.
Qed.

Lemma exd_m4 : forall (da:dart),
  exd m3 da <-> exd m4 da.
Proof.
intro da; split; unfold m4; intro h.
apply -> exd_Merge; assumption.
apply <- exd_Merge in h; assumption.
Qed.

Lemma cA_m4_zero_da : forall (da:dart),
  exd m4 da -> cA m4 zero da = cA m3 zero da.
Proof.
intros da h; unfold m4; rewrite cA_Merge.
simpl; trivial. apply inv_hmap_m3.
Qed.

Lemma cA_m4_one_x : cA m4 one x = max.
Proof.
unfold m4; rewrite cA_Merge.
simpl; eqdartdec; trivial.
apply inv_hmap_m3.
Qed.

Lemma cA_m4_one_max : cA m4 one max = x.
Proof.
unfold m4; rewrite cA_Merge.
simpl; eqdartdec; trivial.
apply inv_hmap_m3.
Qed.

Lemma cA_m4_one_da : forall (da:dart),
  exd m4 da -> da <> x -> da <> max ->
  cA m4 one da = cA m3 one da.
Proof.
intros da h1 h2 h3; unfold m4; rewrite cA_Merge.
simpl; eqdartdec; trivial. apply inv_hmap_m3.
Qed.

Lemma inv_gmap_m4 : inv_gmap m4.
Proof.
unfold inv_gmap; intros k da Hda; induction k.
(* k = zero *)
rewrite cA_m4_zero_da; try assumption.
rewrite cA_m4_zero_da; try assumption.
apply inv_gmap_m3; apply <- exd_m4; try assumption.
apply -> exd_cA; [exact Hda | apply inv_hmap_m4].
(* k = one *)
elim (eq_dart_dec da x); intro h1.
subst da; rewrite cA_m4_one_x.
rewrite cA_m4_one_max; trivial.
elim (eq_dart_dec da max); intro h2.
subst da; rewrite cA_m4_one_max.
rewrite cA_m4_one_x; trivial.
rewrite cA_m4_one_da; try assumption.
rewrite cA_m4_one_da; try assumption.
apply inv_gmap_m3; apply <- exd_m4; try assumption.
apply -> exd_cA; [exact Hda | apply inv_hmap_m4].
rewrite cA_m4_one_da; try assumption.
rewrite cA_m3_one_da; try assumption.
intro h; apply sym_eq in h.
apply subst_cA_cA_1 in h. rewrite not_exd_cA_1 in h.
apply exd_not_nil with m4 da; try assumption.
apply inv_hmap_m4. apply inv_hmap_m2.
apply not_exd_m2_x. apply inv_hmap_m2.
apply exd_m4 in Hda; apply exd_m3_1 in Hda; try tauto.
apply <- exd_m4; assumption.
rewrite cA_m4_one_da; try assumption.
rewrite cA_m3_one_da; try assumption.
intro h; apply sym_eq in h.
apply subst_cA_cA_1 in h. rewrite not_exd_cA_1 in h.
apply exd_not_nil with m4 da; try assumption.
apply inv_hmap_m4. apply inv_hmap_m2.
apply not_exd_m2_max. apply inv_hmap_m2.
apply exd_m4 in Hda; apply exd_m3_1 in Hda; try tauto.
apply <- exd_m4; assumption.
Qed.

Lemma planar_m4 : planar m4.
Proof.
unfold m4; apply <- planarity_crit_Merge1. split.
apply planar_m3. left; unfold m3; simpl; intro h.
elimination h; try tauto. elimination h; try intuition.
apply eqc_exd_exd in h; apply not_exd_m2_x; intuition.
apply not_expv_m3_max_x. unfold m3; simpl; tauto.
unfold m3; simpl; tauto. apply inv_hmap_m3.
Qed.

Open Scope Z_scope.

Lemma nd_m4 : nd m4 = nd m3.
Proof.
unfold m4; apply nd_Merge.
Qed.

Lemma ne_m4 : ne m4 = ne m3.
Proof.
unfold m4; apply ne_Merge1.
apply inv_hmap_m3.
unfold m3; simpl; tauto.
apply not_expv_m3_max_x.
Qed.

Lemma nv_m4 : nv m4 = nv m3 - 1.
Proof.
unfold m4; apply nv_Merge1.
apply inv_hmap_m3.
unfold m3; simpl; tauto.
apply not_expv_m3_max_x.
Qed.

Lemma Iter_cF_m3_i_max : forall (i:nat),
  Iter (cF m3) i max = max.
Proof.
intro i; induction i; simpl; try trivial.
rewrite IHi; unfold cF.
rewrite <- eq_cA_cA_1. rewrite <- eq_cA_cA_1.
rewrite cA_m3_zero_max. apply cA_m3_one_max.
apply inv_hmap_m3. apply inv_gmap_m3.
apply inv_hmap_m3. apply inv_gmap_m3.
Qed.

Lemma nf_m4 : nf m4 = nf m3 - 1.
Proof.
unfold m4; rewrite nf_Merge1.
elim expf_dec; intro h; try ring.
assert False; [idtac|tauto].
unfold expf, MF.expo in h.
destruct h as [h1 [h2 h3]].
elim h3; clear h3; intros i hi.
unfold MF.f, McF.f in hi.
rewrite cA_m3_zero_x in hi.
rewrite Iter_cF_m3_i_max in hi; intuition.
apply inv_hmap_m3.
unfold m3; simpl; tauto.
unfold m3; simpl; tauto.
Qed.

Lemma nc_m4 : nc m4 = nc m3 - 1.
Proof.
unfold m4; rewrite nc_Merge.
elim eqc_dec; intro h; try ring.
assert False; [idtac|tauto].
unfold m3 in h; simpl in h.
elimination h; try tauto.
elimination h; try intuition.
apply eqc_exd_exd in h.
apply not_exd_m2_x; intuition.
apply inv_hmap_m3.
unfold m3; simpl; tauto.
unfold m3; simpl; tauto.
Qed.

Open Scope nat_scope.

Lemma is_well_emb_m4 : is_well_emb m4.
Proof.
unfold is_well_emb; intros da db h1 h2 h3.
apply exd_m4 in h1; apply exd_m4 in h2.
unfold m4; split; intro h4.
(* expv da db *)
do 2 rewrite fpoint_Merge.
apply expv_Merge1_CNS in h4; try assumption.
elimination h4.
generalize (is_well_emb_m3 da db h1 h2 h3).
intros [h5 h6]; apply h5; assumption.
elimination h4.
destruct h4 as [h4 h5].
elimination h1; try subst da.
elimination h2; try subst db; trivial.
elimination h2; try subst db.
simpl; eqdartdec; trivial.
assert False; [idtac|tauto].
apply expv_I in h5.
elimination h5.
destruct h5 as [h5 h6]; intuition.
apply expv_I in h5.
elimination h5.
destruct h5 as [h5 h6]; subst db.
apply not_exd_m2_x; assumption.
apply not_exd_not_expv with m2 x db; try assumption.
apply not_exd_m2_x. apply inv_hmap_m2. apply not_exd_m2_x.
simpl; unfold prec_I; repeat split; try assumption.
apply inv_hmap_m2. apply not_exd_m2_x.
intro h; simpl in h; elimination h; try contradiction.
apply not_exd_m2_max; assumption.
elimination h1; try subst da.
assert False; [idtac|tauto].
apply not_expv_m3_max_x; assumption.
assert False; [idtac|tauto].
apply expv_I in h4.
elimination h4.
destruct h4 as [h4 h6]; subst da.
apply not_exd_m2_max; assumption.
apply expv_I in h4.
elimination h4.
destruct h4 as [h4 h6]; intuition.
apply not_exd_not_expv with m2 max da; try assumption.
apply not_exd_m2_max. apply inv_hmap_m2. apply not_exd_m2_x.
simpl; unfold prec_I; repeat split; try assumption.
apply inv_hmap_m2. apply not_exd_m2_x.
intro h; simpl in h; elimination h; try contradiction.
apply not_exd_m2_max; assumption.
destruct h4 as [h4 h5].
elimination h1; try subst da.
assert False; [idtac|tauto].
apply not_expv_m3_max_x; apply expv_symm.
apply inv_hmap_m3. unfold expv in h5; assumption.
elimination h1; try subst da.
elimination h2; try subst db.
simpl; eqdartdec; trivial.
elimination h2; try subst db; trivial.
assert False; [idtac|tauto].
apply expv_I in h4.
elimination h4.
destruct h4 as [h4 h6]; subst db.
apply not_exd_m2_max; assumption.
apply expv_I in h4.
elimination h4.
destruct h4 as [h4 h6]; intuition.
apply not_exd_not_expv with m2 max db; try assumption.
apply not_exd_m2_max. apply inv_hmap_m2. apply not_exd_m2_x.
simpl; unfold prec_I; repeat split; try assumption.
apply inv_hmap_m2. apply not_exd_m2_x.
intro h; simpl in h; elimination h; try contradiction.
apply not_exd_m2_max; assumption.
assert False; [idtac|tauto].
apply expv_I in h5.
elimination h5.
destruct h5 as [h5 h6]; intuition.
apply expv_I in h5.
elimination h5.
destruct h5 as [h5 h6]; subst da.
apply not_exd_m2_x; assumption.
apply not_exd_not_expv with m2 x da; try assumption.
apply not_exd_m2_x. apply inv_hmap_m2. apply not_exd_m2_x.
simpl; unfold prec_I; repeat split; try assumption.
apply inv_hmap_m2. apply not_exd_m2_x.
intro h; simpl in h; elimination h; try contradiction.
apply not_exd_m2_max; assumption.
apply inv_hmap_m3.
unfold m3; simpl; tauto.
unfold m3; simpl; tauto.
apply not_expv_m3_max_x.
(* expe da db *)
do 2 rewrite fpoint_Merge.
apply -> expe_Merge1 in h4.
generalize (is_well_emb_m3 da db h1 h2 h3).
intros [h5 h6]; apply h6; assumption.
unfold m3; simpl; tauto.
unfold m3; simpl; tauto.
apply inv_hmap_m3.
Qed.

Lemma is_neq_point_m4 : is_neq_point m4.
Proof.
unfold is_neq_point; intros da db h1 h2.
apply exd_m4 in h1; apply exd_m4 in h2.
unfold m4. do 2 rewrite fpoint_Merge.
intro h3; unfold m3; simpl.
elim (eq_dart_dec max da); intro e1; try subst da.
elim (eq_dart_dec max db); intro e2; try subst db.
intro h; clear h; apply h3.
unfold expv, MA1.MfcA.expo. split.
apply -> exd_Merge; assumption.
unfold MA1.MfcA.f, MA1.McAMd.f, Md1.kd.
exists 0; simpl; trivial.
elim (eq_dart_dec x db); intro e3; try subst db.
intro h; clear h; apply h3.
unfold expv, MA1.MfcA.expo. split.
apply -> exd_Merge; assumption.
unfold MA1.MfcA.f, MA1.McAMd.f, Md1.kd.
exists 1; simpl Iter; eqdartdec; trivial.
apply not_eq_sym. unfold m2.
elim (eq_dart_dec l0 r); intro h0.
unfold m1. rewrite fpoint_Split.
apply H16. apply exd_m3_1 in h2.
elimination h2. subst db; tauto.
elimination h2. subst db; tauto.
apply exd_m1; apply exd_m2; assumption.
rewrite fpoint_Split.
unfold m1. rewrite fpoint_Split.
apply H16. apply exd_m3_1 in h2.
elimination h2. subst db; tauto.
elimination h2. subst db; tauto.
apply exd_m1; apply exd_m2; assumption.
elim (eq_dart_dec x da); intro e2; try subst da.
elim (eq_dart_dec max db); intro e2; try subst db.
intro h; clear h; apply h3.
apply expv_Merge1_CNS; try assumption.
apply inv_hmap_m3. apply not_expv_m3_max_x.
right; right; split.
unfold expv, MA1.MfcA.expo.
split. assumption.
unfold MA1.MfcA.f, MA1.McAMd.f, Md1.kd.
exists 0; simpl; trivial.
unfold expv, MA1.MfcA.expo.
split. assumption.
unfold MA1.MfcA.f, MA1.McAMd.f, Md1.kd.
exists 0; simpl; trivial.
elim (eq_dart_dec x db); intro e3; try subst db.
intro h; clear h; apply h3.
unfold expv, MA1.MfcA.expo. split.
apply -> exd_Merge; assumption.
unfold MA1.MfcA.f, MA1.McAMd.f, Md1.kd.
exists 0; simpl; trivial.
apply not_eq_sym. unfold m2.
elim (eq_dart_dec l0 r); intro h0.
unfold m1. rewrite fpoint_Split.
apply H16. apply exd_m3_1 in h2.
elimination h2. subst db; tauto.
elimination h2. subst db; tauto.
apply exd_m1; apply exd_m2; assumption.
rewrite fpoint_Split.
unfold m1. rewrite fpoint_Split.
apply H16. apply exd_m3_1 in h2.
elimination h2. subst db; tauto.
elimination h2. subst db; tauto.
apply exd_m1; apply exd_m2; assumption.
elim (eq_dart_dec max db); intro e3; try subst db.
unfold m2.
elim (eq_dart_dec l0 r); intro h0.
unfold m1. rewrite fpoint_Split.
apply H16. apply exd_m3_1 in h1.
elimination h1. subst da; tauto.
elimination h1. subst da; tauto.
apply exd_m1; apply exd_m2; assumption.
rewrite fpoint_Split.
unfold m1. rewrite fpoint_Split.
apply H16. apply exd_m3_1 in h1.
elimination h1. subst da; tauto.
elimination h1. subst da; tauto.
apply exd_m1; apply exd_m2; assumption.
elim (eq_dart_dec x db); intro e4; try subst db.
unfold m2.
elim (eq_dart_dec l0 r); intro h0.
unfold m1. rewrite fpoint_Split.
apply H16. apply exd_m3_1 in h1.
elimination h1. subst da; tauto.
elimination h1. subst da; tauto.
apply exd_m1; apply exd_m2; assumption.
rewrite fpoint_Split.
unfold m1. rewrite fpoint_Split.
apply H16. apply exd_m3_1 in h1.
elimination h1. subst da; tauto.
elimination h1. subst da; tauto.
apply exd_m1; apply exd_m2; assumption.
apply is_neq_point_m2.
apply exd_m3_1 in h1.
elimination h1. subst da; tauto.
elimination h1. subst da; tauto.
assumption.
apply exd_m3_1 in h2.
elimination h2. subst db; tauto.
elimination h2. subst db; tauto.
assumption.
intro h; apply h3.
apply expv_Merge1_CNS; try assumption.
apply inv_hmap_m3.
unfold m3; simpl; tauto.
unfold m3; simpl; tauto.
apply not_expv_m3_max_x.
left.
unfold m3.
unfold expv, MA1.MfcA.expo. split.
simpl; simpl in h1; assumption.
unfold expv, MA1.MfcA.expo in h.
destruct h as [ha hb].
elim hb; clear hb.
intros i h.
exists i.
rewrite Iter_MA1McAMdf_I; try assumption.
rewrite Iter_MA1McAMdf_I; try assumption.
apply inv_hmap_m2.
apply not_exd_m2_x.
simpl; split. apply inv_hmap_m2.
unfold prec_I; split. assumption.
apply not_exd_m2_x.
simpl. intro h0.
elimination h0.
contradiction.
apply not_exd_m2_max; assumption.
simpl. right; assumption.
Qed.

Lemma is_noalign_m4 : is_noalign m4.
Proof.
unfold is_noalign, m4; intros da db dc h1 h2 h3 h4 h5 h6.
apply exd_m4 in h1; apply exd_m4 in h2; apply exd_m4 in h3.
do 3 rewrite fpoint_Merge in *; apply is_noalign_m3; assumption.
Qed.

(* ================================ *)

Lemma expf_m4_x_max : expf m4 x max.
Proof.
unfold expf; split. apply inv_hmap_m4. unfold m4.
assert (t1: inv_hmap m3). apply inv_hmap_m3.
apply (expof_Merge1_CNS m3 max x x max t1).
unfold m3; simpl; left; trivial.
unfold m3; simpl; right; left; trivial.
apply not_expv_m3_max_x.
unfold m3; simpl; right; left; trivial.
rewrite cA_m3_zero_x.
elim expof_dec; intro h0.
assert False; [idtac|tauto].
apply not_eqc_m3_x_max.
apply expf_eqc; assumption.
right; left; split; apply expf_refl.
exact t1. simpl; right; left; trivial.
exact t1. simpl; left; trivial.
Qed.

Lemma not_eqc_m4_x_l : ~ eqc m4 x l.
Proof.
intro h; apply eqc_Merge in h.
elimination h.
apply not_eqc_m3_x_l; assumption.
elimination h; destruct h as [h1 h2].
apply not_eqc_m3_x_l; assumption.
apply not_eqc_m3_max_l; assumption.
apply inv_hmap_m3.
unfold m3; simpl; left; trivial.
unfold m3; simpl; right; left; trivial.
Qed.

Lemma not_eqc_m4_x_l0 : ~ eqc m4 x l0.
Proof.
intro h; apply eqc_Merge in h.
elimination h.
apply not_eqc_m3_x_l0; assumption.
elimination h; destruct h as [h1 h2].
apply not_eqc_m3_x_l0; assumption.
apply not_eqc_m3_max_l0; assumption.
apply inv_hmap_m3.
unfold m3; simpl; left; trivial.
unfold m3; simpl; right; left; trivial.
Qed.

Lemma not_eqc_m4_r_r0 : l0 <> r -> ~ eqc m4 r r0.
Proof.
intros h0 h; apply eqc_Merge in h.
elimination h.
apply not_eqc_m3_r_r0; assumption.
elimination h; destruct h as [h1 h2].
apply not_eqc_m3_x_l0.
apply eqc_trans with r0. exact h2.
apply expf_eqc. apply inv_hmap_m3.
apply expf_symm; apply expf_m3_l0_r0.
apply not_eqc_m3_max_l0.
apply eqc_trans with r0. exact h2.
apply expf_eqc. apply inv_hmap_m3.
apply expf_symm; apply expf_m3_l0_r0.
apply inv_hmap_m3.
unfold m3; simpl; left; trivial.
unfold m3; simpl; right; left; trivial.
Qed.

Lemma expf_m4_l_r : expf m4 l r.
Proof.
unfold expf; split. apply inv_hmap_m4. unfold m4.
assert (t1: inv_hmap m3). apply inv_hmap_m3.
apply (expof_Merge1_CNS m3 max x l r t1).
unfold m3; simpl; left; trivial.
unfold m3; simpl; right; left; trivial.
apply not_expv_m3_max_x.
apply exd_m3_2; apply exd_m2; apply exd_m1; apply exd_left.
rewrite cA_m3_zero_x.
elim expof_dec; intro h0.
assert False; [idtac|tauto].
apply not_eqc_m3_x_max.
apply expf_eqc; assumption.
left; apply expf_m3_l_r.
Qed.

Lemma expf_m4_l0_r0 : expf m4 l0 r0.
Proof.
unfold expf; split. apply inv_hmap_m4. unfold m4.
assert (t1: inv_hmap m3). apply inv_hmap_m3.
apply (expof_Merge1_CNS m3 max x l0 r0 t1).
unfold m3; simpl; left; trivial.
unfold m3; simpl; right; left; trivial.
apply not_expv_m3_max_x.
apply exd_m3_2; apply exd_m2; apply exd_m1.
apply exd_cA. assumption. apply exd_left.
rewrite cA_m3_zero_x.
elim expof_dec; intro h0.
assert False; [idtac|tauto].
apply not_eqc_m3_x_max.
apply expf_eqc; assumption.
left; apply expf_m3_l0_r0.
Qed.

(* ===== *)

Lemma not_eqc_m4_l_max : ~ eqc m4 l max.
Proof.
intro h. apply not_eqc_m4_x_l.
apply eqc_trans with max.
apply expf_eqc. apply inv_hmap_m4.
apply expf_m4_x_max.
apply eqc_symm; exact h.
Qed.

Lemma not_expe_m4_l_max : ~ expe m4 l max.
Proof.
unfold m4.
rewrite expe_Merge1.
unfold m3.
apply not_expe_I.
simpl; unfold prec_I.
repeat split; try assumption.
apply inv_hmap_m2.
apply not_exd_m2_x.
simpl; intro h.
elimination h.
contradiction.
apply not_exd_m2_max; assumption.
intro h; apply H12.
rewrite <- h; apply exd_left.
intro h; apply expe_symm in h.
apply not_exd_not_expe with (I m2 x t p) max l.
intro h0; simpl in h0.
elimination h0.
contradiction.
apply not_exd_m2_max; assumption.
assumption.
simpl; unfold prec_I.
repeat split; try assumption.
apply inv_hmap_m2.
apply not_exd_m2_x.
apply inv_hmap_m3.
unfold m3; simpl; tauto.
unfold m3; simpl; tauto.
Qed.

(* ================================ *)
(* ========== ########## ========== *)
(* ================================ *)

Lemma inv_hmap_m5 : inv_hmap m5.
Proof.
unfold m5; apply inv_hmap_Merge0.
apply inv_hmap_m4.
apply -> exd_m4.
apply exd_m3_2.
apply -> exd_m2.
apply -> exd_m1.
apply exd_left.
apply -> exd_m4.
unfold m3; simpl; tauto.
unfold m4.
rewrite expe_Merge1.
intro h.
apply expe_I in h.
elimination h.
destruct h as [h1 h2].
apply H12.
rewrite h1.
apply exd_left.
apply expe_I in h.
elimination h.
destruct h as [h1 h2].
contradiction.
apply expe_symm in h.
apply not_exd_not_expe with m2 max l; try assumption.
apply not_exd_m2_max.
apply inv_hmap_m2.
apply inv_hmap_m2.
apply not_exd_m2_x.
simpl; unfold prec_I; repeat split; try assumption.
apply inv_hmap_m2.
apply not_exd_m2_x.
intro h0; simpl in h0; elimination h0.
contradiction.
apply not_exd_m2_max; assumption.
apply inv_hmap_m3.
unfold m3; simpl; tauto.
unfold m3; simpl; tauto.
Qed.

Lemma exd_m5 : forall (da:dart),
  exd m4 da <-> exd m5 da.
Proof.
intro da; split; unfold m5; intro h.
apply -> exd_Merge; assumption.
apply <- exd_Merge in h; assumption.
Qed.

Lemma cA_m5_zero_l : cA m5 zero l = max.
Proof.
unfold m5; rewrite cA_Merge.
elim eq_dim_dec; try tauto.
intro h; clear h; eqdartdec; trivial.
apply inv_hmap_m4.
Qed.

Lemma cA_m5_zero_max : cA m5 zero max = l.
Proof.
unfold m5; rewrite cA_Merge.
elim eq_dim_dec; try tauto.
intro h; clear h.
elim eq_dart_dec; intro h1.
rewrite h1; trivial.
elim eq_dart_dec; intro h2.
rewrite cA_m4_zero_da.
apply cA_m3_zero_l.
apply -> exd_m4.
apply exd_m3_2.
apply -> exd_m2.
apply -> exd_m1.
apply exd_left.
assert False; [idtac|tauto].
apply h2.
rewrite <- eq_cA_cA_1.
rewrite cA_m4_zero_da.
apply cA_m3_zero_max.
apply -> exd_m4.
unfold m3; simpl; tauto.
apply inv_hmap_m4.
apply inv_gmap_m4.
apply inv_hmap_m4.
Qed.

Lemma cA_m5_zero_da : forall (da:dart),
  exd m5 da -> da <> l -> da <> max ->
  cA m5 zero da = cA m4 zero da.
Proof.
intros da h1 h2 h3.
unfold m5; rewrite cA_Merge.
elim eq_dim_dec; try tauto.
intro h; clear h.
elim eq_dart_dec; intro h4.
apply sym_eq in h4; contradiction.
elim eq_dart_dec; intro h5.
assert False; [idtac|tauto].
rewrite <- eq_cA_cA_1 in h5.
rewrite cA_m4_zero_da in h5.
rewrite cA_m3_zero_max in h5.
apply sym_eq in h5; contradiction.
apply -> exd_m4.
unfold m3; simpl; tauto.
apply inv_hmap_m4.
apply inv_gmap_m4.
clear H1 H2 H3 H4 H5 H6 H7 H8.
clear H9 H10 H11 H12 H13 H14 H15.
clear H0 h1 h2 h3 h4 h5.
trivial.
apply inv_hmap_m4.
Qed.

Lemma cA_m5_one_da : forall (da:dart),
  exd m5 da -> cA m5 one da = cA m4 one da.
Proof.
intros da h.
unfold m5; rewrite cA_Merge.
elim eq_dim_dec; try tauto.
intro h0; discriminate.
apply inv_hmap_m4.
Qed.

Lemma inv_gmap_m5 : inv_gmap m5.
Proof.
unfold inv_gmap; intros k da Hda; induction k.
(* k = zero *)
elim (eq_dart_dec da l); intro h1.
subst da; rewrite cA_m5_zero_l.
rewrite cA_m5_zero_max; tauto.
elim (eq_dart_dec da max); intro h2.
subst da; rewrite cA_m5_zero_max.
rewrite cA_m5_zero_l; tauto.
rewrite cA_m5_zero_da; try assumption.
rewrite cA_m5_zero_da; try assumption.
apply inv_gmap_m4; apply <- exd_m5; try assumption.
apply -> exd_cA; [exact Hda | apply inv_hmap_m5].
rewrite cA_m5_zero_da; try assumption.
rewrite cA_m4_zero_da; try assumption.
intro h; apply sym_eq in h.
apply subst_cA_cA_1 in h.
rewrite <- eq_cA_cA_1 in h.
rewrite cA_m3_zero_l in h; contradiction.
apply inv_hmap_m3. apply inv_gmap_m3. apply inv_hmap_m3.
apply exd_m5 in Hda; apply exd_m4 in Hda; assumption.
apply exd_m5 in Hda; assumption.
rewrite cA_m5_zero_da; try assumption.
rewrite cA_m4_zero_da; try assumption.
intro h; apply sym_eq in h.
apply subst_cA_cA_1 in h.
rewrite <- eq_cA_cA_1 in h.
rewrite cA_m3_zero_max in h; contradiction.
apply inv_hmap_m3. apply inv_gmap_m3. apply inv_hmap_m3.
apply exd_m5 in Hda; apply exd_m4 in Hda; assumption.
apply exd_m5 in Hda; assumption.
(* k = one *)
rewrite cA_m5_one_da; try assumption.
rewrite cA_m5_one_da; try assumption.
apply inv_gmap_m4; apply <- exd_m5; try assumption.
apply -> exd_cA; [exact Hda | apply inv_hmap_m5].
Qed.

Lemma planar_m5 : planar m5.
Proof.
unfold m5.
apply <- planarity_crit_Merge0.
split; try left.
apply planar_m4.
apply not_eqc_m4_l_max.
apply not_expe_m4_l_max.
apply -> exd_m4.
unfold m3; simpl; tauto.
apply -> exd_m4.
apply exd_m3_2.
apply -> exd_m2.
apply -> exd_m1.
apply exd_left.
apply inv_hmap_m4.
Qed.

Open Scope Z_scope.

Lemma nd_m5 : nd m5 = nd m4.
Proof.
unfold m5; apply nd_Merge.
Qed.

Lemma ne_m5 : ne m5 = ne m4 - 1.
Proof.
unfold m5; apply ne_Merge0.
apply inv_hmap_m4.
apply -> exd_m4.
unfold m3; simpl; tauto.
apply not_expe_m4_l_max.
Qed.

Lemma nv_m5 : nv m5 = nv m4.
Proof.
unfold m5; apply nv_Merge0.
apply inv_hmap_m4.
apply -> exd_m4.
unfold m3; simpl; tauto.
apply not_expe_m4_l_max.
Qed.

Lemma nf_m5 : nf m5 = nf m4 - 1.
Proof.
unfold m5; rewrite nf_Merge0.
pose (u:= cA_1 m4 one l); fold u.
elim expf_dec; intro h.
assert False; [idtac|tauto].
unfold m4 in h.
unfold expf in h.
destruct h as [h0 h]; clear h0.
apply (expof_Merge1_CNS m3 max x u max (inv_hmap_m3)) in h.
generalize h; clear h.
elim expof_dec; intros h h0.
unfold expof in h. clear h0.
rewrite cA_m3_zero_x in h.
cut (~ eqc m3 x max).
intro h0; apply h0.
apply expf_eqc; try assumption.
apply inv_hmap_m3.
unfold m3; simpl; clear u h.
intro h; elimination h.
destruct h as [h1 h2].
contradiction.
elimination h.
destruct h as [h1 h2].
apply H15; rewrite h2; trivial.
apply eqc_exd_exd in h.
destruct h as [h1 h2].
apply not_exd_m2_x; assumption.
elimination h0.
cut (~ eqc m3 u max).
intro h1; apply h1.
apply expf_eqc; try assumption.
apply inv_hmap_m3.
unfold m3; simpl; clear h h0.
intro h; elimination h.
destruct h as [h1 h2].
apply not_exd_m2_max.
apply -> exd_m2.
apply -> exd_m1.
rewrite <- h1.
unfold u.
rewrite <- eq_cA_cA_1.
rewrite cA_m4_one_da.
rewrite cA_m3_one_da.
rewrite cA_m2_one_da.
rewrite cA_m1_one_da.
apply -> exd_cA.
apply exd_left.
assumption.
apply -> exd_m1.
apply exd_left.
apply -> exd_m2.
apply -> exd_m1.
apply exd_left.
apply exd_m3_2.
apply -> exd_m2.
apply -> exd_m1.
apply exd_left.
intro h; apply H11.
rewrite <- h.
apply exd_left.
intro h; apply H12.
rewrite <- h.
apply exd_left.
apply -> exd_m4.
apply exd_m3_2.
apply -> exd_m2.
apply -> exd_m1.
apply exd_left.
intro h; apply H11.
rewrite <- h.
apply exd_left.
intro h; apply H12.
rewrite <- h.
apply exd_left.
apply inv_hmap_m4.
apply inv_gmap_m4.
elimination h.
destruct h as [h1 h2].
apply H15; rewrite h2; trivial.
apply eqc_exd_exd in h.
destruct h as [h1 h2].
apply not_exd_m2_max; assumption.
elimination h0.
destruct h0 as [h1 h2].
rewrite cA_m3_zero_x in h1.
cut (~ eqc m3 x u).
intro h3; apply h3.
apply expf_eqc; try assumption.
apply inv_hmap_m3.
unfold m3; simpl; clear h h1 h2.
intro h; elimination h.
destruct h as [h1 h2].
contradiction.
elimination h.
destruct h as [h1 h2].
apply not_exd_m2_x.
apply -> exd_m2.
apply -> exd_m1.
rewrite <- h2.
unfold u.
rewrite <- eq_cA_cA_1.
rewrite cA_m4_one_da.
rewrite cA_m3_one_da.
rewrite cA_m2_one_da.
rewrite cA_m1_one_da.
apply -> exd_cA.
apply exd_left.
assumption.
apply -> exd_m1.
apply exd_left.
apply -> exd_m2.
apply -> exd_m1.
apply exd_left.
apply exd_m3_2.
apply -> exd_m2.
apply -> exd_m1.
apply exd_left.
intro h; apply H11.
rewrite <- h.
apply exd_left.
intro h; apply H12.
rewrite <- h.
apply exd_left.
apply -> exd_m4.
apply exd_m3_2.
apply -> exd_m2.
apply -> exd_m1.
apply exd_left.
intro h; apply H11.
rewrite <- h.
apply exd_left.
intro h; apply H12.
rewrite <- h.
apply exd_left.
apply inv_hmap_m4.
apply inv_gmap_m4.
apply eqc_exd_exd in h.
destruct h as [h1 h2].
apply not_exd_m2_x; assumption.
destruct h0 as [h1 h2].
contradiction.
unfold m3; simpl; tauto.
unfold m3; simpl; tauto.
apply not_expv_m3_max_x.
unfold u.
rewrite <- eq_cA_cA_1.
rewrite cA_m4_one_da.
apply -> exd_cA.
apply exd_m3_2.
apply -> exd_m2.
apply -> exd_m1.
apply exd_left.
apply inv_hmap_m3.
apply -> exd_m4.
apply exd_m3_2.
apply -> exd_m2.
apply -> exd_m1.
apply exd_left.
intro h0; apply H11.
rewrite <- h0.
apply exd_left.
intro h0; apply H12.
rewrite <- h0.
apply exd_left.
apply inv_hmap_m4.
apply inv_gmap_m4.
ring_simplify; tauto.
apply inv_hmap_m4.
apply -> exd_m4.
apply exd_m3_2.
apply -> exd_m2.
apply -> exd_m1.
apply exd_left.
apply -> exd_m4.
unfold m3; simpl; tauto.
Qed.

Lemma nc_m5 : nc m5 = nc m4 - 1.
Proof.
unfold m5; rewrite nc_Merge.
elim eqc_dec; intro h.
assert False; [idtac|tauto].
apply not_eqc_m4_l_max.
assumption.
ring_simplify; tauto.
apply inv_hmap_m4.
apply -> exd_m4.
apply exd_m3_2.
apply -> exd_m2.
apply -> exd_m1.
apply exd_left.
apply -> exd_m4.
unfold m3; simpl; tauto.
Qed.

Open Scope nat_scope.

Lemma toto : forall (m:fmap)(x:dart)(y:dart),
  cA m zero x = x -> expe m x y -> x = y.
Proof.
intros m0 x0 y0 h1 h2.
assert (forall i:nat, Iter (MA0.McAMd.f m0) i x0 = x0).
induction i; simpl; trivial. rewrite IHi.
unfold MA0.McAMd.f, Md0.kd; simpl; assumption.
unfold expe, MA0.MfcA.expo, MA0.MfcA.f in h2.
destruct h2 as [h2 h3].
elim h3; clear h3; intros i hi.
rewrite (H i) in hi; assumption.
Qed.

Lemma is_well_emb_m5 : is_well_emb m5.
Proof.
unfold is_well_emb; intros da db h1 h2 h3.
apply exd_m5 in h1; apply exd_m5 in h2.
unfold m5; split; intro h4.
(* expv da db *)
do 2 rewrite fpoint_Merge.
apply -> expv_Merge0 in h4.
generalize (is_well_emb_m4 da db h1 h2 h3).
intros [h5 h6]; apply h5; assumption.
apply -> exd_m4.
unfold m3; simpl; tauto.
apply -> exd_m4.
apply exd_m3_2.
apply -> exd_m2.
apply -> exd_m1.
apply exd_left.
apply inv_hmap_m4.
(* expe da db *)
do 2 rewrite fpoint_Merge.
apply -> expe_Merge0_CNS in h4; try assumption.
elimination h4.
generalize (is_well_emb_m4 da db h1 h2 h3).
intros [h5 h6]; apply h6; assumption.
elimination h4.

destruct h4 as [h4 h5].
apply toto in h4.
apply toto in h5.
subst da db.
unfold m4 at 2.
rewrite fpoint_Merge.
unfold m3; simpl fpoint at 2.
eqdartdec.

unfold m4.
rewrite fpoint_Merge.
unfold m3.
simpl.
eqdartdec.
elim eq_dart_dec; intro h.
rewrite h in H11.
assert False; [idtac|tauto].
apply H11.
apply exd_left.
unfold m2.
elim eq_dart_dec; intro h0.
unfold m1.
rewrite fpoint_Split.
apply H16.
apply exd_left.
rewrite fpoint_Split.
unfold m1.
rewrite fpoint_Split.
apply H16.
apply exd_left.

rewrite cA_m4_zero_da.
apply cA_m3_zero_max.
apply -> exd_m4.
unfold m3; simpl; tauto.
rewrite cA_m4_zero_da.
apply cA_m3_zero_l.
apply -> exd_m4.
apply exd_m3_2.
apply -> exd_m2.
apply -> exd_m1.
apply exd_left.

destruct h4 as [h4 h5].
apply toto in h4.
apply toto in h5.
subst da db.
unfold m4 at 1.
rewrite fpoint_Merge.
unfold m3; simpl fpoint at 1.
eqdartdec.
apply not_eq_sym.
unfold m4.
rewrite fpoint_Merge.
unfold m3.
simpl.
eqdartdec.
elim eq_dart_dec; intro h.
rewrite h in H11.
assert False; [idtac|tauto].
apply H11.
apply exd_left.
unfold m2.
elim eq_dart_dec; intro h0.
unfold m1.
rewrite fpoint_Split.
apply H16.
apply exd_left.
rewrite fpoint_Split.
unfold m1.
rewrite fpoint_Split.
apply H16.
apply exd_left.

rewrite cA_m4_zero_da.
apply cA_m3_zero_max.
apply -> exd_m4.
unfold m3; simpl; tauto.
rewrite cA_m4_zero_da.
apply cA_m3_zero_l.
apply -> exd_m4.
apply exd_m3_2.
apply -> exd_m2.
apply -> exd_m1.
apply exd_left.

apply not_expe_m4_l_max.
apply -> exd_m4.
unfold m3; simpl; tauto.
apply -> exd_m4.
apply exd_m3_2.
apply -> exd_m2.
apply -> exd_m1.
apply exd_left.
apply inv_hmap_m4.
Qed.

Lemma is_neq_point_m5 : is_neq_point m5.
Proof.
unfold is_neq_point; intros da db h1 h2.
apply exd_m5 in h1; apply exd_m5 in h2.
unfold m5. do 2 rewrite fpoint_Merge.
intro h3. rewrite expv_Merge0 in h3.
apply is_neq_point_m4; try assumption.
apply inv_hmap_m4.
apply exd_m4. apply exd_m3_2. apply exd_m2.
apply exd_m1. apply exd_left.
apply exd_m4. unfold m3; simpl; tauto.
Qed.

Lemma is_noalign_m5 : is_noalign m5.
Proof.
unfold is_noalign, m5; intros da db dc h1 h2 h3 h4 h5 h6.
apply exd_m5 in h1; apply exd_m5 in h2; apply exd_m5 in h3.
do 3 rewrite fpoint_Merge in *; apply is_noalign_m4; assumption.
Qed.

(* ================================ *)

Lemma expf_m1_l_cA_m_one_l : expf m1 l (cA m one l).
Proof.
unfold m1.
unfold expf; split. apply inv_hmap_m1.
apply (expof_Split0_CNS m l l0 l (cA m one l) H1).
apply cracke_m_l_l0. apply exd_left.
assert (h1: cA_1 m one l0 = cA m one l0).
rewrite eq_cA_cA_1; tauto.
elim expof_dec; intro h0.
assert False; [idtac|tauto].
rewrite h1 in h0; fold l0 in h0.
apply not_expf_m_l0_cA_m_one_l0.
apply expf_expof; split; assumption.
do 2 right; split; try rewrite h1.
apply expf_cA_cA; try assumption. apply exd_left.
rewrite <- cA_m_zero_l0. apply expf_symm.
apply expf_cA_cA; try assumption.
apply exd_cA. assumption. apply exd_left.
Qed.

Lemma expf_m2_l_cA_m_one_l : expf m2 l (cA m one l).
Proof.
unfold expf; split. apply inv_hmap_m2.
unfold m2; elim eq_dart_dec; intro h.
apply eq_l0_r_r0_l in h. rewrite <- h.
apply expf_m1_r0_cA_m_one_r0.
assert (t1: inv_hmap m1). apply inv_hmap_m1.
assert (t2: inv_gmap m1). apply inv_gmap_m1.
apply (expof_Split0_CNS m1 r0 r l (cA m one l) t1).
apply cracke_m1_r0_r; assumption.
apply exd_m1; apply exd_left.
assert (t3: cA m1 zero r0 = r).
 rewrite cA_m1_zero_da. apply cA_m_zero_r0.
 apply exd_m1; apply exd_cA_1. exact H1. apply exd_right.
 intro h0; apply h; apply eq_l0_r_r0_l; assumption.
 apply not_eq_sym; apply neq_l0_r0. rewrite t3.
assert (t4: cA_1 m1 one r = r1).
 rewrite <- eq_cA_cA_1; try assumption.
 rewrite cA_m1_one_da. unfold r1; tauto.
 apply exd_m1; apply exd_right. rewrite t4.
elim expof_dec; intro h0. left; split.
apply betweenf_m1_r1_l_r. apply betweenf_m1_r1_l1_r.
assert False; [idtac|tauto]. apply h0.
apply expf_m1_r_r1.
Qed.

Lemma expf_m3_l_cA_m_one_l : expf m3 l (cA m one l).
Proof.
unfold m3; apply expf_I.
simpl; split. apply inv_hmap_m2.
unfold prec_I; split.
assumption. apply not_exd_m2_x.
unfold prec_I; split. assumption.
intro h; simpl in h; elimination h.
apply H15; assumption.
apply not_exd_m2_max; assumption.
simpl; right; apply exd_m2; apply exd_m1; apply exd_left.
intro h; apply H12; rewrite h; apply exd_left.
apply expf_I. apply inv_hmap_m2.
unfold prec_I; split.
assumption. apply not_exd_m2_x.
apply exd_m2; apply exd_m1; apply exd_left.
intro h; apply H11; rewrite h; apply exd_left.
apply expf_m2_l_cA_m_one_l.
Qed.

Lemma expf_m4_l_cA_m_one_l : expf m4 l (cA m one l).
Proof.
unfold expf; split. apply inv_hmap_m4. unfold m4.
assert (t1: inv_hmap m3). apply inv_hmap_m3.
rewrite (expof_Merge1_CNS m3 max x l (cA m one l) t1).
elim expof_dec; intro h.
assert False; [idtac|tauto].
apply not_eqc_m3_x_max.
apply expf_eqc. apply inv_hmap_m3.
replace x with (cA m3 zero x). assumption.
apply cA_m3_zero_x.
left. apply expf_m3_l_cA_m_one_l.
unfold m3; simpl; left; trivial.
unfold m3; simpl; right; left; trivial.
apply not_expv_m3_max_x.
apply exd_m3_2. apply exd_m2. apply exd_m1. apply exd_left.
Qed.

Lemma eqc_m4_l_cA_m_one_l : eqc m4 l (cA m one l).
Proof.
apply expf_eqc. apply inv_hmap_m4.
apply expf_m4_l_cA_m_one_l.
Qed.

Lemma not_eqc_m4_max_cA_m_one_l : ~ eqc m4 max (cA m one l).
Proof.
assert (t1: ~ eqc m4 l max). intro h.
apply not_eqc_m4_x_l. apply eqc_trans with max.
apply expf_eqc. apply inv_hmap_m4.
apply expf_m4_x_max. apply eqc_symm; assumption.
intro h; apply t1; clear t1.
apply eqc_trans with (cA m one l).
apply eqc_m4_l_cA_m_one_l.
apply eqc_symm; assumption.
Qed.

Lemma not_expf_m4_max_cA_m_one_l : ~ expf m4 max (cA m one l).
Proof.
intro h; apply not_eqc_m4_max_cA_m_one_l.
apply expf_eqc. apply inv_hmap_m4. apply h.
Qed.

(* ===== *)

Lemma cA_1_m4_one_l : cA_1 m4 one l = cA m one l.
Proof.
rewrite <- eq_cA_cA_1.
rewrite cA_m4_one_da. rewrite cA_m3_one_da.
rewrite cA_m2_one_da. rewrite cA_m1_one_da.
trivial. apply exd_m1; apply exd_left.
apply exd_m2; apply exd_m1; apply exd_left.
apply exd_m3_2; apply exd_m2; apply exd_m1; apply exd_left.
intro h; apply H11; rewrite <- h; apply exd_left.
intro h; apply H12; rewrite <- h; apply exd_left.
apply exd_m4; apply exd_m3_2; apply exd_m2; apply exd_m1; apply exd_left.
intro h; apply H11; rewrite <- h; apply exd_left.
intro h; apply H12; rewrite <- h; apply exd_left.
apply inv_hmap_m4. apply inv_gmap_m4.
Qed.

(* ===== *)

Lemma expf_m5_l_max : expf m5 l max.
Proof.
unfold m5. unfold expf; split.
apply inv_hmap_m5.
assert (t1: inv_hmap m4).
 apply inv_hmap_m4.
assert (t2: exd m4 l).
 apply exd_Merge; simpl; do 2 right.
 apply exd_m2; apply exd_m1; apply exd_left.
assert (t3: exd m4 max).
 apply exd_Merge; simpl; left; trivial.
assert (t4: ~ expe m4 l max).
 apply not_expe_m4_l_max.
apply (expof_Merge0_CNS m4 l max l max t1 t2 t3 t4 t2).
elim expof_dec; intro h0; rewrite cA_1_m4_one_l in *.
assert False; [idtac|tauto].
apply not_expf_m4_max_cA_m_one_l.
unfold expf; split. apply inv_hmap_m4. assumption.
do 2 right; split. apply (expf_refl m4 max t1 t3).
apply expf_symm; apply expf_m4_l_cA_m_one_l.
Qed.

Lemma expf_m5_x_max : expf m5 x max.
Proof.
unfold m5. unfold expf; split.
apply inv_hmap_m5.
assert (t1: inv_hmap m4).
 apply inv_hmap_m4.
assert (t2: exd m4 l).
 apply exd_Merge; simpl; do 2 right.
 apply exd_m2; apply exd_m1; apply exd_left.
assert (t3: exd m4 max).
 apply exd_Merge; simpl; left; trivial.
assert (t4: ~ expe m4 l max).
 apply not_expe_m4_l_max.
apply (expof_Merge0_CNS m4 l max x max t1 t2 t3 t4).
apply exd_m4; simpl; right; left; trivial.
elim expof_dec; intro h0; rewrite cA_1_m4_one_l in *.
assert False; [idtac|tauto].
apply not_expf_m4_max_cA_m_one_l.
unfold expf; split. apply inv_hmap_m4. assumption.
left; apply expf_m4_x_max.
Qed.

Lemma expf_m5_l_r : expf m5 l r.
Proof.
unfold m5. unfold expf; split.
apply inv_hmap_m5.
assert (t1: inv_hmap m4).
 apply inv_hmap_m4.
assert (t2: exd m4 l).
 apply exd_Merge; simpl; do 2 right.
 apply exd_m2; apply exd_m1; apply exd_left.
assert (t3: exd m4 max).
 apply exd_Merge; simpl; left; trivial.
assert (t4: ~ expe m4 l max).
 apply not_expe_m4_l_max.
apply (expof_Merge0_CNS m4 l max l r t1 t2 t3 t4).
apply exd_m4; apply exd_m3_2; apply exd_m2.
apply exd_m1; apply exd_left.
elim expof_dec; intro h0; rewrite cA_1_m4_one_l in *.
assert False; [idtac|tauto].
apply not_expf_m4_max_cA_m_one_l.
unfold expf; split. apply inv_hmap_m4. assumption.
left; apply expf_m4_l_r.
Qed.

Lemma expf_m5_l0_r0 : expf m5 l0 r0.
Proof.
unfold m5. unfold expf; split.
apply inv_hmap_m5.
assert (t1: inv_hmap m4).
 apply inv_hmap_m4.
assert (t2: exd m4 l).
 apply exd_Merge; simpl; do 2 right.
 apply exd_m2; apply exd_m1; apply exd_left.
assert (t3: exd m4 max).
 apply exd_Merge; simpl; left; trivial.
assert (t4: ~ expe m4 l max).
 apply not_expe_m4_l_max.
apply (expof_Merge0_CNS m4 l max l0 r0 t1 t2 t3 t4).
apply exd_m4; apply exd_m3_2; apply exd_m2; apply exd_m1.
apply exd_cA. assumption. apply exd_left.
elim expof_dec; intro h0; rewrite cA_1_m4_one_l in *.
assert False; [idtac|tauto].
apply not_expf_m4_max_cA_m_one_l.
unfold expf; split. apply inv_hmap_m4. assumption.
left; apply expf_m4_l0_r0.
Qed.

Lemma not_eqc_m5_r_r0 : l0 <> r -> ~ eqc m5 r r0.
Proof.
intros h0 h; apply eqc_Merge in h.
elimination h.
apply not_eqc_m4_r_r0; assumption.
elimination h; destruct h as [h1 h2].
apply not_eqc_m4_x_l0. apply eqc_trans with max.
apply expf_eqc. apply inv_hmap_m4. apply expf_m4_x_max.
apply eqc_trans with r0. assumption. apply expf_eqc.
apply inv_hmap_m4. apply expf_symm; apply expf_m4_l0_r0.
apply not_eqc_m4_r_r0; try assumption.
apply eqc_trans with l; try assumption. apply expf_eqc.
apply inv_hmap_m4. apply expf_symm; apply expf_m4_l_r.
apply inv_hmap_m4. apply exd_m4; apply exd_m3_2.
apply exd_m2; apply exd_m1; apply exd_left.
apply exd_m4; unfold m3; simpl; left; trivial.
Qed.

(* ===== *)

Lemma expf_m5_max_r : expf m5 max r.
Proof.
apply expf_trans with l.
apply expf_symm; apply expf_m5_l_max.
apply expf_m5_l_r.
Qed.

Lemma eqc_m5_x_r : eqc m5 x r.
Proof.
apply eqc_trans with max.
apply expf_eqc. apply inv_hmap_m5.
apply expf_m5_x_max.
apply eqc_trans with l.
apply expf_eqc. apply inv_hmap_m5.
apply expf_symm; apply expf_m5_l_max.
apply expf_eqc. apply inv_hmap_m5.
apply expf_m5_l_r.
Qed.

Lemma not_expe_m5_x_r : ~ expe m5 x r.
Proof.
unfold m5.
intro h.
apply -> expe_Merge0_CNS in h.
elimination h.
apply toto in h.
apply H11; rewrite h.
apply exd_right.
rewrite cA_m4_zero_da.
apply cA_m3_zero_x.
apply -> exd_m4.
unfold m3; simpl; tauto.
elimination h.
destruct h as [h1 h2].
apply toto in h2.
apply H12; rewrite h2.
apply exd_right.
rewrite cA_m4_zero_da.
apply cA_m3_zero_max.
apply -> exd_m4.
unfold m3; simpl; tauto.
destruct h as [h1 h2].
apply toto in h2.
apply H15; rewrite h2; trivial.
rewrite cA_m4_zero_da.
apply cA_m3_zero_max.
apply -> exd_m4.
unfold m3; simpl; tauto.
apply not_expe_m4_l_max.
apply -> exd_m4.
unfold m3; simpl; tauto.
apply -> exd_m4.
unfold m3; simpl; tauto.
apply -> exd_m4.
apply exd_m3_2.
apply -> exd_m2.
apply -> exd_m1.
apply exd_left.
apply inv_hmap_m4.
Qed.

(* ================================ *)
(* ========== ########## ========== *)
(* ================================ *)

Lemma inv_hmap_m6 : inv_hmap m6.
Proof.
unfold m6; apply inv_hmap_Merge0.
apply inv_hmap_m5.
apply -> exd_m5.
apply -> exd_m4.
unfold m3; simpl; tauto.
apply -> exd_m5.
apply -> exd_m4.
apply exd_m3_2.
apply -> exd_m2.
apply -> exd_m1.
apply exd_right.
apply not_expe_m5_x_r.
Qed.

Lemma exd_m6 : forall (da:dart),
  exd m5 da <-> exd m6 da.
Proof.
intro da; split; unfold m6; intro h.
apply -> exd_Merge; assumption.
apply <- exd_Merge in h; assumption.
Qed.

Lemma cA_m6_zero_r : cA m6 zero r = x.
Proof.
unfold m6; rewrite cA_Merge.
elim eq_dim_dec; try tauto.
intro h; clear h.
elim eq_dart_dec; intro h1.
rewrite h1; trivial.
elim eq_dart_dec; intro h2.
rewrite cA_m5_zero_da.
rewrite cA_m4_zero_da.
apply cA_m3_zero_x.
apply -> exd_m4.
unfold m3; simpl; tauto.
apply -> exd_m5.
apply -> exd_m4.
unfold m3; simpl; tauto.
intro h; apply H11.
rewrite h; apply exd_left.
assumption.
assert False; [idtac|tauto].
apply h2.
rewrite <- eq_cA_cA_1.
rewrite cA_m5_zero_da.
rewrite cA_m4_zero_da.
apply cA_m3_zero_r.
apply -> exd_m4.
apply exd_m3_2.
apply -> exd_m2.
apply -> exd_m1.
apply exd_right.
apply -> exd_m5.
apply -> exd_m4.
apply exd_m3_2.
apply -> exd_m2.
apply -> exd_m1.
apply exd_right.
apply sym_not_eq; apply neq_left_right; tauto.
intro h; apply H12.
rewrite <- h; apply exd_right.
apply inv_hmap_m5.
apply inv_gmap_m5.
apply inv_hmap_m5.
Qed.

Lemma cA_m6_zero_x : cA m6 zero x = r.
Proof.
unfold m6; rewrite cA_Merge.
elim eq_dim_dec; try tauto.
intro h; clear h; eqdartdec; trivial.
apply inv_hmap_m5.
Qed.

Lemma cA_m6_zero_da : forall (da:dart),
  exd m6 da -> da <> r -> da <> x ->
  cA m6 zero da = cA m5 zero da.
Proof.
intros da h1 h2 h3.
unfold m6; rewrite cA_Merge.
elim eq_dim_dec; try tauto.
intro h; clear h.
elim eq_dart_dec; intro h4.
apply sym_eq in h4; contradiction.
elim eq_dart_dec; intro h5.
assert False; [idtac|tauto].
rewrite <- eq_cA_cA_1 in h5.
rewrite cA_m5_zero_da in h5.
rewrite cA_m4_zero_da in h5.
rewrite cA_m3_zero_r in h5.
apply sym_eq in h5; contradiction.
apply -> exd_m4.
apply exd_m3_2.
apply -> exd_m2.
apply -> exd_m1.
apply exd_right.
apply -> exd_m5.
apply -> exd_m4.
apply exd_m3_2.
apply -> exd_m2.
apply -> exd_m1.
apply exd_right.
apply sym_not_eq; apply neq_left_right; tauto.
intro h; apply H12.
rewrite <- h; apply exd_right.
apply inv_hmap_m5.
apply inv_gmap_m5.
clear H1 H2 H3 H4 H5 H6 H7 H8.
clear H9 H10 H11 H12 H13 H14 H15.
clear H0 h1 h2 h3 h4 h5.
trivial.
apply inv_hmap_m5.
Qed.

Lemma cA_m6_one_da : forall (da:dart),
  exd m6 da -> cA m6 one da = cA m5 one da.
Proof.
intros da h.
unfold m6; rewrite cA_Merge.
elim eq_dim_dec; try tauto.
intro h0; discriminate.
apply inv_hmap_m5.
Qed.

Lemma inv_gmap_m6 : inv_gmap m6.
Proof.
unfold inv_gmap; intros k da Hda; induction k.
(* k = zero *)
elim (eq_dart_dec da r); intro h1.
subst da; rewrite cA_m6_zero_r.
rewrite cA_m6_zero_x; tauto.
elim (eq_dart_dec da x); intro h2.
subst da; rewrite cA_m6_zero_x.
rewrite cA_m6_zero_r; tauto.
rewrite cA_m6_zero_da; try assumption.
rewrite cA_m6_zero_da; try assumption.
apply inv_gmap_m5; apply <- exd_m6; try assumption.
apply -> exd_cA; [exact Hda | apply inv_hmap_m6].
rewrite cA_m6_zero_da; try assumption.
elim (eq_dart_dec da l); intro h3.
subst da; rewrite cA_m5_zero_l.
intro h; apply H12.
rewrite h; apply exd_right.
elim (eq_dart_dec da max); intro h4.
subst da; rewrite cA_m5_zero_max.
apply neq_left_right; tauto.
rewrite cA_m5_zero_da; try assumption.
rewrite cA_m4_zero_da; try assumption.
intro h; apply sym_eq in h.
apply subst_cA_cA_1 in h.
rewrite <- eq_cA_cA_1 in h.
rewrite cA_m3_zero_r in h; contradiction.
apply inv_hmap_m3. apply inv_gmap_m3. apply inv_hmap_m3.
apply exd_m6 in Hda; apply exd_m5 in Hda; apply exd_m4 in Hda; assumption.
apply exd_m6 in Hda; apply exd_m5 in Hda; assumption.
apply exd_m6 in Hda; assumption.
rewrite cA_m6_zero_da; try assumption.
elim (eq_dart_dec da l); intro h3.
subst da; rewrite cA_m5_zero_l.
apply sym_not_eq; assumption.
elim (eq_dart_dec da max); intro h4.
subst da; rewrite cA_m5_zero_max.
intro h; apply H11.
rewrite <- h; apply exd_left.
rewrite cA_m5_zero_da; try assumption.
rewrite cA_m4_zero_da; try assumption.
intro h; apply sym_eq in h.
apply subst_cA_cA_1 in h.
rewrite <- eq_cA_cA_1 in h.
rewrite cA_m3_zero_x in h; contradiction.
apply inv_hmap_m3. apply inv_gmap_m3. apply inv_hmap_m3.
apply <- exd_m4. apply <- exd_m5. apply <- exd_m6. assumption.
apply <- exd_m5. apply <- exd_m6. assumption.
apply <- exd_m6. assumption.
(* k = one *)
rewrite cA_m6_one_da; try assumption.
rewrite cA_m6_one_da; try assumption.
apply inv_gmap_m5; apply <- exd_m6; try assumption.
apply -> exd_cA; [exact Hda | apply inv_hmap_m6].
Qed.

Lemma planar_m6 : planar m6.
Proof.
unfold m6.
apply <- planarity_crit_Merge0.
split; try right.
apply planar_m5.
rewrite <- eq_cA_cA_1.
rewrite cA_m5_one_da.
rewrite cA_m4_one_x.
apply expf_m5_max_r.
apply -> exd_m5.
apply -> exd_m4.
unfold m3; simpl; tauto.
apply inv_hmap_m5.
apply inv_gmap_m5.
apply not_expe_m5_x_r.
apply -> exd_m5.
apply -> exd_m4.
apply exd_m3_2.
apply -> exd_m2.
apply -> exd_m1.
apply exd_right.
apply -> exd_m5.
apply -> exd_m4.
unfold m3; simpl; tauto.
apply inv_hmap_m5.
Qed.

Open Scope Z_scope.

Lemma nd_m6 : nd m6 = nd m5.
Proof.
unfold m6; apply nd_Merge.
Qed.

Lemma ne_m6 : ne m6 = ne m5 - 1.
Proof.
unfold m6; apply ne_Merge0.
apply inv_hmap_m5.
apply -> exd_m5. apply -> exd_m4.
apply exd_m3_2. apply -> exd_m2.
apply -> exd_m1. apply exd_right.
apply not_expe_m5_x_r.
Qed.

Lemma nv_m6 : nv m6 = nv m5.
Proof.
unfold m6; apply nv_Merge0.
apply inv_hmap_m5.
apply -> exd_m5. apply -> exd_m4.
apply exd_m3_2. apply -> exd_m2.
apply -> exd_m1. apply exd_right.
apply not_expe_m5_x_r.
Qed.

Lemma nf_m6 : nf m6 = nf m5 + 1.
Proof.
unfold m6; rewrite nf_Merge0.
elim expf_dec; intro h; try trivial.
assert False; [idtac|tauto].
rewrite <- eq_cA_cA_1 in h.
rewrite cA_m5_one_da in h.
rewrite cA_m4_one_x in h.
apply h; apply expf_m5_max_r.
apply -> exd_m5.
apply -> exd_m4.
unfold m3; simpl; tauto.
apply inv_hmap_m5.
apply inv_gmap_m5.
apply inv_hmap_m5.
apply -> exd_m5.
apply -> exd_m4.
unfold m3; simpl; tauto.
apply -> exd_m5.
apply -> exd_m4.
apply exd_m3_2.
apply -> exd_m2.
apply -> exd_m1.
apply exd_right.
Qed.

Lemma nc_m6 : nc m6 = nc m5.
Proof.
unfold m6; rewrite nc_Merge.
elim eqc_dec; intro h.
ring_simplify; trivial.
assert False; [idtac|tauto].
apply h. clear h.
apply eqc_m5_x_r.
apply inv_hmap_m5.
apply -> exd_m5.
apply -> exd_m4.
unfold m3; simpl; tauto.
apply -> exd_m5.
apply -> exd_m4.
apply exd_m3_2.
apply -> exd_m2.
apply -> exd_m1.
apply exd_right.
Qed.

Open Scope nat_scope.

Lemma is_well_emb_m6 : is_well_emb m6.
Proof.
unfold is_well_emb; intros da db h1 h2 h3.
apply exd_m6 in h1; apply exd_m6 in h2.
unfold m6; split; intro h4.
(* expv da db *)
do 2 rewrite fpoint_Merge.
apply -> expv_Merge0 in h4.
generalize (is_well_emb_m5 da db h1 h2 h3).
intros [h5 h6]; apply h5; assumption.
apply -> exd_m5.
apply -> exd_m4.
apply exd_m3_2.
apply -> exd_m2.
apply -> exd_m1.
apply exd_right.
apply -> exd_m5.
apply -> exd_m4.
unfold m3; simpl; tauto.
apply inv_hmap_m5.
(* expe da db *)
do 2 rewrite fpoint_Merge.
apply -> expe_Merge0_CNS in h4; try assumption.
elimination h4.
generalize (is_well_emb_m5 da db h1 h2 h3).
intros [h5 h6]; apply h6; assumption.
elimination h4.
destruct h4 as [h4 h5].
apply toto in h4.
apply toto in h5.
subst da db.
unfold m5.
do 2 rewrite fpoint_Merge.
unfold m4.
do 2 rewrite fpoint_Merge.
unfold m3.
simpl fpoint. eqdartdec.
elim eq_dart_dec; intro t0.
assert False; [idtac|tauto].
apply H12; rewrite t0.
apply exd_right.
apply not_eq_sym.
unfold m2.
elim eq_dart_dec; intro h0.
unfold m1.
rewrite fpoint_Split.
apply H16.
apply exd_right.
rewrite fpoint_Split.
unfold m1.
rewrite fpoint_Split.
apply H16.
apply exd_right.
rewrite cA_m5_zero_da.
rewrite cA_m4_zero_da.
apply cA_m3_zero_r.
apply -> exd_m4.
apply exd_m3_2.
apply -> exd_m2.
apply -> exd_m1.
apply exd_right.
apply -> exd_m5.
apply -> exd_m4.
apply exd_m3_2.
apply -> exd_m2.
apply -> exd_m1.
apply exd_right.
apply sym_not_eq.
apply neq_left_right; try assumption.
left; assumption.
intro h.
apply H12.
rewrite <- h.
apply exd_right.
rewrite cA_m5_zero_da.
rewrite cA_m4_zero_da.
apply cA_m3_zero_x.
apply -> exd_m4.
unfold m3; simpl; tauto.
apply -> exd_m5.
apply -> exd_m4.
unfold m3; simpl; tauto.
intro h.
apply H11.
rewrite h.
apply exd_left.
assumption.
destruct h4 as [h4 h5].
apply toto in h4.
apply toto in h5.
subst da db.
unfold m5.
do 2 rewrite fpoint_Merge.
unfold m4.
do 2 rewrite fpoint_Merge.
unfold m3.
simpl fpoint. eqdartdec.
elim eq_dart_dec; intro t0.
assert False; [idtac|tauto].
apply H12; rewrite t0.
apply exd_right.
unfold m2.
elim eq_dart_dec; intro h0.
unfold m1.
rewrite fpoint_Split.
apply H16.
apply exd_right.
rewrite fpoint_Split.
unfold m1.
rewrite fpoint_Split.
apply H16.
apply exd_right.
rewrite cA_m5_zero_da.
rewrite cA_m4_zero_da.
apply cA_m3_zero_r.
apply -> exd_m4.
apply exd_m3_2.
apply -> exd_m2.
apply -> exd_m1.
apply exd_right.
apply -> exd_m5.
apply -> exd_m4.
apply exd_m3_2.
apply -> exd_m2.
apply -> exd_m1.
apply exd_right.
apply sym_not_eq.
apply neq_left_right; try assumption.
left; assumption.
intro h.
apply H12.
rewrite <- h.
apply exd_right.
rewrite cA_m5_zero_da.
rewrite cA_m4_zero_da.
apply cA_m3_zero_x.
apply -> exd_m4.
unfold m3; simpl; tauto.
apply -> exd_m5.
apply -> exd_m4.
unfold m3; simpl; tauto.
intro h.
apply H11.
rewrite h.
apply exd_left.
assumption.
apply not_expe_m5_x_r.
apply -> exd_m5.
apply -> exd_m4.
apply exd_m3_2.
apply -> exd_m2.
apply -> exd_m1.
apply exd_right.
apply -> exd_m5.
apply -> exd_m4.
unfold m3; simpl; tauto.
apply inv_hmap_m5.
Qed.

Lemma is_neq_point_m6 : is_neq_point m6.
Proof.
unfold is_neq_point; intros da db h1 h2.
apply exd_m6 in h1; apply exd_m6 in h2.
unfold m6. do 2 rewrite fpoint_Merge.
intro h3. rewrite expv_Merge0 in h3.
apply is_neq_point_m5; try assumption.
apply inv_hmap_m5.
apply exd_m5. apply exd_m4. unfold m3; simpl; tauto.
apply exd_m5. apply exd_m4. apply exd_m3_2. apply exd_m2.
apply exd_m1. apply exd_right.
Qed.

Lemma is_noalign_m6 : is_noalign m6.
Proof.
unfold is_noalign, m6; intros da db dc h1 h2 h3 h4 h5 h6.
apply exd_m6 in h1; apply exd_m6 in h2; apply exd_m6 in h3.
do 3 rewrite fpoint_Merge in *; apply is_noalign_m5; assumption.
Qed.

(* ================================ *)

Lemma cA_1_m5_one_x : cA_1 m5 one x = max.
Proof.
rewrite <- eq_cA_cA_1.
rewrite cA_m5_one_da. apply cA_m4_one_x.
apply exd_m5; apply exd_m4; simpl; right; left; trivial.
apply inv_hmap_m5. apply inv_gmap_m5.
Qed.

Lemma cA_m5_zero_x : cA m5 zero x = x.
Proof.
rewrite cA_m5_zero_da. rewrite cA_m4_zero_da. apply cA_m3_zero_x.
apply exd_m4; simpl; right; left; tauto.
apply exd_m5; apply exd_m4; simpl; right; left; tauto.
intro h; apply H11; rewrite h; apply exd_left. exact H15.
Qed.

Lemma cF_m5_r : cF m5 r = cA m one r.
Proof.
unfold cF. rewrite <- (eq_cA_cA_1 m5 zero r).
rewrite cA_m5_zero_da. rewrite cA_m4_zero_da.
rewrite cA_m3_zero_r. rewrite <- eq_cA_cA_1.
rewrite cA_m5_one_da. rewrite cA_m4_one_da.
rewrite cA_m3_one_da. rewrite cA_m2_one_da.
rewrite cA_m1_one_da. trivial. apply exd_m1; apply exd_right.
apply exd_m2; apply exd_m1; apply exd_right.
apply exd_m3_2; apply exd_m2; apply exd_m1; apply exd_right.
intro heq; apply H11; rewrite <- heq; apply exd_right.
intro heq; apply H12; rewrite <- heq; apply exd_right.
apply exd_m4; apply exd_m3_2; apply exd_m2; apply exd_m1; apply exd_right.
intro heq; apply H11; rewrite <- heq; apply exd_right.
intro heq; apply H12; rewrite <- heq; apply exd_right.
apply exd_m5; apply exd_m4; apply exd_m3_2.
apply exd_m2; apply exd_m1; apply exd_right.
apply inv_hmap_m5. apply inv_gmap_m5.
apply exd_m4; apply exd_m3_2; apply exd_m2; apply exd_m1; apply exd_right.
apply exd_m5; apply exd_m4; apply exd_m3_2.
apply exd_m2; apply exd_m1; apply exd_right.
apply not_eq_sym; apply neq_left_right; try assumption. left; exact H10.
intro heq; apply H12; rewrite <- heq; apply exd_right.
apply inv_hmap_m5. apply inv_gmap_m5.
Qed.

(* ===== *)

Lemma expf_m2_r_cA_m_one_r : expf m2 r (cA m one r).
Proof.
unfold expf; split. apply inv_hmap_m2.
unfold m2; elim eq_dart_dec; intro h.
apply expf_m1_r_r1.
assert (t1: inv_hmap m1). apply inv_hmap_m1.
assert (t2: inv_gmap m1). apply inv_gmap_m1.
apply (expof_Split0_CNS m1 r0 r r (cA m one r) t1).
apply cracke_m1_r0_r; assumption.
apply exd_m1; apply exd_right.
assert (t3: cA m1 zero r0 = r).
 rewrite cA_m1_zero_da. apply cA_m_zero_r0.
 apply exd_m1; apply exd_cA_1. exact H1. apply exd_right.
 intro h0; apply h; apply eq_l0_r_r0_l; assumption.
 apply not_eq_sym; apply neq_l0_r0. rewrite t3.
elim expof_dec; intro h0. left; split.
apply MF.between_expo_refl_2. exact t1.
apply exd_cA_1. exact t1. apply exd_m1; apply exd_right.
apply MF.expo_expo1; try assumption.
replace MF.expo with expof; try tauto.
apply expf_symm. apply expf_expof. split. exact t1. exact h0.
rewrite <- eq_cA_cA_1. rewrite cA_m1_one_da.
apply MF.between_expo_refl_1. exact t1.
apply exd_m1; apply exd_cA. exact H1. apply exd_right.
apply MF.expo_expo1; try assumption.
replace MF.expo with expof; try tauto.
apply expf_symm. apply expf_expof. split. exact t1.
apply expf_m1_r_r1. apply exd_m1; apply exd_right.
apply inv_hmap_m1. apply inv_gmap_m1.
assert False; [idtac|tauto]. apply h0.
replace (cA_1 m1 one r) with (cA m one r).
apply expf_m1_r_r1.
rewrite <- eq_cA_cA_1; try assumption.
rewrite cA_m1_one_da. trivial.
apply exd_m1; apply exd_right.
Qed.

Lemma expf_m3_r_cA_m_one_r : expf m3 r (cA m one r).
Proof.
unfold m3; apply expf_I.
simpl; split. apply inv_hmap_m2.
unfold prec_I; split.
assumption. apply not_exd_m2_x.
unfold prec_I; split. assumption.
intro h; simpl in h; elimination h.
apply H15; assumption.
apply not_exd_m2_max; assumption.
simpl; right; apply exd_m2; apply exd_m1; apply exd_right.
intro h; apply H12; rewrite h; apply exd_right.
apply expf_I. apply inv_hmap_m2.
unfold prec_I; split.
assumption. apply not_exd_m2_x.
apply exd_m2; apply exd_m1; apply exd_right.
intro h; apply H11; rewrite h; apply exd_right.
apply expf_m2_r_cA_m_one_r.
Qed.

Lemma expf_m4_r_cA_m_one_r : expf m4 r (cA m one r).
Proof.
unfold expf; split. apply inv_hmap_m4. unfold m4.
assert (t1: inv_hmap m3). apply inv_hmap_m3.
rewrite (expof_Merge1_CNS m3 max x r (cA m one r) t1).
elim expof_dec; intro h.
assert False; [idtac|tauto].
apply not_eqc_m3_x_max.
apply expf_eqc. apply inv_hmap_m3.
replace x with (cA m3 zero x). assumption.
apply cA_m3_zero_x.
left. apply expf_m3_r_cA_m_one_r.
unfold m3; simpl; left; trivial.
unfold m3; simpl; right; left; trivial.
apply not_expv_m3_max_x.
apply exd_m3_2; apply exd_m2; apply exd_m1; apply exd_right.
Qed.

Lemma expf_m5_r_cA_m_one_r : expf m5 r (cA m one r).
Proof.
unfold m5. unfold expf; split. apply inv_hmap_m5.
assert (t1: inv_hmap m4). apply inv_hmap_m4.
apply (expof_Merge0_CNS m4 l max r (cA m one r) t1).
apply exd_m4; apply exd_m3_2; apply exd_m2; apply exd_m1; apply exd_left.
apply exd_m4; simpl; left; trivial. apply not_expe_m4_l_max.
apply exd_m4; apply exd_m3_2; apply exd_m2; apply exd_m1; apply exd_right.
rewrite cA_1_m4_one_l. elim expof_dec; intro h0.
assert False; [idtac|tauto].
apply not_expf_m4_max_cA_m_one_l.
unfold expf; split. exact t1. exact h0.
left; apply expf_m4_r_cA_m_one_r.
Qed.

(* ===== *)

Lemma not_expf_m6_x_r : ~ expf m6 x r.
Proof.
intro h; unfold expf, m6 in h; destruct h as [h1 h2].
assert (t1: inv_hmap m5). apply inv_hmap_m5.
rewrite (expof_Merge0_CNS m5 x r x r t1) in h2.
generalize h2; clear h1 h2.
rewrite cA_1_m5_one_x; rewrite cA_m5_zero_x.
elim expof_dec; intro h0. intro h.
elimination h. destruct h as [h1 h2].
assert (t2: cF m5 x = max).
 unfold cF. rewrite <- (eq_cA_cA_1 m5 zero x).
 rewrite cA_m5_zero_x. apply cA_1_m5_one_x.
 apply inv_hmap_m5. apply inv_gmap_m5.
unfold betweenf, MF.between in h1; rewrite <- t2 in h1.
assert (t3: exd m5 (cF m5 x)).
 apply -> exd_cF; try assumption.
 apply exd_m5; apply exd_m4; simpl; right; left; trivial.
generalize (h1 t1 t3); clear h1; intro h1.
unfold MF.f, McF.f in h1.
elim h1; clear h1; intros i h1.
elim h1; clear h1; intros j [h1 [h3 h4]].
rewrite MF.upb_eq_degree in h4; try assumption.
replace MF.degree with degreef in h4; try tauto.
assert (t4: degreef m5 (cF m5 x) = (S i)).
 elim (eq_dart_dec (degreef m5 (cF m5 x)) (S i)).
 intro t0; exact t0. intro t0. assert False; [idtac|tauto].
 assert (t5: Iter (cF m5) (S i) x = x).
  rewrite MF.Iter_f_Si; try assumption.
  apply exd_m5; apply exd_m4; simpl; right; left; tauto.
 assert (t6: 0 < S i < degreef m5 (cF m5 x)). omega.
 assert (t7: exd m5 x).
  apply exd_m5; apply exd_m4; simpl; right; left; tauto.
 assert (t8: MF.degree m5 x = degreef m5 (cF m5 x)).
  apply MF.expo_degree; try assumption.
  unfold MF.expo; split. assumption.
  exists 1; simpl; tauto. rewrite <- t8 in t6.
 apply (MF.degree_diff m5 x t1 t7 (S i)); assumption.
rewrite t4 in h4. assert (t5: i = j). omega.
assert (t0: x = r). rewrite <- h1, <- h3, t5; tauto.
apply H11; rewrite t0; apply exd_right.
elimination h; destruct h as [h1 h2].
unfold betweenf, MF.between in h2.
assert (t2: exd m5 (cF m5 r)).
 apply -> exd_cF; try assumption.
 apply exd_m5; apply exd_m4; apply exd_m3_2.
 apply exd_m2; apply exd_m1; apply exd_right.
generalize (h2 t1 t2); clear h2; intro h2.
unfold MF.f, McF.f in h2.
elim h2; clear h2; intros i h2.
elim h2; clear h2; intros j [h2 [h3 h4]].
rewrite MF.upb_eq_degree in h4; try assumption.
replace MF.degree with degreef in h4; try tauto.
assert (t3: degreef m5 (cF m5 r) = (S i)).
 elim (eq_dart_dec (degreef m5 (cF m5 r)) (S i)).
 intro t0; exact t0. intro t0. assert False; [idtac|tauto].
 assert (t4: Iter (cF m5) (S i) r = r).
  rewrite MF.Iter_f_Si; try assumption.
  apply exd_m5; apply exd_m4; apply exd_m3_2.
  apply exd_m2; apply exd_m1; apply exd_right.
 assert (t5: 0 < S i < degreef m5 (cF m5 r)). omega.
 assert (t6: exd m5 r).
  apply exd_m5; apply exd_m4; apply exd_m3_2.
  apply exd_m2; apply exd_m1; apply exd_right.
 assert (t7: MF.degree m5 r = degreef m5 (cF m5 r)).
  apply MF.expo_degree; try assumption.
  unfold MF.expo; split. assumption.
  exists 1; simpl; tauto. rewrite <- t7 in t5.
 apply (MF.degree_diff m5 r t1 t6 (S i)); assumption.
rewrite t3 in h4. assert (t4: i = j). omega.
assert (t0: x = r). rewrite <- h2, <- h3, t4; tauto.
apply H11; rewrite t0; apply exd_right.
apply h1; apply expf_symm. unfold expf; tauto.
intro h; apply h0. apply expf_trans with l.
apply expf_symm; apply expf_m5_l_r. apply expf_m5_l_max.
apply exd_m5; apply exd_m4; simpl; right; left; tauto.
apply exd_m5; apply exd_m4; apply exd_m3_2.
apply exd_m2; apply exd_m1; apply exd_right.
apply not_expe_m5_x_r.
apply exd_m5; apply exd_m4; simpl; right; left; tauto.
Qed.

Lemma not_expf_m6_max_x : ~ expf m6 max x.
Proof.
intro h; unfold expf, m6 in h; destruct h as [h1 h2].
assert (t1: inv_hmap m5). apply inv_hmap_m5.
rewrite (expof_Merge0_CNS m5 x r max x t1) in h2.
generalize h2; clear h1 h2.
rewrite cA_1_m5_one_x; rewrite cA_m5_zero_x.
elim expof_dec; intro h0. intro h.
elimination h. destruct h as [h1 h2].
assert (t2: cF m5 x = max).
 unfold cF. rewrite <- (eq_cA_cA_1 m5 zero x).
 rewrite cA_m5_zero_x. apply cA_1_m5_one_x.
 apply inv_hmap_m5. apply inv_gmap_m5.
unfold betweenf, MF.between in h2; rewrite <- t2 in h2.
assert (t3: exd m5 (cF m5 x)).
 apply -> exd_cF; try assumption.
 apply exd_m5; apply exd_m4; simpl; right; left; trivial.
generalize (h2 t1 t3); clear h2; intro h2.
unfold MF.f, McF.f in h2.
elim h2; clear h2; intros i h2.
elim h2; clear h2; intros j [h2 [h3 h4]].
rewrite MF.upb_eq_degree in h4; try assumption.
replace MF.degree with degreef in h4; try tauto.
assert (t4: degreef m5 (cF m5 x) = (S i)).
 elim (eq_dart_dec (degreef m5 (cF m5 x)) (S i)).
 intro t0; exact t0. intro t0. assert False; [idtac|tauto].
 assert (t5: Iter (cF m5) (S i) x = x).
  rewrite MF.Iter_f_Si; try assumption.
  apply exd_m5; apply exd_m4; simpl; right; left; tauto.
 assert (t6: 0 < S i < degreef m5 (cF m5 x)). omega.
 assert (t7: exd m5 x).
  apply exd_m5; apply exd_m4; simpl; right; left; tauto.
 assert (t8: MF.degree m5 x = degreef m5 (cF m5 x)).
  apply MF.expo_degree; try assumption.
  unfold MF.expo; split. assumption.
  exists 1; simpl; tauto. rewrite <- t8 in t6.
 apply (MF.degree_diff m5 x t1 t7 (S i)); assumption.
rewrite t4 in h4. assert (t5: i = j). omega.
assert (t0: x = r). rewrite <- h2, <- h3, t5; tauto.
apply H11; rewrite t0; apply exd_right.
elimination h; destruct h as [h1 h2].
assert (t2: cF m5 x = max).
 unfold cF. rewrite <- (eq_cA_cA_1 m5 zero x).
 rewrite cA_m5_zero_x. apply cA_1_m5_one_x.
 apply inv_hmap_m5. apply inv_gmap_m5.
unfold betweenf, MF.between in h1; rewrite <- t2 in h1.
assert (t3: exd m5 (cF m5 r)).
 apply -> exd_cF; try assumption.
 apply exd_m5; apply exd_m4; apply exd_m3_2.
 apply exd_m2; apply exd_m1; apply exd_right.
generalize (h1 t1 t3); clear h1; intro h1.
unfold MF.f, McF.f in h1.
elim h1; clear h1; intros i h1.
elim h1; clear h1; intros j [h1 [h3 h4]].
rewrite MF.upb_eq_degree in h4; try assumption.
replace MF.degree with degreef in h4; try tauto.
assert (t4: i = S j). rewrite <- h3 in h1.
 apply MF.degree_unicity with m5 (cF m5 r); try assumption.
 replace MF.degree with degreef; try tauto. omega.
 elim (eq_nat_dec (S j) (MF.degree m5 (cF m5 r))).
 intro h; assert False; [idtac|tauto].
 generalize (MF.degree_per m5 (cF m5 r) t1 t3).
 intro t0. rewrite <- h in t0. simpl in t0.
 unfold MF.f, McF.f in t0. rewrite h3 in t0.
 rewrite t2 in t0. apply H12; rewrite t0.
 rewrite cF_m5_r. apply exd_cA. exact H1. apply exd_right.
 replace MF.degree with degreef; try tauto. intro h; omega.
 omega. contradiction.
intro h; apply h0. apply expf_trans with l.
apply expf_symm; apply expf_m5_l_r. apply expf_m5_l_max.
apply exd_m5; apply exd_m4; simpl; right; left; tauto.
apply exd_m5; apply exd_m4; apply exd_m3_2.
apply exd_m2; apply exd_m1; apply exd_right.
apply not_expe_m5_x_r.
apply exd_m5; apply exd_m4; simpl; left; tauto.
Qed.

Lemma expf_m6_l_x : expf m6 l x.
Proof.
unfold m6. unfold expf; split.
apply inv_hmap_m6.
assert (t1: inv_hmap m5). apply inv_hmap_m5.
apply (expof_Merge0_CNS m5 x r l x t1).
apply exd_m5; apply exd_m4; simpl; right; left; tauto.
apply exd_m5; apply exd_m4; apply exd_m3_2.
apply exd_m2; apply exd_m1; apply exd_right.
apply not_expe_m5_x_r.
apply exd_m5; apply exd_m4; apply exd_m3_2.
apply exd_m2; apply exd_m1; apply exd_left.
rewrite cA_1_m5_one_x; rewrite cA_m5_zero_x.
elim expof_dec; intro h0. right; left; split.
unfold betweenf, MF.between. intros h1 h2.
assert (t2: MF.expo1 m5 (cF m5 r) l).
 apply MF.expo_expo1. exact t1.
 rewrite cF_m5_r. apply expf_trans with r.
 apply expf_symm; apply expf_m5_r_cA_m_one_r.
 apply expf_symm; apply expf_m5_l_r.
unfold MF.expo1 in t2; destruct t2 as [t2 t3].
elim t3; clear t3. intros i [t3 t4].
assert (t5: cF m5 l = x).
 unfold cF. rewrite <- (eq_cA_cA_1 m5 zero l).
 rewrite cA_m5_zero_l. rewrite <- eq_cA_cA_1.
 rewrite cA_m5_one_da. apply cA_m4_one_max.
 apply exd_m5; apply exd_m4; simpl; left; tauto.
 apply inv_hmap_m5. apply inv_gmap_m5.
 apply inv_hmap_m5. apply inv_gmap_m5.
exists i. exists (S i). repeat split.
exact t4. simpl. rewrite t4. tauto. omega.
rewrite MF.upb_eq_degree in *; try assumption.
elim (eq_dart_dec (S i) (MF.degree m5 (cF m5 r))).
intro h. assert False; [idtac|tauto].
generalize (MF.degree_per m5 (cF m5 r) h1 h2); intro t6.
assert (t7: cF m5 l <> cF m5 r).
 rewrite t5. rewrite cF_m5_r.
 intro heq; apply H11; rewrite heq.
 apply exd_cA. exact H1. apply exd_right.
assert (t8: Iter (MF.f m5) (S i) (cF m5 r) = cF m5 l).
 simpl. rewrite t4. tauto.
apply t7. rewrite <- t6. rewrite <- t8.
rewrite h. tauto. intro h; omega.
apply MF.between_expo_refl_2. exact t1.
apply -> exd_cF. apply exd_m5; apply exd_m4; apply exd_m3_2.
apply exd_m2; apply exd_m1; apply exd_right. exact t1.
apply MF.expo_expo1; try assumption.
replace MF.expo with expof; try tauto.
apply expf_trans with r. rewrite cF_m5_r.
apply expf_symm; apply expf_m5_r_cA_m_one_r.
apply expf_trans with max.
apply expf_expof. split. exact t1. exact h0.
apply expf_symm; apply expf_m5_x_max.
assert False; [idtac|tauto]. apply h0.
apply expf_trans with l. apply expf_symm.
apply expf_m5_l_r. apply expf_m5_l_max.
Qed.

Lemma expf_m6_max_r : expf m6 max r.
Proof.
unfold m6. unfold expf; split.
apply inv_hmap_m6.
assert (t1: inv_hmap m5). apply inv_hmap_m5.
apply (expof_Merge0_CNS m5 x r max r t1).
apply exd_m5; apply exd_m4; simpl; right; left; tauto.
apply exd_m5; apply exd_m4; apply exd_m3_2.
apply exd_m2; apply exd_m1; apply exd_right.
apply not_expe_m5_x_r.
apply exd_m5; apply exd_m4; simpl; left; tauto.
rewrite cA_1_m5_one_x; rewrite cA_m5_zero_x.
elim expof_dec; intro h0. left; split.
apply MF.between_expo_refl_1. exact t1.
apply exd_m5; apply exd_m4; simpl; left; tauto.
apply MF.expo_expo1; try assumption.
apply expf_symm. unfold expf. split. exact t1. exact h0.
apply MF.between_expo_refl_2. exact t1.
apply exd_m5; apply exd_m4; simpl; left; tauto.
apply MF.expo_expo1; try assumption.
apply expf_symm. unfold expf. split. exact t1. exact h0.
assert False; [idtac|tauto]. apply h0.
apply expf_trans with l. apply expf_symm.
apply expf_m5_l_r. apply expf_m5_l_max.
Qed.

Lemma expf_m6_l0_r0 : l0 <> r -> expf m6 l0 r0.
Proof.
intro h; unfold m6. unfold expf; split.
apply inv_hmap_m6.
assert (t1: inv_hmap m5). apply inv_hmap_m5.
apply (expof_Merge0_CNS m5 x r l0 r0 t1).
apply exd_m5; apply exd_m4; simpl; right; left; tauto.
apply exd_m5; apply exd_m4; apply exd_m3_2.
apply exd_m2; apply exd_m1; apply exd_right.
apply not_expe_m5_x_r.
apply exd_m5; apply exd_m4; apply exd_m3_2.
apply exd_m2; apply exd_m1; apply exd_cA.
exact H1. apply exd_left.
rewrite cA_1_m5_one_x; rewrite cA_m5_zero_x.
elim expof_dec; intro h0. do 2 right; split.
intro t0. apply expf_eqc in t0; try assumption.
apply not_eqc_m5_r_r0. exact h.
apply eqc_trans with l0. exact t0.
apply expf_eqc. exact t1. apply expf_m5_l0_r0.
apply expf_m5_l0_r0.
assert False; [idtac|tauto]. apply h0.
apply expf_trans with l. apply expf_symm.
apply expf_m5_l_r. apply expf_m5_l_max.
Qed.

Lemma not_eqc_m6_r_r0 : l0 <> r -> ~ eqc m6 r r0.
Proof.
assert (t0: inv_hmap m5). apply inv_hmap_m5.
intros h0 h; apply eqc_Merge in h; try assumption.
elimination h. apply not_eqc_m5_r_r0; assumption.
elimination h; destruct h as [h1 h2].
apply not_eqc_m5_r_r0; assumption.
apply not_eqc_m5_r_r0. exact h0. apply eqc_trans with x.
apply eqc_trans with l. apply eqc_symm.
apply expf_eqc. exact t0. apply expf_m5_l_r. apply eqc_trans with max.
apply expf_eqc. exact t0. apply expf_m5_l_max. apply eqc_symm.
apply expf_eqc. exact t0. apply expf_m5_x_max. exact h2.
apply exd_m5; apply exd_m4; simpl; right; left; trivial.
apply exd_m5; apply exd_m4; apply exd_m3_2.
apply exd_m2; apply exd_m1; apply exd_right.
Qed.

Lemma eqc_m6_max_x : eqc m6 max x.
Proof.
unfold m6; apply eqc_Merge. apply inv_hmap_m5.
apply exd_m5; apply exd_m4.
unfold m3; simpl; right; left; tauto.
apply exd_m5; apply exd_m4; apply exd_m3_2.
apply exd_m2; apply exd_m1; apply exd_right.
left. apply eqc_symm. apply expf_eqc.
apply inv_hmap_m5. apply expf_m5_x_max.
Qed.

(* ===== *)

Lemma not_eqc_m6_x_l0 : l0 <> r -> ~ eqc m6 x l0.
Proof.
intros h0 h.
apply not_eqc_m6_r_r0; try assumption.
apply eqc_trans with x. apply eqc_trans with max.
apply eqc_symm. apply expf_eqc.
apply inv_hmap_m6. apply expf_m6_max_r.
apply eqc_m6_max_x.
apply eqc_trans with l0. exact h.
apply expf_eqc. apply inv_hmap_m6.
apply expf_m6_l0_r0; assumption.
Qed.

(*
Lemma fpoint_m6 : forall (da:dart),
  da <> x -> da <> max -> fpoint m6 da = fpoint m da.
Proof.
intros da h1 h2.
unfold m6; rewrite fpoint_Merge.
unfold m5; rewrite fpoint_Merge.
unfold m4; rewrite fpoint_Merge.
unfold m3; simpl; eqdartdec.
unfold m2; elim eq_dart_dec; intro h.
unfold m1; rewrite fpoint_Split; trivial.
rewrite fpoint_Split.
unfold m1; rewrite fpoint_Split; trivial.
Qed.
*)

(* ================================ *)
(* ========== ########## ========== *)
(* ================================ *)

Lemma cF_m6_x : cF m6 x = r1.
Proof.
unfold cF.
rewrite <- eq_cA_cA_1. rewrite <- eq_cA_cA_1.
rewrite cA_m6_zero_x. rewrite cA_m6_one_da.
rewrite cA_m5_one_da. rewrite cA_m4_one_da.
rewrite cA_m3_one_da. rewrite cA_m2_one_da.
rewrite cA_m1_one_da. unfold r1; tauto.
apply exd_m1; apply exd_right.
apply exd_m2; apply exd_m1; apply exd_right.
apply exd_m3_2; apply exd_m2; apply exd_m1; apply exd_right.
intro h; apply H11; rewrite <- h; apply exd_right.
intro h; apply H12; rewrite <- h; apply exd_right.
apply exd_m4; apply exd_m3_2; apply exd_m2; apply exd_m1; apply exd_right.
intro h; apply H11; rewrite <- h; apply exd_right.
intro h; apply H12; rewrite <- h; apply exd_right.
apply exd_m5; apply exd_m4; apply exd_m3_2.
apply exd_m2; apply exd_m1; apply exd_right.
apply exd_Merge; apply exd_m5; apply exd_m4; apply exd_m3_2.
apply exd_m2; apply exd_m1; apply exd_right.
apply inv_hmap_m6. apply inv_gmap_m6.
apply inv_hmap_m6. apply inv_gmap_m6.
Qed.

Lemma cF_1_m6_r1 : cF_1 m6 r1 = x.
Proof.
unfold cF_1.
rewrite cA_m6_one_da; try assumption.
rewrite cA_m5_one_da. rewrite cA_m4_one_da.
rewrite cA_m3_one_da. rewrite cA_m2_one_da.
rewrite cA_m1_one_da. unfold r1. rewrite H2.
apply cA_m6_zero_r. apply exd_right.
apply exd_m1; apply exd_cA. exact H1. apply exd_right.
apply exd_m2; apply exd_m1; apply exd_cA. exact H1. apply exd_right.
apply exd_m3_2; apply exd_m2; apply exd_m1.
apply exd_cA. exact H1. apply exd_right.
intro h; apply H11; rewrite <- h; apply exd_cA. exact H1. apply exd_right.
intro h; apply H12; rewrite <- h; apply exd_cA. exact H1. apply exd_right.
apply exd_m4; apply exd_m3_2; apply exd_m2; apply exd_m1.
apply exd_cA. exact H1. apply exd_right.
intro h; apply H11; rewrite <- h; apply exd_cA. exact H1. apply exd_right.
intro h; apply H12; rewrite <- h; apply exd_cA. exact H1. apply exd_right.
apply exd_m5; apply exd_m4; apply exd_m3_2; apply exd_m2; apply exd_m1.
apply exd_cA. exact H1. apply exd_right.
apply exd_Merge; apply exd_m5; apply exd_m4; apply exd_m3_2; apply exd_m2.
apply exd_m1. apply exd_cA. exact H1. apply exd_right.
Qed.

Lemma cF_1_m6_x : cF_1 m6 x = l.
Proof.
unfold cF_1.
rewrite cA_m6_one_da; try assumption.
rewrite cA_m5_one_da. rewrite cA_m4_one_x.
rewrite cA_m6_zero_da. apply cA_m5_zero_max.
apply exd_Merge; apply exd_m5; apply exd_m4.
unfold m3; simpl; left; tauto.
intro h; apply H12; rewrite h; apply exd_right.
apply not_eq_sym; exact H15.
apply exd_m5; apply exd_m4.
unfold m3; simpl; right; left; tauto.
apply exd_Merge; apply exd_m5; apply exd_m4.
unfold m3; simpl; right; left; tauto.
Qed.

(* ===== *)

Lemma Iter_cF_m6_i_r1_Iter_cF_m_i_r1 : forall (i:nat)(n:nat),
  i <= n -> n < degreef m6 r1 -> Iter (cF m6) n r1 = l ->
  Iter (cF m6) i r1 = Iter (cF m) i r1.
Proof. 
intros i n hle hd hn; induction i.
simpl; tauto. simpl; rewrite <- IHi; clear IHi.
set (cF6 := Iter (cF m6) i r1).
(**)
assert (a1: inv_hmap m6).
 apply inv_hmap_m6.
assert (a2: exd m6 r1).
 apply exd_Merge; apply exd_m5; apply exd_m4.
 apply exd_m3_2; apply exd_m2; apply exd_m1.
 apply exd_cA. exact H1. apply exd_right.
assert (t1: r <> cF6).
 intro h; apply not_expf_m6_x_r.
 rewrite h; apply expf_trans with r1.
 unfold expf, MF.expo; split. exact a1. split.
 apply exd_Merge; apply exd_m5; apply exd_m4.
 unfold m3; simpl; right; left; tauto.
 exists 1; simpl; apply cF_m6_x.
 unfold expf, MF.expo; split. exact a1. split.
 exact a2. exists i; unfold MF.f, McF.f, cF6; tauto.
assert (t2: max <> cF6).
 intro h; apply not_expf_m6_max_x.
 rewrite h; apply expf_trans with r1; apply expf_symm.
 unfold expf, MF.expo; split. exact a1. split. exact a2.
 exists i; unfold MF.f, McF.f, cF6; tauto.
 unfold expf, MF.expo; split. exact a1. split.
 apply exd_Merge; apply exd_m5; apply exd_m4.
 unfold m3; simpl; right; left; tauto.
 exists 1; simpl; apply cF_m6_x.
assert (t3: l <> cF6).
 intro h; unfold cF6 in h; rewrite <- hn in h.
 cut (n = i). intro h0; rewrite h0 in hle; omega.
 apply (MF.degree_unicity m6 r1 n i); try assumption.
 replace MF.degree with degreef; try tauto. omega.
assert (t4: x <> cF6).
 intro h; unfold cF6 in h.
 assert (t0: Iter (cF m6) (S n) r1 = x).
  simpl; rewrite hn; rewrite <- cF_1_m6_x.
  rewrite cF_cF_1; try assumption. tauto.
  apply exd_Merge; apply exd_m5; apply exd_m4.
  unfold m3; simpl; right; left; tauto.
 rewrite h in t0. cut ((S n) = i).
 intro h0; rewrite <- h0 in hle; omega.
 apply (MF.degree_unicity m6 r1 (S n) i); try assumption.
 elim (eq_nat_dec (S n) (degreef m6 r1)); intro h0.
 assert False; [idtac|tauto].
 generalize (MF.degree_per m6 r1 a1 a2). intro h1.
 apply H11. unfold MF.f, McF.f in h1.
 replace MF.degree with degreef in h1; try tauto.
 rewrite h; rewrite <- t0; rewrite h0; rewrite h1.
 apply exd_cA. exact H1. apply exd_right.
 replace MF.degree with degreef; try tauto. omega.
 replace MF.degree with degreef; try tauto. omega.
assert (t0: exd m6 cF6).
 apply exd_Iter_cF; assumption. apply exd_Merge in t0.
 apply exd_m5 in t0. apply exd_m4 in t0.
 unfold m3 in t0; simpl in t0.
 elimination t0. contradiction.
 elimination t0. contradiction.
 apply exd_m2 in t0. apply exd_m1 in t0.
(**)
unfold m6; rewrite cF_Merge0.
(**)
elim eq_dart_dec; intro h1.
contradiction.
(**)
elim eq_dart_dec; intro h2.
assert False; [idtac|tauto].
rewrite cA_m5_zero_da in h2.
rewrite cA_m4_zero_da in h2.
rewrite cA_m3_zero_x in h2.
contradiction.
apply exd_m4; unfold m3; simpl; tauto.
apply exd_m5; apply exd_m4; unfold m3; simpl; tauto.
intro h; apply H11; rewrite h; apply exd_left. exact H15.
(**)
unfold m5; rewrite cF_Merge0.
(**)
elim eq_dart_dec; intro h3.
contradiction.
(**)
elim eq_dart_dec; intro h4.
assert False; [idtac|tauto].
rewrite cA_m4_zero_da in h4.
rewrite cA_m3_zero_l in h4.
contradiction.
apply exd_m4; apply exd_m3_2; apply exd_m2.
apply exd_m1; apply exd_left.
(**)
unfold m4; rewrite cF_Merge1.
(**)
elim eq_dart_dec; intro h5.
assert False; [idtac|tauto].
rewrite cA_m3_zero_x in h5.
contradiction.
(**)
elim eq_dart_dec; intro h6.
assert False; [idtac|tauto].
unfold cF_1 in h6.
rewrite cA_m3_one_max in h6.
rewrite cA_m3_zero_max in h6.
contradiction.
(**)
unfold m3. rewrite cF_I. rewrite cF_I.
(**)
unfold m2. elim eq_dart_dec; intro heq.
(**)
unfold m1; rewrite cF_Split0.
(**)
elim eq_dart_dec; intro h7.
assert False; [idtac|tauto].
unfold l0 in heq; rewrite heq in h7.
contradiction.
(**)
elim eq_dart_dec; intro h8.
assert False; [idtac|tauto].
rewrite cA_m_zero_l0 in h8.
contradiction.
(**)
tauto. exact H1. apply cracke_m_l_l0. exact t0.
(**)
rewrite cF_Split0.
(**)
elim eq_dart_dec; intro h7.
assert False; [idtac|tauto].
rewrite cA_m1_zero_da in h7.
rewrite cA_m_zero_r0 in h7.
contradiction.
apply exd_m1; apply exd_cA_1. exact H1. apply exd_right.
intro h; apply heq; apply eq_l0_r_r0_l; exact h.
apply not_eq_sym; apply neq_l0_r0.
(**)
elim eq_dart_dec; intro h8.
assert False; [idtac|tauto].
rewrite cA_m1_zero_da in h8.
rewrite eq_cA_cA_1 in h8; try assumption.
apply not_eqc_m6_r_r0; try assumption.
fold r0 in h8; rewrite h8.
apply eqc_trans with l.
apply eqc_trans with x.
apply eqc_trans with max.
apply eqc_symm; apply expf_eqc.
exact a1. apply expf_m6_max_r.
apply eqc_m6_max_x.
apply eqc_symm; apply expf_eqc.
exact a1. apply expf_m6_l_x.
apply eqc_trans with r1.
apply eqc_symm; apply expf_eqc.
exact a1. unfold MF.expo; split.
exact a2. exists n; apply hn.
apply expf_eqc. exact a1. unfold MF.expo; split.
exact a2. exists i; unfold cF6; tauto.
apply exd_m1; apply exd_right.
apply not_eq_sym; apply neq_left_right; tauto.
apply not_eq_sym; exact heq.
(**)
unfold m1; rewrite cF_Split0.
(**)
elim eq_dart_dec; intro h9.
assert False; [idtac|tauto].
apply not_eqc_m6_r_r0; try assumption.
apply eqc_trans with l0.
fold l0 in h9; rewrite h9.
apply eqc_trans with l.
apply eqc_trans with x.
apply eqc_trans with max.
apply eqc_symm; apply expf_eqc.
exact a1. apply expf_m6_max_r.
apply eqc_m6_max_x.
apply eqc_symm; apply expf_eqc.
exact a1. apply expf_m6_l_x.
apply eqc_trans with r1.
apply eqc_symm; apply expf_eqc.
exact a1. unfold MF.expo; split.
exact a2. exists n; apply hn.
apply expf_eqc. exact a1. unfold MF.expo; split.
exact a2. exists i; unfold cF6; tauto.
apply expf_eqc. exact a1.
apply expf_m6_l0_r0; assumption.
(**)
elim eq_dart_dec; intro h10.
assert False; [idtac|tauto].
rewrite cA_m_zero_l0 in h10.
contradiction.
(**)
tauto. exact H1. apply cracke_m_l_l0. exact t0.
apply inv_hmap_m1.
apply cracke_m1_r0_r; assumption.
apply exd_m1; exact t0.
apply inv_hmap_m2.
unfold prec_I; split.
exact H13. apply not_exd_m2_x.
apply exd_m2; apply exd_m1; exact t0.
intro h; apply H11; rewrite h; exact t0.
simpl; split. apply inv_hmap_m2.
unfold prec_I; split.
exact H13. apply not_exd_m2_x.
unfold prec_I; split.
exact H14. intro h; simpl in h; elimination h.
apply H15; exact h. apply not_exd_m2_max; exact h.
simpl; right. apply exd_m2; apply exd_m1; exact t0.
intro h; apply H12; rewrite h; exact t0.
apply inv_hmap_m3.
unfold m3; simpl; tauto.
unfold m3; simpl; tauto.
apply exd_m3_2; apply exd_m2; apply exd_m1; exact t0.
apply inv_hmap_m4.
apply exd_m4; apply exd_m3_2; apply exd_m2.
apply exd_m1; apply exd_left.
apply exd_m4; unfold m3; simpl; tauto.
apply inv_hmap_m5.
apply exd_m5; apply exd_m4; unfold m3; simpl; tauto.
apply exd_m5; apply exd_m4; apply exd_m3_2.
apply exd_m2; apply exd_m1; apply exd_right.
omega.
Qed.

(*
Lemma exists_i_Iter_cF_m_i_r1_l_bis :
  exists i:nat, Iter (cF m) i r1 = l /\
  (forall (j:nat), j < i -> Iter (cF m) j r1 <> l).
Proof.
generalize (exists_i_Iter_cF_m_i_r1_l).
intro h; elim h; clear h; intros i [h1 h2].
exists i; split; try assumption.
intros j hj. intro h. rewrite <- h2 in h.
apply MF.degree_unicity in h. omega.
assumption. apply exd_r1.
replace MF.degree with degreef; try tauto. omega.
replace MF.degree with degreef; try tauto.
Qed.

Lemma exists_i_Iter_cF_m1_i_r1_l :
  exists i:nat, Iter (cF m1) i r1 = l /\
  (forall (j:nat), j < i -> Iter (cF m1) j r1 <> l).
Proof.
assert (h: expf m1 r1 l). apply expf_symm.
 apply expf_trans with r. apply expf_trans with r0.
 apply expf_m1_l_r0. apply expf_symm.
 apply expf_m1_r_r0. apply expf_m1_r_r1.
unfold expf in h; destruct h as [h1 h2].
apply MF.expo_expo1 in h2; try assumption.
unfold MF.expo1 in h2; destruct h2 as [h2 h3].
elim h3; clear h3; intros i [h3 h4].
rewrite MF.upb_eq_degree in *; try assumption.
replace MF.degree with degreef in *; try tauto.
unfold MF.f, McF.f in *.
exists i; split; try assumption.
intros j hj. intro h. rewrite <- h4 in h.
apply MF.degree_unicity in h; try assumption. omega.
replace MF.degree with degreef; try tauto. omega.
Qed.

Lemma testing : forall (i:nat),
  Iter (cF m1) i r1 = l /\
  (forall (j:nat), j < i -> Iter (cF m1) j r1 <> l) ->
  Iter (cF m) i r1 = l /\
  (forall (j:nat), j < i -> Iter (cF m) j r1 <> l).
Proof.
intros i [h1 h2]. split.
rewrite <- h1.
induction i.
simpl. tauto.
simpl.
set (im := Iter (cF m) i r1).
set (im1 := (Iter (cF m1) i r1)).
fold im in IHi; fold im1 in IHi.
simpl in h1. fold im1 in h1.
clear IHi.
rewrite h1.

generalize h1; clear h1.
unfold m1. Check cF_Split0. ; rewrite cF_Split0.
(**)
elim eq_dart_dec; intro h9.
assert False; [idtac|tauto].
apply not_eqc_m6_r_r0; try assumption.
apply eqc_trans with l0.
fold l0 in h9; rewrite h9.
apply eqc_trans with l.
apply eqc_trans with x.
apply eqc_trans with max.
apply eqc_symm; apply expf_eqc.
exact a1. apply expf_m6_max_r.
apply eqc_m6_max_x.
apply eqc_symm; apply expf_eqc.
exact a1. apply expf_m6_l_x.
apply eqc_trans with r1.
apply eqc_symm; apply expf_eqc.
exact a1. unfold MF.expo; split.
exact a2. exists n; apply hn.
apply expf_eqc. exact a1. unfold MF.expo; split.
exact a2. exists i; unfold cF6; tauto.
apply expf_eqc. exact a1.
apply expf_m6_l0_r0; assumption.
(**)
elim eq_dart_dec; intro h10.
assert False; [idtac|tauto].
rewrite cA_m_zero_l0 in h10.
contradiction.
(**)
tauto. exact H1. apply cracke_m_l_l0. exact t0.
apply inv_hmap_m1.
apply cracke_m1_r0_r; assumption.
apply exd_m1; exact t0.
apply inv_hmap_m2.
unfold prec_I; split.
exact H13. apply not_exd_m2_x.
apply exd_m2; apply exd_m1; exact t0.
intro h; apply H11; rewrite h; exact t0.
simpl; split. apply inv_hmap_m2.
unfold prec_I; split.
exact H13. apply not_exd_m2_x.
unfold prec_I; split.
exact H14. intro h; simpl in h; elimination h.
apply H15; exact h. apply not_exd_m2_max; exact h.
simpl; right. apply exd_m2; apply exd_m1; exact t0.
intro h; apply H12; rewrite h; exact t0.
apply inv_hmap_m3.
*)

Lemma expf_m6_x_da_betweenf_m6_r1_da_l : forall (da:dart),
  expf m6 x da -> da = x \/ betweenf m6 r1 da l.
Proof.
intros da hda.
assert (t0: expf m6 r1 da).
 apply expf_trans with x.
 apply expf_symm; unfold expf, MF.expo.
 destruct hda as [h1 [h2 h3]].
 split. exact h1. split. exact h2.
 exists 1; simpl. unfold MF.f, McF.f.
 apply cF_m6_x. exact hda.
apply expf_expof in t0; destruct t0 as [h1 h2].
apply MF.expo_expo1 in h2; try assumption.
unfold MF.expo1 in h2; destruct h2 as [h2 h3].
elim h3; clear h3. intros i [h3 h4].
elim (eq_nat_dec i (degreef m6 r1 - 1)); intro h5.
left; rewrite <- h4; rewrite h5. clear h5 hda h4 da.
rewrite <- MF.Iter_f_f_1; try assumption.
rewrite MF.degree_per; try assumption.
simpl; unfold MF.f_1, McF.f_1. apply cF_1_m6_r1.
rewrite MF.upb_eq_degree in *; try assumption.
replace MF.degree with degreef in *; try tauto.
omega. right; unfold betweenf, MF.between.
intros h6 h7. exists i. exists (degreef m6 r1 - 2).
rewrite MF.upb_eq_degree in *; try assumption.
replace MF.degree with degreef in *; try tauto.
unfold MF.f, McF.f in *. repeat split; try lia.
exact h4. rewrite <- MF.Iter_f_f_1; try assumption.
rewrite MF.degree_per; try assumption.
simpl; unfold MF.f_1, McF.f_1.
rewrite cF_1_m6_r1; apply cF_1_m6_x.
elim (eq_dart_dec (degreef m6 r1) 0); intro t1.
rewrite t1 in h3. assert False; [omega|tauto].
elim (eq_dart_dec (degreef m6 r1) 1); intro t2.
rewrite t2 in h3, h5. assert False; [omega|tauto].
omega.
Qed.

Lemma betweenf_m6_m_r1_da_l : forall (da:dart),
  betweenf m6 r1 da l -> betweenf m r1 da l.
Proof.
unfold betweenf, MF.between; intros da h h1 h2.
assert (t1: inv_hmap m6). apply inv_hmap_m6.
assert (t2: exd m6 r1).
 apply exd_Merge; apply exd_m5; apply exd_m4.
 apply exd_m3_2; apply exd_m2; apply exd_m1. exact h2.
generalize (h t1 t2); clear h; intro h.
elim h; clear h; intros i h.
elim h; clear h; intros j [hi [hj h0]].
rewrite MF.upb_eq_degree in *; try assumption.
replace MF.degree with degreef in *; try tauto.
unfold MF.f, McF.f in *.
generalize hi; generalize hj; intros e1 e2.
rewrite (Iter_cF_m6_i_r1_Iter_cF_m_i_r1 i j) in hi.
rewrite (Iter_cF_m6_i_r1_Iter_cF_m_i_r1 j j) in hj.
(*
assert (t3: MF.expo m r1 da).
unfold MF.expo; split; try assumption.
exists i; rewrite <- hi; tauto.
apply MF.expo_expo1 in t3; try assumption.
unfold MF.expo1 in t3.
destruct t3 as [t3 t4].
elim t4; clear t4; intros z1 [t4 t5].
assert (t6: MF.expo m r1 l).
unfold MF.expo; split; try assumption.
exists j; rewrite <- hj; tauto.
apply MF.expo_expo1 in t6; try assumption.
unfold MF.expo1 in t6.
destruct t6 as [t6 t7].
elim t7; clear t7; intros z2 [t7 t8].
rewrite MF.upb_eq_degree in *; try assumption.
replace MF.degree with degreef in *; try tauto.
unfold MF.f, McF.f in *.
exists z1; exists z2; repeat split; try assumption; try omega.
admit. (* <===== ADMIT in comment *)
omega. omega. exact hj.
omega. omega. exact hj.
Qed.
*)
exists i. exists j. repeat split; try assumption; try omega.
assert (t0: (degreef m6 r1 <= degreef m r1) \/ (degreef m6 r1 = (degreef m r1 + 1))).

admit. (* <===== ADMIT *)
elimination t0. omega. rewrite t0 in h0. clear t0.
elim (eq_nat_dec j (degreef m r1)); intro heq.
assert False; [idtac|tauto]. rewrite heq in hj.
rewrite MF.degree_per in hj; try assumption.
assert (t3: cF_1 m l = r0).
 unfold cF_1; rewrite <- hj; unfold r1.
 rewrite (eq_cA_cA_1 m one r); try assumption.
 rewrite cA_cA_1; try assumption.
 rewrite (eq_cA_cA_1 m zero r); try assumption.
 unfold r0; tauto. apply exd_right.
generalize (invisibleleft m d p 0 H1 H9 H10).
intro h3; fold l in h3; rewrite t3 in h3.
unfold invisible_succ in h3; rewrite cA_m_zero_r0 in h3.
assert (t4: exd m l). apply exd_left.
assert (t5: r <> nil). apply exd_left_dart_exd_right_dart; assumption.
generalize (visibleright m l p 0 H1 t4 t5).
intro h4; fold r in h4; unfold visible_pred in h4; fold r0 in h4.
apply ccw_axiom_2 in h4. contradiction. omega.
omega. omega. exact hj.
omega. omega. exact hj.
Admitted. (*Qed.*)

Lemma expf_m6_x_da_expf_m_d_da : forall (da:dart),
  expf m6 x da -> da = x \/ expf m d da.
Proof.
intros da hda.
apply expf_m6_x_da_betweenf_m6_r1_da_l in hda.
elimination hda. left; exact hda.
apply betweenf_m6_m_r1_da_l in hda.
right. apply expf_trans with l.
apply expfleft; assumption.
apply MF.between_expo in hda.
destruct hda as [h1 h2].
apply expf_trans with r1. apply expf_symm.
unfold expf; split; assumption.
unfold expf; split; assumption.
exact H1. apply exd_cA. exact H1. apply exd_right.
Qed.

Lemma betweenf_m_r1_l_invisible_succ_m_p :
  forall (da:dart), betweenf m r1 da (cF_1 m l) ->
  invisible_succ m da p.
Proof.
intros da h0.
unfold betweenf, MF.between in h0.
assert (t0: exd m (cA m one r)).
 apply exd_cA; try assumption. apply exd_right.
generalize (h0 H1 t0); clear h0; intro h0.
elim h0; clear h0; intros i h0.
elim h0; clear h0; intros j h0.
destruct h0 as [h1 [h2 h3]].
rewrite <- h1.
apply not_left_dart_until_i_invisible_i with d; try assumption.
apply expf_trans with r0. apply expf_trans with l.
apply expfleft; assumption. apply expfright; try assumption.
apply exd_left. apply exd_left_dart_exd_right_dart; assumption.
unfold r0. rewrite <- eq_cA_cA_1; try assumption.
apply expf_cA_cA; try assumption. apply exd_right.
assert (t1: exd m l). apply exd_left.
assert (t2: r <> nil).
 apply exd_left_dart_exd_right_dart; assumption.
generalize (invisibleright m l p 0 H1 t1 t2). fold r.
unfold cF_1; unfold invisible_pred, invisible_succ.
rewrite cA_1_cA; try assumption. fold r1; tauto.
intros k hk h.
assert (t1: left_dart m l p).
unfold left_dart; split.
apply invisibleleft; assumption.
apply visibleleft; assumption.
assert (t3: l = (Iter (cF m) k (cA m one r))).
apply left_uniqueness with m d p; try assumption.
apply exd_left.
apply exd_Iter_cF; assumption.
apply expfleft; assumption.
apply expf_trans with l.
apply expfleft; assumption.
apply expf_trans with r0.
apply expfright; try assumption.
apply exd_left.
apply exd_left_dart_exd_right_dart; assumption.
apply expf_trans with (cA m one r).
unfold r0. rewrite <- eq_cA_cA_1; try assumption.
apply expf_cA_cA; try assumption. apply exd_right.
unfold expf, MF.expo; repeat split; try assumption.
exists k; unfold MF.f, McF.f; tauto.
intro z; induction z.
intro h0. apply not_expf_m_l_l0.
apply expf_trans with (Iter (cF m) k (cA m one r)).
apply expf_trans with r0.
apply expfright; try assumption.
apply exd_left.
apply exd_left_dart_exd_right_dart; assumption.
apply expf_trans with (cA m one r).
unfold r0. rewrite <- eq_cA_cA_1; try assumption.
apply expf_cA_cA; try assumption. apply exd_right.
unfold expf, MF.expo; repeat split; try assumption.
exists k; unfold MF.f, McF.f; tauto.
apply expf_symm; apply h0.
intro h0. apply not_expf_m_l_l0.
apply expf_trans with l1.
apply expf_trans with (Iter (cF m) k (cA m one r)).
apply expf_trans with r0.
apply expfright; try assumption.
apply exd_left.
apply exd_left_dart_exd_right_dart; assumption.
apply expf_trans with (cA m one r).
unfold r0. rewrite <- eq_cA_cA_1; try assumption.
apply expf_cA_cA; try assumption. apply exd_right.
unfold expf, MF.expo; repeat split; try assumption.
exists k; unfold MF.f, McF.f; tauto.
apply expf_symm; apply h0.
unfold l0, l1; apply expf_symm.
apply expf_cA_cA; try assumption.
apply exd_left.
clear h t1.
assert (t4: Iter (MF.f m) (S j) (cA m one r) = l).
simpl. fold r1; rewrite h2. unfold MF.f, McF.f.
rewrite cF_cF_1; try assumption. tauto. apply exd_left.
assert (t5: S j = k).
apply MF.degree_unicity with m (cA m one r); try assumption.
elim (eq_dart_dec (S j) (MF.degree m r1)); intro h0.
assert False; [idtac|tauto].
rewrite h0 in t4. unfold r1 in t4.
rewrite MF.degree_per in t4; try assumption.
fold r1 in t4.
generalize (visibleleft m d p 0 H1 H9 H10).
unfold visible_succ. fold l. intro c1.
assert (t1: exd m l). apply exd_left.
assert (t2: r <> nil).
 apply exd_left_dart_exd_right_dart; assumption.
generalize (invisibleright m l p 0 H1 t1 t2). fold r.
unfold invisible_pred.
unfold cF_1. fold r1. rewrite cA_1_cA; try assumption.
intro c2; rewrite t4 in c2.
apply ccw_axiom_2 in c2. apply c2; exact c1.
rewrite MF.upb_eq_degree in h3; try assumption.
unfold r1 in *; omega.
rewrite MF.upb_eq_degree in h3; try assumption.
unfold r1 in *; omega.
unfold MF.f, McF.f in *. rewrite t4; exact t3.
rewrite <- t5 in hk. omega.
Qed.

Lemma betweenf_m_r1_cF_1_m_l :
  forall (da:dart), da <> l -> betweenf m r1 da l ->
  betweenf m r1 da (cF_1 m l).
Proof.
intros da hl.
unfold betweenf, MF.between.
intros h0 h1 h2.
generalize (h0 h1 h2); clear h0; intro h0.
elim h0; clear h0; intros i h0.
elim h0; clear h0; intros j h0.
destruct h0 as [h3 [h4 h5]].
exists i; exists (j-1); repeat split; try lia.
exact h3. rewrite <- MF.Iter_f_f_1; try assumption.
rewrite h4; simpl Iter; unfold MF.f_1, McF.f_1; tauto.
elim (eq_dart_dec 0 j); intro hj; try omega.
assert False; [idtac|tauto].
rewrite <- hj in h4; simpl in h4.
apply neq_l_r1; rewrite h4; tauto.
elim (eq_dart_dec i j); intro hj; try omega.
assert False; [idtac|tauto].
apply hl; rewrite <- h3; rewrite <- h4; rewrite hj; tauto.
Qed.

(* ================================ *)

Lemma eqc_m6_x_da_eqc_m_d_da : forall (da:dart),
  eqc m6 x da -> da = x \/ da = max \/ eqc m d da.
Proof.
intros da hda.
unfold m6 in hda.
apply eqc_Merge in hda.
elimination hda.
unfold m5 in hda.
apply eqc_Merge in hda.
elimination hda.
unfold m4 in hda.
apply eqc_Merge in hda.
elimination hda.
unfold m3 in hda; simpl in hda.
elimination hda.
destruct hda as [t1 t2]; tauto.
elimination hda.
destruct hda as [t1 t2]; tauto.
assert False; [idtac|tauto].
apply eqc_exd_exd in hda.
destruct hda as [t1 t2].
apply not_exd_m2_x; assumption.
elimination hda.
destruct hda as [t1 t2].
assert False; [idtac|tauto].
apply not_eqc_m3_x_max; assumption.
destruct hda as [t1 t2].
unfold m3 in t2; simpl in t2.
elimination t2.
destruct t2 as [t2 t3]; tauto.
elimination t2.
destruct t2 as [t2 t3]; tauto.
assert False; [idtac|tauto].
apply eqc_exd_exd in t2.
destruct t2 as [t2 t3].
apply not_exd_m2_max; assumption.
apply inv_hmap_m3.
unfold m3; simpl; tauto.
unfold m3; simpl; tauto.
elimination hda.
destruct hda as [t1 t2].
assert False; [idtac|tauto].
apply not_eqc_m4_x_l; assumption.
destruct hda as [t1 t2].
unfold m4 in t2.
apply eqc_Merge in t2.
elimination t2.
unfold m3 in t2; simpl in t2.
elimination t2.
destruct t2 as [t2 t3]; tauto.
elimination t2.
destruct t2 as [t2 t3]; tauto.
generalize t2; clear t2; unfold m2.
elim eq_dart_dec; intros h0 h.
apply eqc_Split in h; try assumption.
do 2 right.
apply eqc_trans with l.
apply eqcleft; assumption.
exact h. apply exd_left.
apply exd_cA. exact H1. apply exd_left.
unfold crack. elim eq_dim_dec; try tauto.
intro hk; apply cracke_m_l_l0.
apply eqc_Split in h.
apply eqc_Split in h; try assumption.
do 2 right.
apply eqc_trans with l.
apply eqcleft; assumption.
exact h. apply exd_left.
apply exd_cA. exact H1. apply exd_left.
unfold crack. elim eq_dim_dec; try tauto.
intro hk; apply cracke_m_l_l0.
apply inv_hmap_m1.
apply exd_m1; apply exd_cA_1. exact H1. apply exd_right.
apply exd_m1; apply exd_right.
unfold crack. elim eq_dim_dec; try tauto.
intro hk; apply cracke_m1_r0_r; assumption.
elimination t2.
destruct t2 as [t2 t3].
assert False; [idtac|tauto].
apply not_eqc_m3_max_l.
apply eqc_symm; exact t2.
destruct t2 as [t2 t3].
assert False; [idtac|tauto].
apply not_eqc_m3_x_l.
apply eqc_symm; exact t2.
apply inv_hmap_m3.
unfold m3; simpl; tauto.
unfold m3; simpl; tauto.
apply inv_hmap_m4.
apply exd_m4; apply exd_m3_2; apply exd_m2.
apply exd_m1; apply exd_left.
apply exd_m4; unfold m3; simpl; tauto.
elimination hda.
destruct hda as [t1 t2].
unfold m5 in t2.
apply eqc_Merge in t2.
elimination t2.
unfold m4 in t2.
apply eqc_Merge in t2.
elimination t2.
unfold m3 in t2; simpl in t2.
elimination t2.
destruct t2 as [t2 t3]; tauto.
elimination t2.
destruct t2 as [t2 t3]; tauto.
generalize t2; clear t2; unfold m2.
elim eq_dart_dec; intros h0 h.
apply eqc_Split in h; try assumption.
do 2 right.
apply eqc_trans with l.
apply eqcleft; assumption.
apply eqc_trans with r.
apply eqcright; try assumption.
apply exd_left.
apply exd_left_dart_exd_right_dart; assumption.
exact h. apply exd_left.
apply exd_cA. exact H1. apply exd_left.
unfold crack. elim eq_dim_dec; try tauto.
intro hk; apply cracke_m_l_l0.
apply eqc_Split in h.
apply eqc_Split in h; try assumption.
do 2 right.
apply eqc_trans with l.
apply eqcleft; assumption.
apply eqc_trans with r.
apply eqcright; try assumption.
apply exd_left.
apply exd_left_dart_exd_right_dart; assumption.
exact h. apply exd_left.
apply exd_cA. exact H1. apply exd_left.
unfold crack. elim eq_dim_dec; try tauto.
intro hk; apply cracke_m_l_l0.
apply inv_hmap_m1.
apply exd_m1; apply exd_cA_1. exact H1. apply exd_right.
apply exd_m1; apply exd_right.
unfold crack. elim eq_dim_dec; try tauto.
intro hk; apply cracke_m1_r0_r; assumption.
elimination t2.
destruct t2 as [t2 t3].
assert False; [idtac|tauto].
apply not_eqc_m3_max_l.
apply eqc_trans with r.
apply eqc_symm; exact t2.
apply eqc_symm; apply expf_eqc.
apply inv_hmap_m3. apply expf_m3_l_r.
destruct t2 as [t2 t3].
assert False; [idtac|tauto].
apply not_eqc_m3_x_l.
apply eqc_trans with r.
apply eqc_symm; exact t2.
apply eqc_symm; apply expf_eqc.
apply inv_hmap_m3. apply expf_m3_l_r.
apply inv_hmap_m3.
unfold m3; simpl; tauto.
unfold m3; simpl; tauto.
elimination t2.
destruct t2 as [t2 t3].
unfold m4 in t3.
apply eqc_Merge in t3.
elimination t3.
unfold m3 in t3; simpl in t3.
elimination t3.
destruct t3 as [t3 t4]; tauto.
elimination t3.
destruct t3 as [t3 t4]; tauto.
assert False; [idtac|tauto].
apply eqc_exd_exd in t3.
destruct t3 as [t3 t4].
apply not_exd_m2_max; assumption.
elimination t3.
destruct t3 as [t3 t4].
unfold m3 in t4; simpl in t4.
elimination t4.
destruct t4 as [t4 t5]; tauto.
elimination t4.
destruct t4 as [t4 t5]; tauto.
assert False; [idtac|tauto].
apply eqc_exd_exd in t4.
destruct t4 as [t4 t5].
apply not_exd_m2_x; assumption.
destruct t3 as [t3 t4].
assert False; [idtac|tauto].
apply not_eqc_m3_x_max.
apply eqc_symm; exact t3.
apply inv_hmap_m3.
unfold m3; simpl; tauto.
unfold m3; simpl; tauto.
elimination t2.
assert False; [idtac|tauto].
apply not_eqc_m4_x_l.
apply eqc_trans with r.
apply eqc_trans with max.
apply expf_eqc. apply inv_hmap_m4.
apply expf_m4_x_max.
apply eqc_symm; exact t2.
apply eqc_symm; apply expf_eqc.
apply inv_hmap_m4. apply expf_m4_l_r.
apply inv_hmap_m4.
apply exd_m4; apply exd_m3_2; apply exd_m2.
apply exd_m1; apply exd_left.
apply exd_m4; unfold m3; simpl; tauto.
destruct hda as [t1 t2].
unfold m5 in t2.
apply eqc_Merge in t2.
elimination t2.
unfold m4 in t2.
apply eqc_Merge in t2.
elimination t2.
unfold m3 in t2; simpl in t2.
elimination t2.
destruct t2 as [t2 t3]; tauto.
elimination t2.
destruct t2 as [t2 t3]; tauto.
assert False; [idtac|tauto].
apply eqc_exd_exd in t2.
destruct t2 as [t2 t3].
apply not_exd_m2_x; assumption.
elimination t2.
destruct t2 as [t2 t3].
assert False; [idtac|tauto].
apply not_eqc_m3_x_max; assumption.
destruct t2 as [t2 t3].
unfold m3 in t3; simpl in t3.
elimination t3.
destruct t3 as [t3 t4]; tauto.
elimination t3.
destruct t3 as [t3 t4]; tauto.
assert False; [idtac|tauto].
apply eqc_exd_exd in t3.
destruct t3 as [t3 t4].
apply not_exd_m2_max; assumption.
apply inv_hmap_m3.
unfold m3; simpl; tauto.
unfold m3; simpl; tauto.
elimination t2.
destruct t2 as [t2 t3].
assert False; [idtac|tauto].
apply not_eqc_m4_x_l; assumption.
destruct t2 as [t2 t3].
unfold m4 in t3.
apply eqc_Merge in t3.
elimination t3.
unfold m3 in t3; simpl in t3.
elimination t3.
destruct t3 as [t3 t4]; tauto.
elimination t3.
destruct t3 as [t3 t4]; tauto.
generalize t3; clear t3; unfold m2.
elim eq_dart_dec; intros h0 h.
apply eqc_Split in h; try assumption.
do 2 right.
apply eqc_trans with l.
apply eqcleft; assumption.
exact h. apply exd_left.
apply exd_cA. exact H1. apply exd_left.
unfold crack. elim eq_dim_dec; try tauto.
intro hk; apply cracke_m_l_l0.
apply eqc_Split in h.
apply eqc_Split in h; try assumption.
do 2 right.
apply eqc_trans with l.
apply eqcleft; assumption.
exact h. apply exd_left.
apply exd_cA. exact H1. apply exd_left.
unfold crack. elim eq_dim_dec; try tauto.
intro hk; apply cracke_m_l_l0.
apply inv_hmap_m1.
apply exd_m1; apply exd_cA_1. exact H1. apply exd_right.
apply exd_m1; apply exd_right.
unfold crack. elim eq_dim_dec; try tauto.
intro hk; apply cracke_m1_r0_r; assumption.
elimination t3.
destruct t3 as [t3 t4].
assert False; [idtac|tauto].
apply not_eqc_m3_max_l.
apply eqc_symm; exact t3.
destruct t3 as [t3 t4].
assert False; [idtac|tauto].
apply not_eqc_m3_x_l.
apply eqc_symm; exact t3.
apply inv_hmap_m3.
unfold m3; simpl; tauto.
unfold m3; simpl; tauto.
apply inv_hmap_m4.
apply exd_m4; apply exd_m3_2; apply exd_m2.
apply exd_m1; apply exd_left.
apply exd_m4; unfold m3; simpl; tauto.
apply inv_hmap_m5.
apply exd_m5; apply exd_m4; unfold m3; simpl; tauto.
apply exd_m5; apply exd_m4; apply exd_m3_2.
apply exd_m2; apply exd_m1; apply exd_right.
Qed.

Lemma inv_poly_m6 : inv_poly m6 x.
Proof.
unfold inv_poly; intros k da hda.
generalize (eqc_m6_x_da_eqc_m_d_da da hda).
intro t0; induction k.
elim (eq_dart_dec da x); intro h1.
subst da; rewrite cA_m6_zero_x.
intro h; apply H11; rewrite h; apply exd_right.
elim (eq_dart_dec da r); intro h2.
subst da; rewrite cA_m6_zero_r. exact h1.
rewrite cA_m6_zero_da; try assumption.
elim (eq_dart_dec da max); intro h3.
subst da; rewrite cA_m5_zero_max.
intro h; apply H12; rewrite h; apply exd_left.
elim (eq_dart_dec da l); intro h4.
subst da; rewrite cA_m5_zero_l. exact h3.
elimination t0. contradiction.
elimination t0. contradiction.
assert (h5: da <> l0).
elim (eq_dart_dec l0 r); intro h0.
rewrite <- h0 in h2; exact h2.
intro h. apply not_eqc_m6_r_r0.
exact h0. apply eqc_trans with x.
apply eqc_trans with max.
apply eqc_symm; apply expf_eqc.
apply inv_hmap_m6. apply expf_m6_max_r.
apply eqc_m6_max_x. apply eqc_trans with l0.
rewrite h in hda; exact hda.
apply expf_eqc. apply inv_hmap_m6.
apply expf_m6_l0_r0. exact h0.
assert (h6: da <> r0).
elim (eq_dart_dec l0 r); intro h0.
apply eq_l0_r_r0_l in h0.
rewrite h0; exact h4.
intro h. apply not_eqc_m6_r_r0.
exact h0. apply eqc_trans with x.
apply eqc_trans with max.
apply eqc_symm; apply expf_eqc.
apply inv_hmap_m6. apply expf_m6_max_r.
apply eqc_m6_max_x.
rewrite h in hda; exact hda.
rewrite cA_m5_zero_da; try assumption.
rewrite cA_m4_zero_da; try assumption.
rewrite cA_m3_zero_da; try assumption.
rewrite cA_m2_zero_da; try assumption.
rewrite cA_m1_zero_da; try assumption.
apply H3. exact t0.
apply eqc_exd_exd in t0.
destruct t0 as [t1 t2].
apply exd_m1 in t2. exact t2.
apply eqc_exd_exd in t0.
destruct t0 as [t1 t2].
apply exd_m1 in t2.
apply exd_m2 in t2. exact t2.
apply eqc_exd_exd in hda.
destruct hda as [t1 t2].
apply exd_m6 in t2.
apply exd_m5 in t2.
apply exd_m4 in t2.
exact t2.
apply eqc_exd_exd in hda.
destruct hda as [t1 t2].
apply exd_m6 in t2.
apply exd_m5 in t2.
exact t2.
apply eqc_exd_exd in hda.
destruct hda as [t1 t2].
apply exd_m6 in t2.
exact t2.
apply eqc_exd_exd in hda.
destruct hda as [t1 t2].
exact t2.
rewrite cA_m6_one_da; try assumption.
rewrite cA_m5_one_da; try assumption.
elim (eq_dart_dec da x); intro h1.
subst da; rewrite cA_m4_one_x. exact H15.
elim (eq_dart_dec da max); intro h2.
subst da; rewrite cA_m4_one_max.
apply not_eq_sym; exact H15.
elimination t0. contradiction.
elimination t0. contradiction.
rewrite cA_m4_one_da; try assumption.
rewrite cA_m3_one_da; try assumption.
rewrite cA_m2_one_da; try assumption.
rewrite cA_m1_one_da; try assumption.
apply H3. exact t0.
apply eqc_exd_exd in t0.
destruct t0 as [t1 t2].
apply exd_m1 in t2. exact t2.
apply eqc_exd_exd in t0.
destruct t0 as [t1 t2].
apply exd_m1 in t2.
apply exd_m2 in t2. exact t2.
apply eqc_exd_exd in hda.
destruct hda as [t1 t2].
apply exd_m6 in t2.
apply exd_m5 in t2.
apply exd_m4 in t2.
exact t2.
apply eqc_exd_exd in hda.
destruct hda as [t1 t2].
apply exd_m6 in t2.
apply exd_m5 in t2.
exact t2.
apply eqc_exd_exd in hda.
destruct hda as [t1 t2].
apply exd_m6 in t2.
exact t2.
apply eqc_exd_exd in hda.
destruct hda as [t1 t2].
exact t2.
Qed.

(* ================================ *)

Lemma expf_m2_r0_cA_m_one_r0 : expf m2 r0 (cA m one r0).
Proof.
unfold expf; split. apply inv_hmap_m2.
unfold m2; elim eq_dart_dec; intro h.
apply expf_m1_r0_cA_m_one_r0.
assert (t1: inv_hmap m1). apply inv_hmap_m1.
assert (t2: inv_gmap m1). apply inv_gmap_m1.
apply (expof_Split0_CNS m1 r0 r r0 (cA m one r0) t1).
apply cracke_m1_r0_r; assumption.
apply exd_m1; apply exd_cA_1. exact H1. apply exd_right.
assert (t3: cA m1 zero r0 = r).
 rewrite cA_m1_zero_da. apply cA_m_zero_r0.
 apply exd_m1; apply exd_cA_1. exact H1. apply exd_right.
 intro h0; apply h; apply eq_l0_r_r0_l; assumption.
 apply not_eq_sym; apply neq_l0_r0. rewrite t3.
elim expof_dec; intro h0. right; left; split.
assert (t4: cA m1 zero r = r0).
 rewrite cA_m1_zero_da. rewrite eq_cA_cA_1; try assumption.
 unfold r0; tauto. apply exd_m1; apply exd_right.
 apply not_eq_sym; apply neq_left_right; try assumption.
 left; exact H10. apply not_eq_sym; exact h. rewrite t4.
apply MF.between_expo_refl_2. exact t1.
apply exd_cA_1. exact t1. apply exd_m1.
apply exd_cA_1. exact H1. apply exd_right.
apply MF.expo_expo1; try assumption.
replace MF.expo with expof; try tauto.
apply expf_symm. apply expf_expof. split. exact t1.
replace (cA_1 m1 one r0) with (cA m one r0).
apply expf_m1_r0_cA_m_one_r0.
rewrite <- eq_cA_cA_1; try assumption. rewrite cA_m1_one_da.
tauto. apply exd_m1. apply exd_cA_1. exact H1. apply exd_right.
replace (cA_1 m1 one r0) with (cA m one r0).
apply MF.between_expo_refl_1. exact t1.
apply exd_m1; apply exd_cA. exact H1.
apply exd_cA_1. exact H1. apply exd_right.
apply MF.expo_expo1; try assumption.
replace MF.expo with expof; try tauto.
replace (cA m1 zero r) with r0.
apply expf_symm. apply expf_expof. split. exact t1.
apply expf_m1_r0_cA_m_one_r0.
rewrite cA_m1_zero_da; try assumption.
rewrite eq_cA_cA_1; try tauto.
apply exd_m1; apply exd_right.
apply not_eq_sym; apply neq_left_right; try assumption.
left; exact H10. apply not_eq_sym; exact h.
rewrite <- eq_cA_cA_1; try assumption.
rewrite cA_m1_one_da. tauto. apply exd_m1.
apply exd_cA_1. exact H1. apply exd_right.
assert False; [idtac|tauto]. apply h0.
replace (cA_1 m1 one r) with (cA m one r).
apply expf_m1_r_r1.
rewrite <- eq_cA_cA_1; try assumption.
rewrite cA_m1_one_da. trivial.
apply exd_m1; apply exd_right.
Qed.

Lemma degreef_m1_r1 :
  degreef m1 r1 = degreef m r1 + degreef m l0.
Proof.
assert (h1: cracke m l l0).
 apply cracke_m_l_l0.
assert (h2: exd m r1).
 apply exd_cA. exact H1. apply exd_right.
assert (h3: ~ expof m l0 (cA m one l0)).
 intro h; apply not_expf_m_l_l0.
 apply expf_trans with (cA m one l0).
 rewrite <- cA_m_zero_l0. apply expf_cA_cA.
 exact H1. exact H2. apply exd_cA. exact H1. apply exd_left.
 apply expf_symm; unfold expf; split. exact H1. apply h.
assert (h4: cA_1 m one l0 = cA m one l0).
 apply eq_sym; apply eq_cA_cA_1; assumption.
generalize (degreef_Split0_merge_summary m l l0 r1 H1 h1 h2).
fold l0; rewrite h4. intro h; generalize (h h3); clear h.
elim expof_dec; intro heq1.
assert False; [idtac|tauto].
apply not_expf_m_l_l0.
apply expf_trans with r0.
apply expfright; try assumption. apply exd_left.
apply exd_left_dart_exd_right_dart; assumption.
apply expf_trans with r1.
unfold r0, r1. rewrite <- eq_cA_cA_1; try assumption.
apply expf_cA_cA; try assumption. apply exd_right.
apply expf_symm; unfold expf; split. exact H1. apply heq1.
elim expof_dec; intro heq2. fold m1.
assert (h5: degreef m r1 = degreef m (cA m one l0)).
 apply MF.expo_degree; try assumption.
 apply expf_symm. unfold expf; split. exact H1. apply heq2.
intro h; rewrite h; rewrite h5; ring.
assert False; [idtac|tauto]. apply heq2.
apply expf_trans with r0. apply expf_trans with l.
apply expf_symm; rewrite <- cA_m_zero_l0.
apply expf_cA_cA; try assumption.
apply exd_cA. exact H1. apply exd_left.
apply expfright; try assumption. apply exd_left.
apply exd_left_dart_exd_right_dart; assumption.
unfold r0, r1; rewrite <- eq_cA_cA_1; try assumption.
apply expf_cA_cA; try assumption. apply exd_right.
Qed.

Lemma degreef_m2_r1 :
  l0 <> r -> degreef m1 r1 = degreef m2 r1 + degreef m2 l0.
Proof.
intro hneq.
assert (h1: inv_hmap m1).
 apply inv_hmap_m1.
assert (h2: cracke m1 r0 r).
 apply cracke_m1_r0_r; assumption.
assert (h3: exd m1 r1).
 apply exd_m1; apply exd_cA. exact H1. apply exd_right.
assert (h4: cA_1 m1 one r = r1).
 rewrite <- eq_cA_cA_1. rewrite cA_m1_one_da. tauto.
 apply exd_m1; apply exd_right. exact h1. apply inv_gmap_m1.
assert (h5: cA m1 zero r0 = r).
 rewrite cA_m1_zero_da. rewrite cA_m_zero_r0. tauto.
 apply exd_m1; apply exd_cA_1. exact H1. apply exd_right.
 intro h; apply hneq; apply eq_l0_r_r0_l; exact h.
 apply not_eq_sym; apply neq_l0_r0.
assert (h6: expf m1 r r1).
 apply expf_m1_r_r1.
destruct h6 as [h0 h6]; clear h0.
apply MF.expo_expo1 in h6; try assumption.
unfold MF.expo1 in h6; destruct h6 as [h0 h6]; clear h0.
elim h6; clear h6; intros i [hd hi]. unfold MF.f, McF.f in hi.
rewrite MF.upb_eq_degree in hd; try assumption.
replace MF.degree with degreef in hd; try tauto.
assert (h6: 2 <= i <= degreef m1 r1). split.
 elim (eq_dart_dec i 0); intro t1.
 subst i; assert False; [idtac|tauto].
 simpl in hi; apply H3 with one r; try assumption.
 apply eqc_trans with l. apply eqcleft; assumption.
 apply eqcright; try assumption. apply exd_left.
 apply exd_left_dart_exd_right_dart; assumption.
 elim (eq_dart_dec i 1); intro t2.
 subst i; simpl in hi; assert False; [idtac|tauto].
 assert (t0: cF m1 r = cA m one r0).
  unfold cF. rewrite <- eq_cA_cA_1. rewrite <- eq_cA_cA_1.
  rewrite cA_m1_zero_da. rewrite cA_m1_one_da.
  rewrite (eq_cA_cA_1 m zero r). fold r0. tauto.
  exact H1. exact H2. apply exd_m1.
  apply exd_cA. exact H1. apply exd_right.
  apply exd_m1; apply exd_right. apply not_eq_sym.
  apply neq_left_right; try assumption. left; exact H10.
  apply not_eq_sym; exact hneq. exact h1. apply inv_gmap_m1.
  exact h1. apply inv_gmap_m1. rewrite t0 in hi.
 apply not_expf_m_r_r0. apply expf_trans with r1.
 apply expf_trans with (cA m one r0). rewrite <- cA_m_zero_r0.
 apply expf_cA_cA; try assumption.
 apply exd_cA_1. exact H1. apply exd_right.
 rewrite hi. apply expf_refl; try assumption.
 apply exd_cA. exact H1. apply exd_right.
 unfold r0, r1; rewrite <- eq_cA_cA_1; try assumption.
 apply expf_symm; apply expf_cA_cA; try assumption. apply exd_right.
 omega. rewrite <- hi; rewrite <- MF.degree_uniform; try assumption.
 replace MF.degree with degreef; try tauto. omega.
 apply exd_m1; apply exd_right.
generalize (degreef_Split0_split_summary m1 r0 r r1 i h1 h2 h3).
rewrite h4; rewrite h5; apply eq_sym in hi.
intro h; generalize (h hi h6); clear h.
elim expof_dec; intro heq.
assert (h7: degreef m2 l0 = degreef m2 (cA_1 m1 one r0)).
 rewrite <- eq_cA_cA_1. rewrite cA_m1_one_da.
 apply MF.expo_degree. apply inv_hmap_m2.
 apply expf_trans with r0. apply expf_m2_l0_r0.
 apply expf_m2_r0_cA_m_one_r0. apply exd_m1.
 apply exd_cA_1. exact H1. apply exd_right.
 exact h1. apply inv_gmap_m1.
rewrite h7; unfold m2; eqdartdec; tauto.
assert False; [idtac|tauto]. apply heq.
apply expf_refl. exact h1. apply exd_m1.
apply exd_cA. exact H1. apply exd_right.
apply exd_m1; apply exd_right.
Qed.

(*
Lemma degreef_m3_r1 : degreef m3 r1 = degreef m2 r1.
Proof.
admit. (* <===== ADMIT in comment *)
Qed.
*)

Lemma degreef_m4_r1 : degreef m4 r1 = degreef m3 r1.
Proof.
assert (h1: inv_hmap m3).
 apply inv_hmap_m3.
assert (h2: exd m3 max).
 unfold m3; simpl; left; tauto.
assert (h3: exd m3 x).
 unfold m3; simpl; right; left; tauto.
assert (h4: ~ expv m3 max x).
 apply not_expv_m3_max_x.
assert (h5: exd m3 r1).
 apply exd_m3_2; apply exd_m2; apply exd_m1.
 apply exd_cA. exact H1. apply exd_right.
assert (h6: cA m3 zero x = x).
 apply cA_m3_zero_x.
assert (h7: ~ expof m3 x max).
 intro h; apply not_eqc_m3_x_max.
 apply expf_eqc; try assumption.
generalize (degreef_Merge1_merge_summary m3 max x r1 h1 h2 h3 h4 h5).
rewrite h6. intro h; generalize (h h7); clear h.
elim expof_dec; intro heq1.
assert False; [idtac|tauto].
apply not_eqc_m3_x_l. apply eqc_trans with r.
apply eqc_trans with r1. apply expf_eqc. exact h1.
apply heq1. apply eqc_symm. apply expf_eqc; try assumption.
apply expf_m3_r_cA_m_one_r. apply eqc_symm.
apply expf_eqc; try assumption. apply expf_m3_l_r.
elim expof_dec; intro heq2.
assert False; [idtac|tauto].
apply not_eqc_m3_max_l. apply eqc_trans with r.
apply eqc_trans with r1. apply expf_eqc. exact h1.
apply heq2. apply eqc_symm. apply expf_eqc. exact h1.
apply expf_m3_r_cA_m_one_r. apply eqc_symm.
apply expf_eqc. exact h1. apply expf_m3_l_r.
fold m4; tauto.
Qed.

Lemma degreef_m5_r1 :
  degreef m5 r1 = degreef m4 r1 + degreef m4 max.
Proof.
assert (h1: inv_hmap m4).
 apply inv_hmap_m4.
assert (h2: exd m4 l).
 apply exd_m4; apply exd_m3_2;
 apply exd_m2; apply exd_m1; apply exd_left.
assert (h3: exd m4 max).
 apply exd_m4; unfold m3; simpl; left; tauto.
assert (h4: ~ expe m4 l max).
 apply not_expe_m4_l_max.
assert (h5: exd m4 r1).
 apply exd_m4; apply exd_m3_2; apply exd_m2; apply exd_m1.
 apply exd_cA. exact H1. apply exd_right.
assert (h6: cA_1 m4 one l = l1).
 rewrite <- eq_cA_cA_1; try assumption.
 rewrite cA_m4_one_da; try assumption.
 rewrite cA_m3_one_da. rewrite cA_m2_one_da.
 rewrite cA_m1_one_da. unfold l1; tauto.
 apply exd_m1; apply exd_left.
 apply exd_m2; apply exd_m1; apply exd_left.
 apply exd_m3_2; apply exd_m2; apply exd_m1; apply exd_left.
 intro h; apply H11; rewrite <- h; apply exd_left.
 intro h; apply H12; rewrite <- h; apply exd_left.
 intro h; apply H11; rewrite <- h; apply exd_left.
 intro h; apply H12; rewrite <- h; apply exd_left.
 apply inv_gmap_m4.
assert (h7: ~ expof m4 max l1).
 intro h; apply not_expf_m4_max_cA_m_one_l.
 unfold expf; split. exact h1. apply h.
generalize (degreef_Merge0_merge_summary m4 l max r1 h1 h2 h3 h4 h5).
rewrite h6. intro h; generalize (h h7); clear h.
elim expof_dec; intro heq1.
assert False; [idtac|tauto].
 apply not_eqc_m4_x_l. apply eqc_trans with max.
 apply expf_eqc; try assumption. apply expf_m4_x_max.
 apply eqc_trans with r. apply eqc_trans with r1.
 apply expf_eqc; try assumption. apply eqc_symm. 
 apply expf_eqc; try assumption.
 apply expf_m4_r_cA_m_one_r. apply eqc_symm. 
 apply expf_eqc; try assumption. apply expf_m4_l_r.
elim expof_dec; intro heq2.
assert (h8: degreef m4 l1 = degreef m4 r1).
 apply MF.expo_degree; try assumption.
rewrite h8; fold m5; intro h; rewrite h; ring.
assert False; [idtac|tauto].
apply heq2. apply expf_trans with l.
apply expf_symm; apply expf_m4_l_cA_m_one_l.
apply expf_trans with r. apply expf_m4_l_r.
apply expf_m4_r_cA_m_one_r.
Qed.

Lemma degreef_m6_r1 :
  degreef m5 r1 = degreef m6 r1 + degreef m6 max.
Proof.
assert (h1: inv_hmap m5).
 apply inv_hmap_m5.
assert (h2: exd m5 x).
 apply exd_m5; apply exd_m4; unfold m3; simpl; right; left; tauto.
assert (h3: exd m5 r).
 apply exd_m5; apply exd_m4; apply exd_m3_2;
 apply exd_m2; apply exd_m1; apply exd_right.
assert (h4: ~ expe m5 x r).
 apply not_expe_m5_x_r.
assert (h5: exd m5 r1).
 apply exd_m5; apply exd_m4; apply exd_m3_2;
 apply exd_m2; apply exd_m1; apply exd_cA.
 exact H1. apply exd_right.
assert (h6: cA_1 m5 one x = max).
 rewrite <- eq_cA_cA_1. rewrite cA_m5_one_da.
 apply cA_m4_one_x. exact h2. exact h1. apply inv_gmap_m5.
assert (h7: expf m5 r max).
 apply expf_trans with l. apply expf_symm.
 apply expf_m5_l_r. apply expf_m5_l_max.
destruct h7 as [h0 h7]; clear h0.
apply MF.expo_expo1 in h7; try assumption.
unfold MF.expo1 in h7; destruct h7 as [h0 h7]; clear h0.
elim h7; clear h7; intros i [hd hi]. unfold MF.f, McF.f in hi.
rewrite MF.upb_eq_degree in hd; try assumption.
replace MF.degree with degreef in hd; try tauto.
assert (h8: 2 <= i <= degreef m5 max). split.
 elim (eq_dart_dec i 0); intro t1.
 subst i; assert False; [idtac|tauto].
 simpl in hi; apply H12; rewrite <- hi; apply exd_right.
 elim (eq_dart_dec i 1); intro t2.
 subst i; assert False; [idtac|tauto].
 simpl in hi; rewrite cF_m5_r in hi.
 apply H12; rewrite <- hi; apply exd_cA. exact H1. apply exd_right.
 omega. rewrite <- hi; rewrite <- MF.degree_uniform; try assumption.
 replace MF.degree with degreef; try tauto. omega.
generalize (degreef_Merge0_split_summary m5 x r r1 i h1 h2 h3 h4 h5).
rewrite h6; rewrite cF_m5_r; apply eq_sym in hi.
intro h; generalize (h hi h8); clear h.
elim expof_dec; intro heq.
fold m6; fold r1; intro h; rewrite h; ring.
assert False; [idtac|tauto]. apply heq.
apply expf_trans with r. apply expf_trans with l.
apply expf_symm; apply expf_m5_l_max. apply expf_m5_l_r.
apply expf_m5_r_cA_m_one_r.
Qed.

(* ================================ *)
(* ========== ########## ========== *)
(* ================================ *)

End CHID_sec.