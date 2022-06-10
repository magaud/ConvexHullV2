(* ================================ *)
(* ========== CH07_CH.v =========== *)
(* ================================ *)

Require Export CH06_CHID.

(* ================================ *)
(* ========== ########## ========== *)
(* ================================ *)

Section CH2_sec.

Variables (x1:dart)(t1:tag)(p1:point)(x2:dart)(t2:tag)(p2:point)(max:dart).

Let m1 := (I (I (I (I V x1 t1 p1) x2 t2 p2) (max + 1) t1 p1) (max + 2) t2 p2).
Let m2 := Merge m1 one (max + 1) x1.
Let m3 := Merge m2 one (max + 2) x2.
Let m4 := Merge m3 zero x1 (max + 2).
Let m5 := Merge m4 zero x2 (max + 1).

Hypothesis H1 : x1 <> x2.
Hypothesis H2 : x1 <> nil.
Hypothesis H3 : x2 <> nil.
Hypothesis H4 : x1 <= max.
Hypothesis H5 : x2 <= max.

Hypothesis Hp : p1 <> p2.

(* ================================ *)

Lemma inv_hmap_CH2_m1 : inv_hmap m1.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
unfold m1.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
Qed.

Lemma inv_hmap_CH2_m2 : inv_hmap m2.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
unfold m2.
apply inv_hmap_Merge1.
apply inv_hmap_CH2_m1.
simpl; tauto. simpl; tauto.
apply not_expv_I.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto. apply not_eq_sym; assumption.
apply not_expv_I.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto. apply not_eq_sym; assumption.
apply not_expv_I.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto. apply not_eq_sym; assumption.
apply not_expv_I.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto. apply not_eq_sym; assumption.
intro h; unfold expv, MA1.MfcA.expo in h.
destruct h as [h1 h2]; simpl in h1; assumption.
Qed.

Lemma inv_hmap_CH2_m3 : inv_hmap m3.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
unfold m3.
apply inv_hmap_Merge1.
apply inv_hmap_CH2_m2.
apply exd_Merge; simpl; tauto.
apply exd_Merge; simpl; tauto.
intro h; apply -> expv_Merge1_CNS in h.
elimination h.
apply expv_I in h. elimination h. intuition.
apply expv_I in h. elimination h. intuition.
apply expv_I in h. elimination h. intuition.
apply expv_I in h. elimination h. intuition.
unfold expv, MA1.MfcA.expo in h.
destruct h as [h1 h2]; simpl in h1; assumption.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
elimination h.
destruct h as [h0 h].
apply expv_I in h. elimination h. intuition.
apply expv_I in h. elimination h. intuition.
apply expv_I in h. elimination h. intuition.
apply expv_I in h. elimination h. intuition.
unfold expv, MA1.MfcA.expo in h.
destruct h as [h1 h2]; simpl in h1; assumption.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
destruct h as [h0 h].
apply expv_I in h. elimination h. intuition.
apply expv_I in h. elimination h. intuition.
apply expv_I in h. elimination h. intuition.
apply expv_I in h. elimination h. intuition.
unfold expv, MA1.MfcA.expo in h.
destruct h as [h1 h2]; simpl in h1; assumption.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
intro h0.
apply expv_I in h0. elimination h0. intuition.
apply expv_I in h0. elimination h0. intuition.
apply expv_I in h0. elimination h0. intuition.
apply expv_I in h0. elimination h0. intuition.
unfold expv, MA1.MfcA.expo in h0.
destruct h0 as [h1 h2]; simpl in h1; assumption.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
simpl; tauto. simpl; tauto. simpl; tauto.
apply inv_hmap_CH2_m1.
Qed.

Lemma inv_hmap_CH2_m4 : inv_hmap m4.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
unfold m4.
apply inv_hmap_Merge0.
apply inv_hmap_CH2_m3.
do 2 apply exd_Merge; simpl; tauto.
do 2 apply exd_Merge; simpl; tauto.
intro h. apply -> expe_Merge1 in h. apply -> expe_Merge1 in h.
apply expe_I in h. elimination h. intuition.
apply expe_I in h. elimination h. intuition.
apply expe_I in h. elimination h. intuition.
apply expe_I in h. elimination h. intuition.
unfold expe, MA0.MfcA.expo in h.
destruct h as [h1 h2]; simpl in h1; assumption.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
simpl; tauto. simpl; tauto.
apply inv_hmap_CH2_m1.
apply exd_Merge; simpl; tauto.
apply exd_Merge; simpl; tauto.
apply inv_hmap_CH2_m2.
Qed.

Lemma inv_hmap_CH2_m5 : inv_hmap m5.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
unfold m5.
apply inv_hmap_Merge0.
apply inv_hmap_CH2_m4.
do 3 apply exd_Merge; simpl; tauto.
do 3 apply exd_Merge; simpl; tauto.
intro h. apply -> expe_Merge0_CNS in h.
elimination h.
apply -> expe_Merge1 in h.
apply -> expe_Merge1 in h.
apply expe_I in h. elimination h. intuition.
apply expe_I in h. elimination h. intuition.
apply expe_I in h. elimination h. intuition.
apply expe_I in h. elimination h. intuition.
unfold expe, MA0.MfcA.expo in h.
destruct h as [h1 h2]; simpl in h1; assumption.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
simpl; tauto.
simpl; tauto.
apply inv_hmap_CH2_m1.
apply exd_Merge; simpl; tauto.
apply exd_Merge; simpl; tauto.
apply inv_hmap_CH2_m2.
elimination h.
destruct h as [h h0]; clear h0.
apply -> expe_Merge1 in h.
apply -> expe_Merge1 in h.
apply expe_I in h. elimination h. intuition.
apply expe_I in h. elimination h. intuition.
apply expe_I in h. elimination h. intuition.
apply expe_I in h. elimination h. intuition.
unfold expe, MA0.MfcA.expo in h.
destruct h as [h1 h2]; simpl in h1; assumption.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
simpl; tauto.
simpl; tauto.
apply inv_hmap_CH2_m1.
apply exd_Merge; simpl; tauto.
apply exd_Merge; simpl; tauto.
apply inv_hmap_CH2_m2.
destruct h as [h h0]; clear h0.
apply -> expe_Merge1 in h.
apply -> expe_Merge1 in h.
apply expe_I in h. elimination h. intuition.
apply expe_I in h. elimination h. intuition.
apply expe_I in h. elimination h. intuition.
apply expe_I in h. elimination h. intuition.
unfold expe, MA0.MfcA.expo in h.
destruct h as [h1 h2]; simpl in h1; assumption.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
simpl; tauto.
simpl; tauto.
apply inv_hmap_CH2_m1.
apply exd_Merge; simpl; tauto.
apply exd_Merge; simpl; tauto.
apply inv_hmap_CH2_m2.
intro h0.
apply -> expe_Merge1 in h0.
apply -> expe_Merge1 in h0.
apply expe_I in h0. elimination h0. intuition.
apply expe_I in h0. elimination h0. intuition.
apply expe_I in h0. elimination h0. intuition.
apply expe_I in h0. elimination h0. intuition.
unfold expe, MA0.MfcA.expo in h0.
destruct h0 as [h1 h2]; simpl in h1; assumption.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
simpl; tauto.
simpl; tauto.
apply inv_hmap_CH2_m1.
apply exd_Merge; simpl; tauto.
apply exd_Merge; simpl; tauto.
apply inv_hmap_CH2_m2.
do 2 apply exd_Merge; simpl; tauto.
do 2 apply exd_Merge; simpl; tauto.
do 2 apply exd_Merge; simpl; tauto.
apply inv_hmap_CH2_m3.
Qed.

(* ================================ *)

Lemma cA_m1_k_da :
  forall (k:dim)(da:dart), exd m1 da -> cA m1 k da = da.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
intros k da h; case k; unfold m1 in *; simpl in *.
elimination h. subst da; eqdartdec; trivial.
elimination h. subst da; eqdartdec; trivial.
elimination h. subst da; eqdartdec; trivial.
elimination h. subst da; eqdartdec; trivial.
tauto.
elimination h. subst da; eqdartdec; trivial.
elimination h. subst da; eqdartdec; trivial.
elimination h. subst da; eqdartdec; trivial.
elimination h. subst da; eqdartdec; trivial.
tauto.
Qed.

(* ===== *)

Lemma cA_m2_zero_da :
  forall (da:dart), exd m2 da -> cA m2 zero da = da.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
intros da h; unfold m2 in *; simpl in *.
elimination h. subst da; eqdartdec; trivial.
elimination h. subst da; eqdartdec; trivial.
elimination h. subst da; eqdartdec; trivial.
elimination h. subst da; eqdartdec; trivial.
tauto.
Qed.

Lemma cA_m2_one_x1 : cA m2 one x1 = max+1.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
unfold m2; simpl; eqdartdec; trivial.
Qed.

Lemma cA_m2_one_x2 : cA m2 one x2 = x2.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
unfold m2; simpl; eqdartdec; trivial.
Qed.

Lemma cA_m2_one_max1 : cA m2 one (max+1) = x1.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
unfold m2; simpl; eqdartdec; trivial.
Qed.

Lemma cA_m2_one_max2 : cA m2 one (max+2) = max+2.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
unfold m2; simpl; eqdartdec; trivial.
Qed.

(* ===== *)

Lemma cA_m3_zero_da :
  forall (da:dart), exd m3 da -> cA m3 zero da = da.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
intros da h; do 2 apply exd_Merge in h.
simpl in h; unfold m3. rewrite cA_Merge.
elim eq_dim_dec; intro h0; try inversion h0.
elimination h. subst da; rewrite cA_m2_zero_da.
trivial. apply exd_Merge; simpl; tauto.
elimination h. subst da; rewrite cA_m2_zero_da.
trivial. apply exd_Merge; simpl; tauto.
elimination h. subst da; rewrite cA_m2_zero_da.
trivial. apply exd_Merge; simpl; tauto.
elimination h. subst da; rewrite cA_m2_zero_da.
trivial. apply exd_Merge; simpl; tauto.
tauto. apply inv_hmap_CH2_m2.
Qed.

Lemma cA_m3_one_x1 : cA m3 one x1 = max+1.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
unfold m3. rewrite cA_Merge.
elim eq_dim_dec; intro h0; try tauto.
eqdartdec. elim eq_dart_dec.
unfold m2 at 1; rewrite -> cA_1_Merge.
elim eq_dim_dec; intro t0; try tauto.
eqdartdec. elim eq_dart_dec.
rewrite cA_m1_k_da; [idtac | simpl; tauto].
intro h; apply eq_sym in h; contradiction.
intro h1. simpl cA_1. eqdartdec.
intro h; apply eq_sym in h; contradiction.
apply inv_hmap_CH2_m1.
intro h; rewrite cA_m2_one_x1; trivial.
apply inv_hmap_CH2_m2.
Qed.

Lemma cA_m3_one_x2 : cA m3 one x2 = max+2.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
unfold m3. rewrite cA_Merge.
elim eq_dim_dec; intro h0; try tauto.
eqdartdec. elim eq_dart_dec.
intro h1. apply cA_m2_one_max2.
unfold m2 at 1; rewrite -> cA_1_Merge.
elim eq_dim_dec; intro t0; try tauto.
eqdartdec. elim eq_dart_dec.
rewrite cA_m1_k_da; [idtac | simpl; tauto].
intro h; apply eq_sym in h; contradiction.
intro h1. simpl cA_1. eqdartdec. tauto.
apply inv_hmap_CH2_m1. apply inv_hmap_CH2_m2.
Qed.

Lemma cA_m3_one_max1 : cA m3 one (max+1) = x1.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
unfold m3. rewrite cA_Merge.
elim eq_dim_dec; intro h0; try tauto.
eqdartdec. elim eq_dart_dec.
unfold m2 at 1; rewrite -> cA_1_Merge.
elim eq_dim_dec; intro t0; try tauto.
eqdartdec. elim eq_dart_dec.
rewrite cA_m1_k_da; [idtac | simpl; tauto].
intro h; apply eq_sym in h; contradiction.
intro h1. simpl cA_1. eqdartdec. tauto.
apply inv_hmap_CH2_m1.
intro h; rewrite cA_m2_one_max1; trivial.
apply inv_hmap_CH2_m2.
Qed.

Lemma cA_m3_one_max2 : cA m3 one (max+2) = x2.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
unfold m3. rewrite cA_Merge.
elim eq_dim_dec; intro h0; try tauto.
eqdartdec. trivial.
apply inv_hmap_CH2_m2.
Qed.

(* ===== *)

Lemma cA_m4_zero_x1 : cA m4 zero x1 = max+2.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
unfold m4. rewrite cA_Merge.
elim eq_dim_dec; intro h0; try tauto.
eqdartdec. trivial.
apply inv_hmap_CH2_m3.
Qed.

Lemma cA_m4_zero_x2 : cA m4 zero x2 = x2.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
unfold m4. rewrite cA_Merge.
elim eq_dim_dec; intro h0; try tauto.
eqdartdec. elim eq_dart_dec.
unfold m3 at 1; rewrite -> cA_1_Merge.
elim eq_dim_dec; intro t0; try inversion t0.
unfold m2 at 1; rewrite -> cA_1_Merge.
elim eq_dim_dec; intro k1; try inversion k1.
unfold m1 at 1; simpl cA_1. eqdartdec.
intro h; apply eq_sym in h; contradiction.
apply inv_hmap_CH2_m1. apply inv_hmap_CH2_m2.
intro h; rewrite cA_m3_zero_da; trivial.
do 2 apply exd_Merge; simpl; tauto.
apply inv_hmap_CH2_m3.
Qed.

Lemma cA_m4_zero_max1 : cA m4 zero (max+1) = max+1.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
unfold m4. rewrite cA_Merge.
elim eq_dim_dec; intro h0; try tauto.
eqdartdec. elim eq_dart_dec.
unfold m3 at 1; rewrite -> cA_1_Merge.
elim eq_dim_dec; intro t0; try inversion t0.
unfold m2 at 1; rewrite -> cA_1_Merge.
elim eq_dim_dec; intro k1; try inversion k1.
unfold m1 at 1; simpl cA_1. eqdartdec.
intro h; apply eq_sym in h; contradiction.
apply inv_hmap_CH2_m1. apply inv_hmap_CH2_m2.
intro h; rewrite cA_m3_zero_da; trivial.
do 2 apply exd_Merge; simpl; tauto.
apply inv_hmap_CH2_m3.
Qed.

Lemma cA_m4_zero_max2 : cA m4 zero (max+2) = x1.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
unfold m4. rewrite cA_Merge.
elim eq_dim_dec; intro h0; try tauto.
eqdartdec. elim eq_dart_dec.
intro h; rewrite cA_m3_zero_da; trivial.
do 2 apply exd_Merge; simpl; tauto.
unfold m3 at 1; rewrite -> cA_1_Merge.
elim eq_dim_dec; intro t0; try inversion t0.
unfold m2 at 1; rewrite -> cA_1_Merge.
elim eq_dim_dec; intro k1; try inversion k1.
unfold m1 at 1; simpl cA_1. eqdartdec. tauto.
apply inv_hmap_CH2_m1.
apply inv_hmap_CH2_m2.
apply inv_hmap_CH2_m3.
Qed.

Lemma cA_m4_one_x1 : cA m4 one x1 = max+1.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
unfold m4. rewrite cA_Merge.
elim eq_dim_dec; intro h0; try inversion h0.
rewrite cA_m3_one_x1; trivial.
apply inv_hmap_CH2_m3.
Qed.

Lemma cA_m4_one_x2 : cA m4 one x2 = max+2.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
unfold m4. rewrite cA_Merge.
elim eq_dim_dec; intro h0; try inversion h0.
rewrite cA_m3_one_x2; trivial.
apply inv_hmap_CH2_m3.
Qed.

Lemma cA_m4_one_max1 : cA m4 one (max+1) = x1.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
unfold m4. rewrite cA_Merge.
elim eq_dim_dec; intro h0; try inversion h0.
rewrite cA_m3_one_max1; trivial.
apply inv_hmap_CH2_m3.
Qed.

Lemma cA_m4_one_max2 : cA m4 one (max+2) = x2.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
unfold m4. rewrite cA_Merge.
elim eq_dim_dec; intro h0; try inversion h0.
rewrite cA_m3_one_max2; trivial.
apply inv_hmap_CH2_m3.
Qed.

(* ===== *)

Lemma cA_m5_zero_x1 : cA m5 zero x1 = max+2.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
unfold m5. rewrite cA_Merge.
elim eq_dim_dec; intro h0; try tauto.
eqdartdec. elim eq_dart_dec.
unfold m4 at 1; rewrite -> cA_1_Merge.
elim eq_dim_dec; intro t0; try tauto.
eqdartdec. elim eq_dart_dec.
rewrite cA_m3_zero_da. contradiction.
do 2 apply exd_Merge; simpl; tauto.
intro h1.
unfold m3 at 1; rewrite -> cA_1_Merge.
elim eq_dim_dec; intro k0; try inversion k0.
unfold m2 at 1; rewrite -> cA_1_Merge.
elim eq_dim_dec; intro k1; try inversion k1.
unfold m1 at 1; simpl cA_1. eqdartdec.
intro h; apply eq_sym in h; contradiction.
apply inv_hmap_CH2_m1.
apply inv_hmap_CH2_m2.
apply inv_hmap_CH2_m3.
intro h; apply cA_m4_zero_x1.
apply inv_hmap_CH2_m4.
Qed.

Lemma cA_m5_zero_x2 : cA m5 zero x2 = max+1.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
unfold m5. rewrite cA_Merge.
elim eq_dim_dec; intro h0; try tauto.
eqdartdec. trivial.
apply inv_hmap_CH2_m4.
Qed.

Lemma cA_m5_zero_max1 : cA m5 zero (max+1) = x2.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
unfold m5. rewrite cA_Merge.
elim eq_dim_dec; intro h0; try tauto.
eqdartdec. elim eq_dart_dec.
intro h; apply cA_m4_zero_x2.
unfold m4 at 1; rewrite -> cA_1_Merge.
elim eq_dim_dec; intro t0; try tauto.
eqdartdec. elim eq_dart_dec.
rewrite cA_m3_zero_da. contradiction.
do 2 apply exd_Merge; simpl; tauto.
intro h1.
unfold m3 at 1; rewrite -> cA_1_Merge.
elim eq_dim_dec; intro k0; try inversion k0.
unfold m2 at 1; rewrite -> cA_1_Merge.
elim eq_dim_dec; intro k1; try inversion k1.
unfold m1 at 1; simpl cA_1. eqdartdec. tauto.
apply inv_hmap_CH2_m1. apply inv_hmap_CH2_m2.
apply inv_hmap_CH2_m3. apply inv_hmap_CH2_m4.
Qed.

Lemma cA_m5_zero_max2 : cA m5 zero (max+2) = x1.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
unfold m5. rewrite cA_Merge.
elim eq_dim_dec; intro h0; try tauto.
eqdartdec. elim eq_dart_dec.
unfold m4 at 1; rewrite -> cA_1_Merge.
elim eq_dim_dec; intro t0; try tauto.
eqdartdec. elim eq_dart_dec.
rewrite cA_m3_zero_da. contradiction.
do 2 apply exd_Merge; simpl; tauto.
intro h1.
unfold m3 at 1; rewrite -> cA_1_Merge.
elim eq_dim_dec; intro k0; try inversion k0.
unfold m2 at 1; rewrite -> cA_1_Merge.
elim eq_dim_dec; intro k1; try inversion k1.
unfold m1 at 1; simpl cA_1. eqdartdec. tauto.
apply inv_hmap_CH2_m1.
apply inv_hmap_CH2_m2.
apply inv_hmap_CH2_m3.
intro h; apply cA_m4_zero_max2.
apply inv_hmap_CH2_m4.
Qed.

Lemma cA_m5_one_x1 : cA m5 one x1 = max+1.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
unfold m5. rewrite cA_Merge.
elim eq_dim_dec; intro h0; try inversion h0.
rewrite cA_m4_one_x1; trivial.
apply inv_hmap_CH2_m4.
Qed.

Lemma cA_m5_one_x2 : cA m5 one x2 = max+2.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
unfold m5. rewrite cA_Merge.
elim eq_dim_dec; intro h0; try inversion h0.
rewrite cA_m4_one_x2; trivial.
apply inv_hmap_CH2_m4.
Qed.

Lemma cA_m5_one_max1 : cA m5 one (max+1) = x1.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
unfold m5. rewrite cA_Merge.
elim eq_dim_dec; intro h0; try inversion h0.
rewrite cA_m4_one_max1; trivial.
apply inv_hmap_CH2_m4.
Qed.

Lemma cA_m5_one_max2 : cA m5 one (max+2) = x2.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
unfold m5. rewrite cA_Merge.
elim eq_dim_dec; intro h0; try inversion h0.
rewrite cA_m4_one_max2; trivial.
apply inv_hmap_CH2_m4.
Qed.

(* ================================ *)

Lemma inv_gmap_CH2_m1 : inv_gmap m1.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
unfold inv_gmap. intros k x hx.
do 2 rewrite cA_m1_k_da; try assumption. trivial.
Qed.

Lemma inv_gmap_CH2_m2 : inv_gmap m2.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
unfold inv_gmap. intros k x hx. case k.
(* k = zero *)
do 2 rewrite cA_m2_zero_da; try assumption. trivial.
(* k = one *)
apply exd_Merge in hx. simpl in hx.
elimination hx. subst x.
do 2 rewrite cA_m2_one_max2. trivial.
elimination hx. subst x.
rewrite cA_m2_one_max1. apply cA_m2_one_x1.
elimination hx. subst x.
do 2 rewrite cA_m2_one_x2. trivial.
elimination hx. subst x.
rewrite cA_m2_one_x1. apply cA_m2_one_max1.
tauto.
Qed.

Lemma inv_gmap_CH2_m3 : inv_gmap m3.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
unfold inv_gmap. intros k x hx. case k.
(* k = zero *)
do 2 rewrite cA_m3_zero_da; try assumption. trivial.
(* k = one *)
do 2 apply exd_Merge in hx. simpl in hx.
elimination hx. subst x.
rewrite cA_m3_one_max2. apply cA_m3_one_x2.
elimination hx. subst x.
rewrite cA_m3_one_max1. apply cA_m3_one_x1.
elimination hx. subst x.
rewrite cA_m3_one_x2. apply cA_m3_one_max2.
elimination hx. subst x.
rewrite cA_m3_one_x1. apply cA_m3_one_max1.
tauto.
Qed.

Lemma inv_gmap_CH2_m4 : inv_gmap m4.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
unfold inv_gmap. intros k x hx.
do 3 apply exd_Merge in hx. simpl in hx. case k.
(* k = zero *)
elimination hx. subst x.
rewrite cA_m4_zero_max2. apply cA_m4_zero_x1.
elimination hx. subst x.
rewrite cA_m4_zero_max1. apply cA_m4_zero_max1.
elimination hx. subst x.
rewrite cA_m4_zero_x2. apply cA_m4_zero_x2.
elimination hx. subst x.
rewrite cA_m4_zero_x1. apply cA_m4_zero_max2.
tauto.
(* k = one *)
elimination hx. subst x.
rewrite cA_m4_one_max2. apply cA_m4_one_x2.
elimination hx. subst x.
rewrite cA_m4_one_max1. apply cA_m4_one_x1.
elimination hx. subst x.
rewrite cA_m4_one_x2. apply cA_m4_one_max2.
elimination hx. subst x.
rewrite cA_m4_one_x1. apply cA_m4_one_max1.
tauto.
Qed.

Lemma inv_gmap_CH2_m5 : inv_gmap m5.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
unfold inv_gmap. intros k x hx.
do 4 apply exd_Merge in hx. simpl in hx. case k.
(* k = zero *)
elimination hx. subst x.
rewrite cA_m5_zero_max2. apply cA_m5_zero_x1.
elimination hx. subst x.
rewrite cA_m5_zero_max1. apply cA_m5_zero_x2.
elimination hx. subst x.
rewrite cA_m5_zero_x2. apply cA_m5_zero_max1.
elimination hx. subst x.
rewrite cA_m5_zero_x1. apply cA_m5_zero_max2.
tauto.
(* k = one *)
elimination hx. subst x.
rewrite cA_m5_one_max2. apply cA_m5_one_x2.
elimination hx. subst x.
rewrite cA_m5_one_max1. apply cA_m5_one_x1.
elimination hx. subst x.
rewrite cA_m5_one_x2. apply cA_m5_one_max2.
elimination hx. subst x.
rewrite cA_m5_one_x1. apply cA_m5_one_max1.
tauto.
Qed.

(* ================================ *)

Lemma inv_poly_m5 : inv_poly m5 x1.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
unfold inv_poly. intros k x.
fold m1. fold m2. fold m3. fold m4. fold m5. intro h.
assert (H: x = x1 \/ x = x2 \/ x = max+1 \/ x = max+2).
unfold m5 in h; apply eqc_Merge in h.
elimination h.
unfold m4 in h; apply eqc_Merge in h.
elimination h.
unfold m3 in h; apply eqc_Merge in h.
elimination h.
unfold m2 in h; apply eqc_Merge in h.
elimination h.
unfold m1 in h; simpl in h; tauto.
elimination h.
destruct h as [h0 h].
unfold m1 in h; simpl in h; tauto.
destruct h as [h0 h].
unfold m1 in h; simpl in h; tauto.
apply inv_hmap_CH2_m1.
unfold m1; simpl; tauto.
unfold m1; simpl; tauto.
elimination h.
destruct h as [h1 h].
unfold m2 in h; apply eqc_Merge in h.
elimination h.
unfold m1 in h; simpl in h; tauto.
elimination h.
destruct h as [h2 h].
unfold m1 in h; simpl in h; tauto.
destruct h as [h2 h].
unfold m1 in h; simpl in h; tauto.
apply inv_hmap_CH2_m1.
unfold m1; simpl; tauto.
unfold m1; simpl; tauto.
destruct h as [h1 h].
unfold m2 in h; apply eqc_Merge in h.
elimination h.
unfold m1 in h; simpl in h; tauto.
elimination h.
destruct h as [h2 h].
unfold m1 in h; simpl in h; tauto.
destruct h as [h2 h].
unfold m1 in h; simpl in h; tauto.
apply inv_hmap_CH2_m1.
unfold m1; simpl; tauto.
unfold m1; simpl; tauto.
apply inv_hmap_CH2_m2.
unfold m2; apply exd_Merge.
unfold m1; simpl; tauto.
unfold m2; apply exd_Merge.
unfold m1; simpl; tauto.
elimination h.
destruct h as [h1 h].
unfold m3 in h; apply eqc_Merge in h.
elimination h.
unfold m2 in h; apply eqc_Merge in h.
elimination h.
unfold m1 in h; simpl in h; tauto.
elimination h.
destruct h as [h2 h].
unfold m1 in h; simpl in h; tauto.
destruct h as [h2 h].
unfold m1 in h; simpl in h; tauto.
apply inv_hmap_CH2_m1.
unfold m1; simpl; tauto.
unfold m1; simpl; tauto.
elimination h.
destruct h as [h2 h].
unfold m2 in h; apply eqc_Merge in h.
elimination h.
unfold m1 in h; simpl in h; tauto.
elimination h.
destruct h as [h3 h].
unfold m1 in h; simpl in h; tauto.
destruct h as [h3 h].
unfold m1 in h; simpl in h; tauto.
apply inv_hmap_CH2_m1.
unfold m1; simpl; tauto.
unfold m1; simpl; tauto.
destruct h as [h2 h].
unfold m2 in h; apply eqc_Merge in h.
elimination h.
unfold m1 in h; simpl in h; tauto.
elimination h.
destruct h as [h3 h].
unfold m1 in h; simpl in h; tauto.
destruct h as [h3 h].
unfold m1 in h; simpl in h; tauto.
apply inv_hmap_CH2_m1.
unfold m1; simpl; tauto.
unfold m1; simpl; tauto.
apply inv_hmap_CH2_m2.
unfold m2; apply exd_Merge.
unfold m1; simpl; tauto.
unfold m2; apply exd_Merge.
unfold m1; simpl; tauto.
destruct h as [h1 h].
unfold m3 in h; apply eqc_Merge in h.
elimination h.
unfold m2 in h; apply eqc_Merge in h.
elimination h.
unfold m1 in h; simpl in h; tauto.
elimination h.
destruct h as [h2 h].
unfold m1 in h; simpl in h; tauto.
destruct h as [h2 h].
unfold m1 in h; simpl in h; tauto.
apply inv_hmap_CH2_m1.
unfold m1; simpl; tauto.
unfold m1; simpl; tauto.
elimination h.
destruct h as [h2 h].
unfold m2 in h; apply eqc_Merge in h.
elimination h.
unfold m1 in h; simpl in h; tauto.
elimination h.
destruct h as [h3 h].
unfold m1 in h; simpl in h; tauto.
destruct h as [h3 h].
unfold m1 in h; simpl in h; tauto.
apply inv_hmap_CH2_m1.
unfold m1; simpl; tauto.
unfold m1; simpl; tauto.
destruct h as [h2 h].
unfold m2 in h; apply eqc_Merge in h.
elimination h.
unfold m1 in h; simpl in h; tauto.
elimination h.
destruct h as [h3 h].
unfold m1 in h; simpl in h; tauto.
destruct h as [h3 h].
unfold m1 in h; simpl in h; tauto.
apply inv_hmap_CH2_m1.
unfold m1; simpl; tauto.
unfold m1; simpl; tauto.
apply inv_hmap_CH2_m2.
unfold m2; apply exd_Merge.
unfold m1; simpl; tauto.
unfold m2; apply exd_Merge.
unfold m1; simpl; tauto.
apply inv_hmap_CH2_m3.
unfold m3; apply exd_Merge.
unfold m2; apply exd_Merge.
unfold m1; simpl; tauto.
unfold m3; apply exd_Merge.
unfold m2; apply exd_Merge.
unfold m1; simpl; tauto.
elimination h.
destruct h as [h1 h].
unfold m4 in h; apply eqc_Merge in h.
elimination h.
unfold m3 in h; apply eqc_Merge in h.
elimination h.
unfold m2 in h; apply eqc_Merge in h.
elimination h.
unfold m1 in h; simpl in h; tauto.
elimination h.
destruct h as [h2 h].
unfold m1 in h; simpl in h; tauto.
destruct h as [h2 h].
unfold m1 in h; simpl in h; tauto.
apply inv_hmap_CH2_m1.
unfold m1; simpl; tauto.
unfold m1; simpl; tauto.
elimination h.
destruct h as [h2 h].
unfold m2 in h; apply eqc_Merge in h.
elimination h.
unfold m1 in h; simpl in h; tauto.
elimination h.
destruct h as [h3 h].
unfold m1 in h; simpl in h; tauto.
destruct h as [h3 h].
unfold m1 in h; simpl in h; tauto.
apply inv_hmap_CH2_m1.
unfold m1; simpl; tauto.
unfold m1; simpl; tauto.
destruct h as [h2 h].
unfold m2 in h; apply eqc_Merge in h.
elimination h.
unfold m1 in h; simpl in h; tauto.
elimination h.
destruct h as [h3 h].
unfold m1 in h; simpl in h; tauto.
destruct h as [h3 h].
unfold m1 in h; simpl in h; tauto.
apply inv_hmap_CH2_m1.
unfold m1; simpl; tauto.
unfold m1; simpl; tauto.
apply inv_hmap_CH2_m2.
unfold m2; apply exd_Merge.
unfold m1; simpl; tauto.
unfold m2; apply exd_Merge.
unfold m1; simpl; tauto.
elimination h.
destruct h as [h2 h].
unfold m3 in h; apply eqc_Merge in h.
elimination h.
unfold m2 in h; apply eqc_Merge in h.
elimination h.
unfold m1 in h; simpl in h; tauto.
elimination h.
destruct h as [h3 h].
unfold m1 in h; simpl in h; tauto.
destruct h as [h3 h].
unfold m1 in h; simpl in h; tauto.
apply inv_hmap_CH2_m1.
unfold m1; simpl; tauto.
unfold m1; simpl; tauto.
elimination h.
destruct h as [h3 h].
unfold m2 in h; apply eqc_Merge in h.
elimination h.
unfold m1 in h; simpl in h; tauto.
elimination h.
destruct h as [h4 h].
unfold m1 in h; simpl in h; tauto.
destruct h as [h4 h].
unfold m1 in h; simpl in h; tauto.
apply inv_hmap_CH2_m1.
unfold m1; simpl; tauto.
unfold m1; simpl; tauto.
destruct h as [h3 h].
unfold m2 in h; apply eqc_Merge in h.
elimination h.
unfold m1 in h; simpl in h; tauto.
elimination h.
destruct h as [h4 h].
unfold m1 in h; simpl in h; tauto.
destruct h as [h4 h].
unfold m1 in h; simpl in h; tauto.
apply inv_hmap_CH2_m1.
unfold m1; simpl; tauto.
unfold m1; simpl; tauto.
apply inv_hmap_CH2_m2.
unfold m2; apply exd_Merge.
unfold m1; simpl; tauto.
unfold m2; apply exd_Merge.
unfold m1; simpl; tauto.
destruct h as [h2 h].
unfold m3 in h; apply eqc_Merge in h.
elimination h.
unfold m2 in h; apply eqc_Merge in h.
elimination h.
unfold m1 in h; simpl in h; tauto.
elimination h.
destruct h as [h3 h].
unfold m1 in h; simpl in h; tauto.
destruct h as [h3 h].
unfold m1 in h; simpl in h; tauto.
apply inv_hmap_CH2_m1.
unfold m1; simpl; tauto.
unfold m1; simpl; tauto.
elimination h.
destruct h as [h3 h].
unfold m2 in h; apply eqc_Merge in h.
elimination h.
unfold m1 in h; simpl in h; tauto.
elimination h.
destruct h as [h4 h].
unfold m1 in h; simpl in h; tauto.
destruct h as [h4 h].
unfold m1 in h; simpl in h; tauto.
apply inv_hmap_CH2_m1.
unfold m1; simpl; tauto.
unfold m1; simpl; tauto.
destruct h as [h3 h].
unfold m2 in h; apply eqc_Merge in h.
elimination h.
unfold m1 in h; simpl in h; tauto.
elimination h.
destruct h as [h4 h].
unfold m1 in h; simpl in h; tauto.
destruct h as [h4 h].
unfold m1 in h; simpl in h; tauto.
apply inv_hmap_CH2_m1.
unfold m1; simpl; tauto.
unfold m1; simpl; tauto.
apply inv_hmap_CH2_m2.
unfold m2; apply exd_Merge.
unfold m1; simpl; tauto.
unfold m2; apply exd_Merge.
unfold m1; simpl; tauto.
apply inv_hmap_CH2_m3.
unfold m3; apply exd_Merge.
unfold m2; apply exd_Merge.
unfold m1; simpl; tauto.
unfold m3; apply exd_Merge.
unfold m2; apply exd_Merge.
unfold m1; simpl; tauto.
destruct h as [h1 h].
unfold m4 in h; apply eqc_Merge in h.
elimination h.
unfold m3 in h; apply eqc_Merge in h.
elimination h.
unfold m2 in h; apply eqc_Merge in h.
elimination h.
unfold m1 in h; simpl in h; tauto.
elimination h.
destruct h as [h2 h].
unfold m1 in h; simpl in h; tauto.
destruct h as [h2 h].
unfold m1 in h; simpl in h; tauto.
apply inv_hmap_CH2_m1.
unfold m1; simpl; tauto.
unfold m1; simpl; tauto.
elimination h.
destruct h as [h2 h].
unfold m2 in h; apply eqc_Merge in h.
elimination h.
unfold m1 in h; simpl in h; tauto.
elimination h.
destruct h as [h3 h].
unfold m1 in h; simpl in h; tauto.
destruct h as [h3 h].
unfold m1 in h; simpl in h; tauto.
apply inv_hmap_CH2_m1.
unfold m1; simpl; tauto.
unfold m1; simpl; tauto.
destruct h as [h2 h].
unfold m2 in h; apply eqc_Merge in h.
elimination h.
unfold m1 in h; simpl in h; tauto.
elimination h.
destruct h as [h3 h].
unfold m1 in h; simpl in h; tauto.
destruct h as [h3 h].
unfold m1 in h; simpl in h; tauto.
apply inv_hmap_CH2_m1.
unfold m1; simpl; tauto.
unfold m1; simpl; tauto.
apply inv_hmap_CH2_m2.
unfold m2; apply exd_Merge.
unfold m1; simpl; tauto.
unfold m2; apply exd_Merge.
unfold m1; simpl; tauto.
elimination h.
destruct h as [h2 h].
unfold m3 in h; apply eqc_Merge in h.
elimination h.
unfold m2 in h; apply eqc_Merge in h.
elimination h.
unfold m1 in h; simpl in h; tauto.
elimination h.
destruct h as [h3 h].
unfold m1 in h; simpl in h; tauto.
destruct h as [h3 h].
unfold m1 in h; simpl in h; tauto.
apply inv_hmap_CH2_m1.
unfold m1; simpl; tauto.
unfold m1; simpl; tauto.
elimination h.
destruct h as [h3 h].
unfold m2 in h; apply eqc_Merge in h.
elimination h.
unfold m1 in h; simpl in h; tauto.
elimination h.
destruct h as [h4 h].
unfold m1 in h; simpl in h; tauto.
destruct h as [h4 h].
unfold m1 in h; simpl in h; tauto.
apply inv_hmap_CH2_m1.
unfold m1; simpl; tauto.
unfold m1; simpl; tauto.
destruct h as [h3 h].
unfold m2 in h; apply eqc_Merge in h.
elimination h.
unfold m1 in h; simpl in h; tauto.
elimination h.
destruct h as [h4 h].
unfold m1 in h; simpl in h; tauto.
destruct h as [h4 h].
unfold m1 in h; simpl in h; tauto.
apply inv_hmap_CH2_m1.
unfold m1; simpl; tauto.
unfold m1; simpl; tauto.
apply inv_hmap_CH2_m2.
unfold m2; apply exd_Merge.
unfold m1; simpl; tauto.
unfold m2; apply exd_Merge.
unfold m1; simpl; tauto.
destruct h as [h2 h].
unfold m3 in h; apply eqc_Merge in h.
elimination h.
unfold m2 in h; apply eqc_Merge in h.
elimination h.
unfold m1 in h; simpl in h; tauto.
elimination h.
destruct h as [h3 h].
unfold m1 in h; simpl in h; tauto.
destruct h as [h3 h].
unfold m1 in h; simpl in h; tauto.
apply inv_hmap_CH2_m1.
unfold m1; simpl; tauto.
unfold m1; simpl; tauto.
elimination h.
destruct h as [h3 h].
unfold m2 in h; apply eqc_Merge in h.
elimination h.
unfold m1 in h; simpl in h; tauto.
elimination h.
destruct h as [h4 h].
unfold m1 in h; simpl in h; tauto.
destruct h as [h4 h].
unfold m1 in h; simpl in h; tauto.
apply inv_hmap_CH2_m1.
unfold m1; simpl; tauto.
unfold m1; simpl; tauto.
destruct h as [h3 h].
unfold m2 in h; apply eqc_Merge in h.
elimination h.
unfold m1 in h; simpl in h; tauto.
elimination h.
destruct h as [h4 h].
unfold m1 in h; simpl in h; tauto.
destruct h as [h4 h].
unfold m1 in h; simpl in h; tauto.
apply inv_hmap_CH2_m1.
unfold m1; simpl; tauto.
unfold m1; simpl; tauto.
apply inv_hmap_CH2_m2.
unfold m2; apply exd_Merge.
unfold m1; simpl; tauto.
unfold m2; apply exd_Merge.
unfold m1; simpl; tauto.
apply inv_hmap_CH2_m3.
unfold m3; apply exd_Merge.
unfold m2; apply exd_Merge.
unfold m1; simpl; tauto.
unfold m3; apply exd_Merge.
unfold m2; apply exd_Merge.
unfold m1; simpl; tauto.
apply inv_hmap_CH2_m4.
unfold m4; apply exd_Merge.
unfold m3; apply exd_Merge.
unfold m2; apply exd_Merge.
unfold m1; simpl; tauto.
unfold m4; apply exd_Merge.
unfold m3; apply exd_Merge.
unfold m2; apply exd_Merge.
unfold m1; simpl; tauto.
case k.
(* k = zero *)
elimination H. subst x.
rewrite cA_m5_zero_x1; assumption.
elimination H. subst x.
rewrite cA_m5_zero_x2; assumption.
elimination H; subst x.
rewrite cA_m5_zero_max1; lia.
rewrite cA_m5_zero_max2; lia.
(* k = one *)
elimination H. subst x.
rewrite cA_m5_one_x1; assumption.
elimination H. subst x.
rewrite cA_m5_one_x2; assumption.
elimination H; subst x.
rewrite cA_m5_one_max1; lia.
rewrite cA_m5_one_max2; lia.
Qed.

(* ================================ *)

Lemma planar_CH2_m1 : planar m1.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
unfold m1.
apply planar_I.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
apply planar_I.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
apply planar_I.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
apply planar_I.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
unfold planar, genus; simpl; trivial.
unfold prec_I; simpl; repeat split; tauto.
unfold prec_I; simpl; repeat split; tauto.
unfold prec_I; simpl; repeat split; tauto.
unfold prec_I; simpl; repeat split; tauto.
Qed.

Lemma planar_CH2_m2 : planar m2.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
unfold m2. apply <- planarity_crit_Merge1. split.
apply planar_CH2_m1. left. simpl; intro h.
elimination h. destruct h as [h1 h2]. contradiction.
elimination h. destruct h as [h1 h2]. contradiction.
elimination h. destruct h as [h1 h2]. contradiction.
elimination h. destruct h as [h1 h2].
apply eq_sym in h1; contradiction. assumption.
apply not_expv_I; [idtac | simpl; intro h | idtac | idtac].
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
elimination h. contradiction.
elimination h. contradiction.
elimination h; tauto.
apply not_eq_sym; assumption.
apply not_expv_I; [idtac | simpl; intro h | idtac | idtac].
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
elimination h. contradiction.
elimination h; tauto.
apply not_eq_sym; assumption.
apply not_expv_I; [idtac | simpl; intro h | idtac | idtac].
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
elimination h; tauto.
apply not_eq_sym; assumption.
apply not_expv_I; [idtac | simpl; tauto | idtac | idtac].
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
apply not_eq_sym; assumption.
apply not_exd_not_expv. simpl. tauto.
simpl; tauto. simpl; tauto.
apply inv_hmap_CH2_m1.
Qed.

Lemma planar_CH2_m3 : planar m3.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
unfold m3. apply <- planarity_crit_Merge1. split.
apply planar_CH2_m2. left.
intro h. apply eqc_Merge in h.
elimination h. simpl in h.
do 4 (elimination h; [intuition|idtac]). tauto.
elimination h; destruct h as [h1 h2]; simpl in h2.
do 4 (elimination h2; [intuition|idtac]). tauto.
do 4 (elimination h2; [intuition|idtac]). tauto.
apply inv_hmap_CH2_m1. simpl; tauto. simpl; tauto.
intro h. apply expv_Merge1_CNS in h.
elimination h. apply expv_I in h.
elimination h; [intuition|idtac]. apply expv_I in h.
elimination h; [intuition|idtac]. apply expv_I in h.
elimination h; [intuition|idtac]. apply expv_I in h.
elimination h; [intuition|idtac].
apply not_exd_not_expv with V (max+2) x2; try assumption.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
elimination h; destruct h as [h1 h]; apply expv_I in h.
elimination h; [intuition|idtac]. apply expv_I in h.
elimination h; [intuition|idtac]. apply expv_I in h.
elimination h; [intuition|idtac]. apply expv_I in h.
elimination h; [intuition|idtac].
apply not_exd_not_expv with V x1 x2; try assumption.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
elimination h; [intuition|idtac]. apply expv_I in h.
elimination h; [intuition|idtac]. apply expv_I in h.
elimination h; [intuition|idtac]. apply expv_I in h.
elimination h; [intuition|idtac].
apply not_exd_not_expv with V x1 (max+2); try assumption.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
apply inv_hmap_CH2_m1.
simpl; tauto. simpl; tauto. simpl; tauto.
intro h0. apply expv_I in h0.
elimination h0; [intuition|idtac]. apply expv_I in h0.
elimination h0; [intuition|idtac]. apply expv_I in h0.
elimination h0; [intuition|idtac]. apply expv_I in h0.
elimination h0; [intuition|idtac].
apply not_exd_not_expv with V (max+1) x1; try assumption.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
apply exd_Merge; simpl; tauto.
apply exd_Merge; simpl; tauto.
apply inv_hmap_CH2_m2.
Qed.

Lemma planar_CH2_m4 : planar m4.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
unfold m4. apply <- planarity_crit_Merge0. split.
apply planar_CH2_m3. left.
intro h. apply eqc_Merge in h.
elimination h. apply eqc_Merge in h. simpl in h.
elimination h.
do 4 (elimination h; [intuition|idtac]). tauto.
elimination h. destruct h as [h h0].
do 4 (elimination h; [intuition|idtac]). tauto.
elimination h.
do 4 (elimination h; [intuition|idtac]). tauto.
apply inv_hmap_CH2_m1.
simpl; tauto. simpl; tauto.
elimination h; destruct h as [h h0].
apply eqc_Merge in h. simpl in h.
elimination h.
do 4 (elimination h; [intuition|idtac]). tauto.
elimination h. destruct h as [h hz].
do 4 (elimination h; [intuition|idtac]). tauto.
elimination h.
do 4 (elimination h; [intuition|idtac]). tauto.
apply inv_hmap_CH2_m1.
simpl; tauto. simpl; tauto.
apply eqc_Merge in h. simpl in h.
elimination h.
do 4 (elimination h; [intuition|idtac]). tauto.
elimination h. destruct h as [h hz].
do 4 (elimination h; [intuition|idtac]). tauto.
elimination h.
do 4 (elimination h; [intuition|idtac]). tauto.
apply inv_hmap_CH2_m1.
simpl; tauto. simpl; tauto.
apply inv_hmap_CH2_m2.
apply exd_Merge; simpl; tauto.
apply exd_Merge; simpl; tauto.
intro h. do 2 apply expe_Merge1 in h.
apply expe_I in h.
elimination h; [intuition|idtac]. apply expe_I in h.
elimination h; [intuition|idtac]. apply expe_I in h.
elimination h; [intuition|idtac]. apply expe_I in h.
elimination h; [intuition|idtac].
apply not_exd_not_expe with V x1 (max+2); try assumption.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
apply inv_hmap_CH2_m1.
simpl; tauto. simpl; tauto.
apply inv_hmap_CH2_m2.
apply inv_hmap_CH2_m2.
apply exd_Merge; simpl; tauto.
apply exd_Merge; simpl; tauto.
apply exd_Merge; simpl; tauto.
apply inv_hmap_CH2_m2.
apply exd_Merge; simpl; tauto.
apply exd_Merge; simpl; tauto.
apply exd_Merge; simpl; tauto.
apply inv_hmap_CH2_m2.
apply exd_Merge; simpl; tauto.
apply exd_Merge; simpl; tauto.
do 2 apply exd_Merge; simpl; tauto.
do 2 apply exd_Merge; simpl; tauto.
apply inv_hmap_CH2_m3.
Qed.

Lemma expf_m4_max2_max1 : expf m4 (max + 2) (max + 1).
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
unfold expf; split. apply inv_hmap_CH2_m4. unfold m4.
assert (h0: inv_hmap m3). apply inv_hmap_CH2_m3.
rewrite (expof_Merge0_CNS m3 x1 (max+2) (max+2) (max+1) h0).
rewrite <- eq_cA_cA_1. rewrite cA_m3_one_x1.
elim expof_dec; intro h2.
assert False; [idtac|tauto]. apply expf_eqc in h2. 
unfold m3 in h2. apply eqc_Merge in h2.
(**)
elimination h2.
unfold m2 in h2. apply eqc_Merge in h2.
elimination h2.
unfold m1 in h2. simpl in h2.
elimination h2. tauto.
elimination h2. destruct h2 as [h2 h3].
apply eq_sym in h2. contradiction.
elimination h2. destruct h2 as [h2 h3].
apply eq_sym in h2. contradiction.
elimination h2. destruct h2 as [h2 h3].
apply eq_sym in h2. contradiction.
tauto.
elimination h2. destruct h2 as [h2 h3].
unfold m1 in h3. simpl in h3.
elimination h3. tauto.
elimination h3. tauto.
elimination h3. tauto.
elimination h3. destruct h3 as [h3 h4].
apply eq_sym in h4. contradiction.
tauto.
destruct h2 as [h2 h3].
unfold m1 in h2. simpl in h2.
elimination h2. tauto.
elimination h2. tauto.
elimination h2. tauto.
elimination h2. destruct h2 as [h2 h4].
apply eq_sym in h2. contradiction.
tauto.
apply inv_hmap_CH2_m1.
unfold m1; simpl. tauto.
unfold m1; simpl. tauto.
(**)
elimination h2. destruct h2 as [h2 h3].
unfold m2 in h3. apply eqc_Merge in h3.
elimination h3.
unfold m1 in h3. simpl in h3.
elimination h3. tauto.
elimination h3. tauto.
elimination h3. destruct h3 as [h3 h4].
apply eq_sym in h4. contradiction.
elimination h3. destruct h3 as [h3 h4].
apply eq_sym in h3. contradiction.
tauto.
elimination h3. destruct h3 as [h3 h4].
unfold m1 in h4. simpl in h4.
elimination h4. tauto.
elimination h4. tauto.
elimination h4. tauto.
elimination h4. destruct h4 as [h4 h5].
apply eq_sym in h5. contradiction.
tauto.
destruct h3 as [h3 h4].
unfold m1 in h3. simpl in h3.
elimination h3. tauto.
elimination h3. tauto.
elimination h3. tauto.
elimination h3. destruct h3 as [h3 h5].
apply eq_sym in h3. contradiction.
tauto.
apply inv_hmap_CH2_m1.
unfold m1; simpl; tauto.
unfold m1; simpl; tauto.
(**)
destruct h2 as [h2 h3].
unfold m2 in h3. apply eqc_Merge in h3.
elimination h3.
unfold m1 in h3. simpl in h3.
elimination h3. tauto.
elimination h3. destruct h3 as [h3 h4].
apply eq_sym in h3. contradiction.
elimination h3. destruct h3 as [h3 h4].
apply eq_sym in h4. contradiction.
elimination h3. destruct h3 as [h3 h4].
apply eq_sym in h3. contradiction.
tauto.
elimination h3. destruct h3 as [h3 h4].
unfold m1 in h4. simpl in h4.
elimination h4. tauto.
elimination h4. tauto.
elimination h4. tauto.
elimination h4. destruct h4 as [h4 h5].
apply eq_sym in h5. contradiction.
tauto.
destruct h3 as [h3 h4].
unfold m1 in h3. simpl in h3.
elimination h3. tauto.
elimination h3. tauto.
elimination h3. tauto.
elimination h3. destruct h3 as [h3 h5].
apply eq_sym in h3. contradiction.
tauto.
apply inv_hmap_CH2_m1.
unfold m1; simpl; tauto.
unfold m1; simpl; tauto.
(**)
apply inv_hmap_CH2_m2.
unfold m2. apply exd_Merge.
unfold m1; simpl; tauto.
unfold m2. apply exd_Merge.
unfold m1; simpl; tauto.
apply inv_hmap_CH2_m3.
right; left; split; apply expf_refl.
apply inv_hmap_CH2_m3.
unfold m3; apply exd_Merge.
unfold m2; apply exd_Merge.
unfold m1; simpl; tauto.
apply inv_hmap_CH2_m3.
unfold m3; apply exd_Merge.
unfold m2; apply exd_Merge.
unfold m1; simpl; tauto.
apply inv_hmap_CH2_m3.
apply inv_gmap_CH2_m3.
unfold m3; apply exd_Merge.
unfold m2; apply exd_Merge.
unfold m1; simpl; tauto.
unfold m3; apply exd_Merge.
unfold m2; apply exd_Merge.
unfold m1; simpl; tauto.
(**)
intro h.
unfold m3 in h. apply expe_Merge1 in h.
unfold m2 in h. apply expe_Merge1 in h.
unfold m1 in h.
apply expe_I in h. elimination h.
destruct h as [h1 h2].
apply eq_sym in h1. contradiction.
apply expe_I in h. elimination h.
destruct h as [h1 h2].
apply eq_sym in h1. contradiction.
apply expe_I in h. elimination h.
destruct h as [h1 h2].
apply eq_sym in h1. contradiction.
apply expe_I in h. elimination h.
destruct h as [h1 h2].
apply eq_sym in h1. contradiction.
apply not_exd_not_expe with V x1 (max+2).
simpl; tauto. exact h.
(**)
simpl; tauto. simpl; tauto.
simpl; split; try tauto.
unfold prec_I; split; simpl; tauto.
simpl; tauto.
simpl; split; try tauto.
unfold prec_I; split; simpl; tauto.
unfold prec_I; split; simpl; tauto.
simpl; tauto.
simpl; split; try tauto.
unfold prec_I; split; simpl; tauto.
unfold prec_I; split; simpl; tauto.
simpl; tauto.
apply inv_hmap_CH2_m1.
simpl; tauto. simpl; tauto.
apply inv_hmap_CH2_m2.
apply exd_Merge; simpl; tauto.
apply exd_Merge; simpl; tauto.
do 2 apply exd_Merge; simpl; tauto.
Qed.

Lemma not_expe_m4_x2_max1 : ~ expe m4 x2 (max + 1).
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
intro h. apply expe_Merge0_CNS in h.
elimination h. do 2 apply expe_Merge1 in h.
apply expe_I in h.
elimination h; [intuition|idtac]. apply expe_I in h.
elimination h; [intuition|idtac]. apply expe_I in h.
elimination h; [intuition|idtac]. apply expe_I in h.
elimination h; [intuition|idtac].
apply not_exd_not_expe with V x2 (max+1); try assumption.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
apply inv_hmap_CH2_m1.
simpl; tauto. simpl; tauto.
apply inv_hmap_CH2_m2.
apply inv_hmap_CH2_m2.
apply exd_Merge; simpl; tauto.
apply exd_Merge; simpl; tauto.
apply exd_Merge; simpl; tauto.
apply inv_hmap_CH2_m2.
apply exd_Merge; simpl; tauto.
apply exd_Merge; simpl; tauto.
apply exd_Merge; simpl; tauto.
apply inv_hmap_CH2_m2.
apply exd_Merge; simpl; tauto.
apply exd_Merge; simpl; tauto.
elimination h; destruct h as [h h0].
do 2 apply expe_Merge1 in h.
apply expe_I in h.
elimination h; [intuition|idtac]. apply expe_I in h.
elimination h; [intuition|idtac]. apply expe_I in h.
elimination h; [intuition|idtac]. apply expe_I in h.
elimination h; [intuition|idtac].
apply not_exd_not_expe with V x1 x2; try assumption.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
apply inv_hmap_CH2_m1.
simpl; tauto. simpl; tauto.
apply inv_hmap_CH2_m2.
apply inv_hmap_CH2_m2.
apply exd_Merge; simpl; tauto.
apply exd_Merge; simpl; tauto.
apply exd_Merge; simpl; tauto.
apply inv_hmap_CH2_m2.
apply exd_Merge; simpl; tauto.
apply exd_Merge; simpl; tauto.
apply exd_Merge; simpl; tauto.
apply inv_hmap_CH2_m2.
apply exd_Merge; simpl; tauto.
apply exd_Merge; simpl; tauto.
do 2 apply expe_Merge1 in h.
apply expe_I in h.
elimination h; [intuition|idtac]. apply expe_I in h.
elimination h; [intuition|idtac]. apply expe_I in h.
elimination h; [intuition|idtac]. apply expe_I in h.
elimination h; [intuition|idtac].
apply not_exd_not_expe with V x1 (max+1); try assumption.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
apply inv_hmap_CH2_m1.
simpl; tauto. simpl; tauto.
apply inv_hmap_CH2_m2.
apply inv_hmap_CH2_m2.
apply exd_Merge; simpl; tauto.
apply exd_Merge; simpl; tauto.
apply exd_Merge; simpl; tauto.
apply inv_hmap_CH2_m2.
apply exd_Merge; simpl; tauto.
apply exd_Merge; simpl; tauto.
apply exd_Merge; simpl; tauto.
apply inv_hmap_CH2_m2.
apply exd_Merge; simpl; tauto.
apply exd_Merge; simpl; tauto.
apply inv_hmap_CH2_m3.
do 2 apply exd_Merge; simpl; tauto.
do 2 apply exd_Merge; simpl; tauto.
do 2 apply exd_Merge; simpl; tauto.
intro h0. do 2 apply expe_Merge1 in h0.
apply expe_I in h0.
elimination h0; [intuition|idtac]. apply expe_I in h0.
elimination h0; [intuition|idtac]. apply expe_I in h0.
elimination h0; [intuition|idtac]. apply expe_I in h0.
elimination h0; [intuition|idtac].
apply not_exd_not_expe with V x1 (max+2); try assumption.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
unfold inv_hmap, prec_I; simpl; repeat split; tauto.
simpl; tauto.
apply inv_hmap_CH2_m1.
simpl; tauto. simpl; tauto.
apply inv_hmap_CH2_m2.
apply inv_hmap_CH2_m2.
apply exd_Merge; simpl; tauto.
apply exd_Merge; simpl; tauto.
apply exd_Merge; simpl; tauto.
apply inv_hmap_CH2_m2.
apply exd_Merge; simpl; tauto.
apply exd_Merge; simpl; tauto.
apply exd_Merge; simpl; tauto.
apply inv_hmap_CH2_m2.
apply exd_Merge; simpl; tauto.
apply exd_Merge; simpl; tauto.
Qed.

Lemma planar_CH2_m5 : planar m5.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
unfold m5. apply <- planarity_crit_Merge0. split.
apply planar_CH2_m4. right.
rewrite <- eq_cA_cA_1. rewrite cA_m4_one_x2.
apply expf_m4_max2_max1.
apply inv_hmap_CH2_m4. apply inv_gmap_CH2_m4.
apply not_expe_m4_x2_max1.
do 3 apply exd_Merge; simpl; tauto.
do 3 apply exd_Merge; simpl; tauto.
apply inv_hmap_CH2_m4.
Qed.

(* ================================ *)

Lemma Iter_cA_m5_one_i_x1 : forall (i:nat),
  Iter (MA1.MfcA.f m5) i x1 = x1 \/
  Iter (MA1.MfcA.f m5) i x1 = (max+1).
Proof.
induction i; simpl. left; tauto.
elimination IHi; rewrite IHi;
unfold MA1.MfcA.f, MA1.McAMd.f, Md1.kd.
right; apply cA_m5_one_x1.
left; apply cA_m5_one_max1.
Qed.

Lemma Iter_cA_m5_one_i_max1 : forall (i:nat),
  Iter (MA1.MfcA.f m5) i (max+1) = (max+1) \/
  Iter (MA1.MfcA.f m5) i (max+1) = x1.
Proof.
induction i; simpl. left; tauto.
elimination IHi; rewrite IHi;
unfold MA1.MfcA.f, MA1.McAMd.f, Md1.kd.
right; apply cA_m5_one_max1.
left; apply cA_m5_one_x1.
Qed.

Lemma not_expv_m5_x1_x2 : ~ expv m5 x1 x2.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
intro h. unfold expv in h.
unfold MA1.MfcA.expo in h.
destruct h as [h1 h2].
elim h2; clear h2. intros i hi.
generalize (Iter_cA_m5_one_i_x1 i).
intro h; elimination h; rewrite h in hi.
apply H1; assumption.
apply H9; apply eq_sym; assumption.
Qed.

Lemma not_expv_m5_x1_max2 : ~ expv m5 x1 (max+2).
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
intro h. unfold expv in h.
unfold MA1.MfcA.expo in h.
destruct h as [h1 h2].
elim h2; clear h2. intros i hi.
generalize (Iter_cA_m5_one_i_x1 i).
intro h; elimination h; rewrite h in hi.
apply H10; assumption.
apply H12; assumption.
Qed.

Lemma not_expv_m5_max1_x2 : ~ expv m5 (max+1) x2.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
intro h. unfold expv in h.
unfold MA1.MfcA.expo in h.
destruct h as [h1 h2].
elim h2; clear h2. intros i hi.
generalize (Iter_cA_m5_one_i_max1 i).
intro h; elimination h; rewrite h in hi.
apply H9; apply eq_sym; assumption.
apply H1; assumption.
Qed.

Lemma not_expv_m5_max1_max2 : ~ expv m5 (max+1) (max+2).
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
intro h. unfold expv in h.
unfold MA1.MfcA.expo in h.
destruct h as [h1 h2].
elim h2; clear h2. intros i hi.
generalize (Iter_cA_m5_one_i_max1 i).
intro h; elimination h; rewrite h in hi.
apply H12; assumption.
apply H10; assumption.
Qed.

(* ===== *)

Lemma Iter_cA_m5_zero_i_x1 : forall (i:nat),
  Iter (MA0.MfcA.f m5) i x1 = x1 \/
  Iter (MA0.MfcA.f m5) i x1 = (max+2).
Proof.
induction i; simpl. left; tauto.
elimination IHi; rewrite IHi;
unfold MA0.MfcA.f, MA0.McAMd.f, Md0.kd.
right; apply cA_m5_zero_x1.
left; apply cA_m5_zero_max2.
Qed.

Lemma Iter_cA_m5_zero_i_max2 : forall (i:nat),
  Iter (MA0.MfcA.f m5) i (max+2) = (max+2) \/
  Iter (MA0.MfcA.f m5) i (max+2) = x1.
Proof.
induction i; simpl. left; tauto.
elimination IHi; rewrite IHi;
unfold MA0.MfcA.f, MA0.McAMd.f, Md0.kd.
right; apply cA_m5_zero_max2.
left; apply cA_m5_zero_x1.
Qed.

Lemma not_expe_m5_x1_x2 : ~ expe m5 x1 x2.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
intro h. unfold expe in h.
unfold MA0.MfcA.expo in h.
destruct h as [h1 h2].
elim h2; clear h2. intros i hi.
generalize (Iter_cA_m5_zero_i_x1 i).
intro h; elimination h; rewrite h in hi.
apply H1; assumption.
apply H11; apply eq_sym; assumption.
Qed.

Lemma not_expe_m5_x1_max1 : ~ expe m5 x1 (max+1).
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
intro h. unfold expe in h.
unfold MA0.MfcA.expo in h.
destruct h as [h1 h2].
elim h2; clear h2. intros i hi.
generalize (Iter_cA_m5_zero_i_x1 i).
intro h; elimination h; rewrite h in hi.
apply H8; assumption.
apply H12; apply eq_sym; assumption.
Qed.

Lemma not_expe_m5_max2_x2 : ~ expe m5 (max+2) x2.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
intro h. unfold expe in h.
unfold MA0.MfcA.expo in h.
destruct h as [h1 h2].
elim h2; clear h2. intros i hi.
generalize (Iter_cA_m5_zero_i_max2 i).
intro h; elimination h; rewrite h in hi.
apply H11; apply eq_sym; assumption.
apply H1; assumption.
Qed.

Lemma not_expe_m5_max2_max1 : ~ expe m5 (max+2) (max+1).
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
intro h. unfold expe in h.
unfold MA0.MfcA.expo in h.
destruct h as [h1 h2].
elim h2; clear h2. intros i hi.
generalize (Iter_cA_m5_zero_i_max2 i).
intro h; elimination h; rewrite h in hi.
apply H12; apply eq_sym; assumption.
apply H8; assumption.
Qed.

(* ===== *)

Lemma is_well_emb_m5 : is_well_emb m5.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
unfold is_well_emb.
fold m1. fold m2. fold m3. fold m4. fold m5.
intros x y h1 h2 h3.
do 4 apply exd_Merge in h1.
do 4 apply exd_Merge in h2.
simpl in h1. simpl in h2. split; intro h.
elimination h1.
elimination h2.
rewrite <- h1 in h3. rewrite <- h2 in h3. tauto.
elimination h2.
assert False; [idtac|tauto].
rewrite <- h1 in h. rewrite <- h2 in h.
apply not_expv_m5_max1_max2.
apply expv_symm; try exact h.
apply inv_hmap_CH2_m5.
elimination h2.
rewrite <- h1; rewrite <- h2.
unfold m5, m4, m3, m2.
do 8 rewrite fpoint_Merge.
unfold m1; simpl; eqdartdec; tauto.
elimination h2; try tauto.
assert False; [idtac|tauto].
rewrite <- h1 in h. rewrite <- h2 in h.
apply not_expv_m5_x1_max2.
apply expv_symm; try exact h.
apply inv_hmap_CH2_m5.
elimination h1.
elimination h2.
assert False; [idtac|tauto].
rewrite <- h1 in h. rewrite <- h2 in h.
apply not_expv_m5_max1_max2; exact h.
elimination h2.
rewrite <- h1 in h3. rewrite <- h2 in h3. tauto.
elimination h2.
assert False; [idtac|tauto].
rewrite <- h1 in h. rewrite <- h2 in h.
apply not_expv_m5_max1_x2; exact h.
elimination h2; try tauto.
rewrite <- h1; rewrite <- h2.
unfold m5, m4, m3, m2.
do 8 rewrite fpoint_Merge.
unfold m1; simpl; eqdartdec; tauto.
elimination h1.
elimination h2.
rewrite <- h1; rewrite <- h2.
unfold m5, m4, m3, m2.
do 8 rewrite fpoint_Merge.
unfold m1; simpl; eqdartdec; tauto.
elimination h2.
assert False; [idtac|tauto].
rewrite <- h1 in h. rewrite <- h2 in h.
apply not_expv_m5_max1_x2.
apply expv_symm; try exact h.
apply inv_hmap_CH2_m5.
elimination h2.
rewrite <- h1 in h3. rewrite <- h2 in h3. tauto.
elimination h2; try tauto.
assert False; [idtac|tauto].
rewrite <- h1 in h. rewrite <- h2 in h.
apply not_expv_m5_x1_x2.
apply expv_symm; try exact h.
apply inv_hmap_CH2_m5.
elimination h1; try tauto.
elimination h2.
assert False; [idtac|tauto].
rewrite <- h1 in h. rewrite <- h2 in h.
apply not_expv_m5_x1_max2; exact h.
elimination h2.
rewrite <- h1; rewrite <- h2.
unfold m5, m4, m3, m2.
do 8 rewrite fpoint_Merge.
unfold m1; simpl; eqdartdec; tauto.
elimination h2.
assert False; [idtac|tauto].
rewrite <- h1 in h. rewrite <- h2 in h.
apply not_expv_m5_x1_x2; exact h.
elimination h2; try tauto.
rewrite <- h1 in h3. rewrite <- h2 in h3. tauto.
(**)
elimination h1.
elimination h2.
rewrite <- h1 in h3. rewrite <- h2 in h3. tauto.
elimination h2.
assert False; [idtac|tauto].
rewrite <- h1 in h. rewrite <- h2 in h.
apply not_expe_m5_max2_max1; exact h.
elimination h2.
assert False; [idtac|tauto].
rewrite <- h1 in h. rewrite <- h2 in h.
apply not_expe_m5_max2_x2; exact h.
elimination h2; try tauto.
rewrite <- h1; rewrite <- h2.
unfold m5, m4, m3, m2.
do 8 rewrite fpoint_Merge.
unfold m1; simpl; eqdartdec.
apply not_eq_sym; exact Hp.
elimination h1.
elimination h2.
assert False; [idtac|tauto].
rewrite <- h1 in h. rewrite <- h2 in h.
apply not_expe_m5_max2_max1.
apply expe_symm; try exact h.
apply inv_hmap_CH2_m5.
elimination h2.
rewrite <- h1 in h3. rewrite <- h2 in h3. tauto.
elimination h2.
rewrite <- h1; rewrite <- h2.
unfold m5, m4, m3, m2.
do 8 rewrite fpoint_Merge.
unfold m1; simpl; eqdartdec; exact Hp.
elimination h2; try tauto.
assert False; [idtac|tauto].
rewrite <- h1 in h. rewrite <- h2 in h.
apply not_expe_m5_x1_max1.
apply expe_symm; try exact h.
apply inv_hmap_CH2_m5.
elimination h1.
elimination h2.
assert False; [idtac|tauto].
rewrite <- h1 in h. rewrite <- h2 in h.
apply not_expe_m5_max2_x2.
apply expe_symm; try exact h.
apply inv_hmap_CH2_m5.
elimination h2.
rewrite <- h1; rewrite <- h2.
unfold m5, m4, m3, m2.
do 8 rewrite fpoint_Merge.
unfold m1; simpl; eqdartdec.
apply not_eq_sym; exact Hp.
elimination h2.
rewrite <- h1 in h3. rewrite <- h2 in h3. tauto.
elimination h2; try tauto.
assert False; [idtac|tauto].
rewrite <- h1 in h. rewrite <- h2 in h.
apply not_expe_m5_x1_x2.
apply expe_symm; try exact h.
apply inv_hmap_CH2_m5.
elimination h1; try tauto.
elimination h2.
rewrite <- h1; rewrite <- h2.
unfold m5, m4, m3, m2.
do 8 rewrite fpoint_Merge.
unfold m1; simpl; eqdartdec; exact Hp.
elimination h2.
assert False; [idtac|tauto].
rewrite <- h1 in h. rewrite <- h2 in h.
apply not_expe_m5_x1_max1; exact h.
elimination h2.
assert False; [idtac|tauto].
rewrite <- h1 in h. rewrite <- h2 in h.
apply not_expe_m5_x1_x2; exact h.
elimination h2; try tauto.
rewrite <- h1 in h3. rewrite <- h2 in h3. tauto.
Qed.

(* ================================ *)

Lemma is_neq_point_m5 : is_neq_point m5.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
unfold is_neq_point.
fold m1. fold m2. fold m3. fold m4. fold m5.
intros x y h1 h2 h3.
do 4 apply exd_Merge in h1.
do 4 apply exd_Merge in h2.
simpl in h1. simpl in h2.
elimination h1.
elimination h2.
assert False; [idtac|tauto].
apply h3; rewrite <- h1; rewrite <- h2.
apply expv_refl. apply inv_hmap_CH2_m5.
do 4 apply exd_Merge; simpl; tauto.
elimination h2.
rewrite <- h1, <- h2.
unfold m5, m4, m3, m2.
do 8 rewrite fpoint_Merge.
unfold m1; simpl; eqdartdec.
apply not_eq_sym; exact Hp.
elimination h2.
assert False; [idtac|tauto].
apply h3; rewrite <- h1; rewrite <- h2.
unfold expv; split.
do 4 apply exd_Merge; simpl; tauto.
exists 1; simpl.
unfold MA1.MfcA.f, MA1.McAMd.f, Md1.kd.
apply cA_m5_one_max2.
elimination h2; try tauto.
rewrite <- h1, <- h2.
unfold m5, m4, m3, m2.
do 8 rewrite fpoint_Merge.
unfold m1; simpl; eqdartdec.
apply not_eq_sym; exact Hp.
elimination h1.
elimination h2.
rewrite <- h1, <- h2.
unfold m5, m4, m3, m2.
do 8 rewrite fpoint_Merge.
unfold m1; simpl; eqdartdec; exact Hp.
elimination h2.
assert False; [idtac|tauto].
apply h3; rewrite <- h1; rewrite <- h2.
apply expv_refl. apply inv_hmap_CH2_m5.
do 4 apply exd_Merge; simpl; tauto.
elimination h2.
rewrite <- h1, <- h2.
unfold m5, m4, m3, m2.
do 8 rewrite fpoint_Merge.
unfold m1; simpl; eqdartdec; exact Hp.
elimination h2; try tauto.
assert False; [idtac|tauto].
apply h3; rewrite <- h1; rewrite <- h2.
unfold expv; split.
do 4 apply exd_Merge; simpl; tauto.
exists 1; simpl.
unfold MA1.MfcA.f, MA1.McAMd.f, Md1.kd.
apply cA_m5_one_max1.
elimination h1.
elimination h2.
assert False; [idtac|tauto].
apply h3; rewrite <- h1; rewrite <- h2.
unfold expv; split.
do 4 apply exd_Merge; simpl; tauto.
exists 1; simpl.
unfold MA1.MfcA.f, MA1.McAMd.f, Md1.kd.
apply cA_m5_one_x2.
elimination h2.
rewrite <- h1, <- h2.
unfold m5, m4, m3, m2.
do 8 rewrite fpoint_Merge.
unfold m1; simpl; eqdartdec.
apply not_eq_sym; exact Hp.
elimination h2.
assert False; [idtac|tauto].
apply h3; rewrite <- h1; rewrite <- h2.
apply expv_refl. apply inv_hmap_CH2_m5.
do 4 apply exd_Merge; simpl; tauto.
elimination h2; try tauto.
rewrite <- h1, <- h2.
unfold m5, m4, m3, m2.
do 8 rewrite fpoint_Merge.
unfold m1; simpl; eqdartdec.
apply not_eq_sym; exact Hp.
elimination h1; try tauto.
elimination h2.
rewrite <- h1, <- h2.
unfold m5, m4, m3, m2.
do 8 rewrite fpoint_Merge.
unfold m1; simpl; eqdartdec; exact Hp.
elimination h2.
assert False; [idtac|tauto].
apply h3; rewrite <- h1; rewrite <- h2.
unfold expv; split.
do 4 apply exd_Merge; simpl; tauto.
exists 1; simpl.
unfold MA1.MfcA.f, MA1.McAMd.f, Md1.kd.
apply cA_m5_one_x1.
elimination h2.
rewrite <- h1, <- h2.
unfold m5, m4, m3, m2.
do 8 rewrite fpoint_Merge.
unfold m1; simpl; eqdartdec; exact Hp.
elimination h2; try tauto.
assert False; [idtac|tauto].
apply h3; rewrite <- h1; rewrite <- h2.
apply expv_refl. apply inv_hmap_CH2_m5.
do 4 apply exd_Merge; simpl; tauto.
Qed.

(* ================================ *)

Lemma is_noalign_m5 : is_noalign m5.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
unfold is_noalign.
fold m1. fold m2. fold m3. fold m4. fold m5.
intros x y z h1 h2 h3 h4 h5 h6 h7; clear h7.
generalize h4 h5 h6; clear h4 h5 h6.
unfold m5, m4, m3, m2.
do 12 rewrite fpoint_Merge.
do 4 apply exd_Merge in h1.
do 4 apply exd_Merge in h2.
do 4 apply exd_Merge in h3.
simpl in h1; simpl in h2; simpl in h3.
elimination h1.
elimination h2.
rewrite <- h1, <- h2.
unfold m1; simpl; eqdartdec; tauto.
elimination h2.
elimination h3.
rewrite <- h1, <- h3.
unfold m1; simpl; eqdartdec; tauto.
elimination h3.
rewrite <- h2, <- h3.
unfold m1; simpl; eqdartdec; tauto.
elimination h3.
rewrite <- h1, <- h3.
unfold m1; simpl; eqdartdec; tauto.
elimination h3; try tauto.
rewrite <- h2, <- h3.
unfold m1; simpl; eqdartdec; tauto.
elimination h2.
rewrite <- h1, <- h2.
unfold m1; simpl; eqdartdec; tauto.
elimination h2; try tauto.
elimination h3.
rewrite <- h1, <- h3.
unfold m1; simpl; eqdartdec; tauto.
elimination h3.
rewrite <- h2, <- h3.
unfold m1; simpl; eqdartdec; tauto.
elimination h3.
rewrite <- h1, <- h3.
unfold m1; simpl; eqdartdec; tauto.
elimination h3; try tauto.
rewrite <- h2, <- h3.
unfold m1; simpl; eqdartdec; tauto.
elimination h1.
elimination h2.
elimination h3.
rewrite <- h2, <- h3.
unfold m1; simpl; eqdartdec; tauto.
elimination h3.
rewrite <- h1, <- h3.
unfold m1; simpl; eqdartdec; tauto.
elimination h3.
rewrite <- h2, <- h3.
unfold m1; simpl; eqdartdec; tauto.
elimination h3; try tauto.
rewrite <- h1, <- h3.
unfold m1; simpl; eqdartdec; tauto.
elimination h2.
rewrite <- h1, <- h2.
unfold m1; simpl; eqdartdec; tauto.
elimination h2.
elimination h3.
rewrite <- h2, <- h3.
unfold m1; simpl; eqdartdec; tauto.
elimination h3.
rewrite <- h1, <- h3.
unfold m1; simpl; eqdartdec; tauto.
elimination h3.
rewrite <- h2, <- h3.
unfold m1; simpl; eqdartdec; tauto.
elimination h3; try tauto.
rewrite <- h1, <- h3.
unfold m1; simpl; eqdartdec; tauto.
elimination h2; try tauto.
rewrite <- h1, <- h2.
unfold m1; simpl; eqdartdec; tauto.
elimination h1.
elimination h2.
rewrite <- h1, <- h2.
unfold m1; simpl; eqdartdec; tauto.
elimination h2.
elimination h3.
rewrite <- h1, <- h3.
unfold m1; simpl; eqdartdec; tauto.
elimination h3.
rewrite <- h2, <- h3.
unfold m1; simpl; eqdartdec; tauto.
elimination h3.
rewrite <- h1, <- h3.
unfold m1; simpl; eqdartdec; tauto.
elimination h3; try tauto.
rewrite <- h2, <- h3.
unfold m1; simpl; eqdartdec; tauto.
elimination h2.
rewrite <- h1, <- h2.
unfold m1; simpl; eqdartdec; tauto.
elimination h2; try tauto.
elimination h3.
rewrite <- h1, <- h3.
unfold m1; simpl; eqdartdec; tauto.
elimination h3.
rewrite <- h2, <- h3.
unfold m1; simpl; eqdartdec; tauto.
elimination h3.
rewrite <- h1, <- h3.
unfold m1; simpl; eqdartdec; tauto.
elimination h3; try tauto.
rewrite <- h2, <- h3.
unfold m1; simpl; eqdartdec; tauto.
elimination h1; try tauto.
elimination h2.
elimination h3.
rewrite <- h2, <- h3.
unfold m1; simpl; eqdartdec; tauto.
elimination h3.
rewrite <- h1, <- h3.
unfold m1; simpl; eqdartdec; tauto.
elimination h3.
rewrite <- h2, <- h3.
unfold m1; simpl; eqdartdec; tauto.
elimination h3; try tauto.
rewrite <- h1, <- h3.
unfold m1; simpl; eqdartdec; tauto.
elimination h2.
rewrite <- h1, <- h2.
unfold m1; simpl; eqdartdec; tauto.
elimination h2.
elimination h3.
rewrite <- h2, <- h3.
unfold m1; simpl; eqdartdec; tauto.
elimination h3.
rewrite <- h1, <- h3.
unfold m1; simpl; eqdartdec; tauto.
elimination h3.
rewrite <- h2, <- h3.
unfold m1; simpl; eqdartdec; tauto.
elimination h3; try tauto.
rewrite <- h1, <- h3.
unfold m1; simpl; eqdartdec; tauto.
elimination h2; try tauto.
rewrite <- h1, <- h2.
unfold m1; simpl; eqdartdec; tauto.
Qed.

(* ================================ *)

Lemma Iter_cF_m5_i_x1 : forall (i:nat),
  Iter (cF m5) i x1 = x1 \/ Iter (cF m5) i x1 = x2.
Proof.
intro i; induction i. simpl; left; trivial.
assert (t3: inv_hmap m5). apply inv_hmap_CH2_m5.
assert (t4: inv_gmap m5). apply inv_gmap_CH2_m5.
elimination IHi; simpl; rewrite IHi; clear IHi.
right; unfold cF.
rewrite <- eq_cA_cA_1; try assumption.
rewrite <- eq_cA_cA_1; try assumption.
rewrite cA_m5_zero_x1; apply cA_m5_one_max2.
left; unfold cF.
rewrite <- eq_cA_cA_1; try assumption.
rewrite <- eq_cA_cA_1; try assumption.
rewrite cA_m5_zero_x2; apply cA_m5_one_max1.
Qed.

Lemma expf_m5_x1_x1_x2 :
  forall (da:dart), expf m5 x1 da ->
  da = x1 \/ da = x2.
Proof.
intro da; unfold expf, MF.expo.
intros [h1 [h2 h3]].
elim h3; clear h3; intros i hi.
unfold MF.f, McF.f in hi.
rewrite <- hi; apply Iter_cF_m5_i_x1.
Qed.

(* ===== *)

Lemma is_convex_m5 : is_convex m5 x1.
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
unfold is_convex. intros x y h1 h2 h3 h4.
assert False; [idtac|tauto].
apply expf_m5_x1_x1_x2 in h1.
elimination h1.
subst x; rewrite cA_m5_zero_x1 in *.
unfold m5, m4, m3, m2 in h2.
do 4 apply exd_Merge in h2.
unfold m1 in h2; simpl in h2.
elimination h2.
subst y; apply h4; tauto.
elimination h2.
subst y; apply h3.
unfold m5, m4, m3, m2; do 8 rewrite fpoint_Merge.
unfold m1; simpl; eqdartdec; tauto.
elimination h2.
subst y; apply h4.
unfold m5, m4, m3, m2; do 8 rewrite fpoint_Merge.
unfold m1; simpl; eqdartdec; tauto.
elimination h2; try tauto.
subst y; apply h3; tauto.
subst x; rewrite cA_m5_zero_x2 in *.
unfold m5, m4, m3, m2 in h2.
do 4 apply exd_Merge in h2.
unfold m1 in h2; simpl in h2.
elimination h2.
subst y; apply h3.
unfold m5, m4, m3, m2; do 8 rewrite fpoint_Merge.
unfold m1; simpl; eqdartdec; tauto.
elimination h2.
subst y; apply h4; tauto.
elimination h2.
subst y; apply h3; tauto.
elimination h2; try tauto.
subst y; apply h4.
unfold m5, m4, m3, m2; do 8 rewrite fpoint_Merge.
unfold m1; simpl; eqdartdec; tauto.
Qed.

(* ================================ *)

Lemma not_expf_m5_x1_cA_m5_zero_x1 : ~ expf m5 x1 (cA m5 zero x1).
Proof.
assert (H6 : max+1 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H7 : max+2 <> nil).
 apply sym_not_eq; apply lt_O_neq.
 apply lt_trans with max; [idtac|lia].
 apply lt_le_trans with x1; [idtac|assumption].
 apply neq_O_lt; apply sym_not_eq; assumption.
assert (H8 : x1 <> max+1); [lia|idtac].
assert (H9 : x2 <> max+1); [lia|idtac].
assert (H10 : x1 <> max+2); [lia|idtac].
assert (H11 : x2 <> max+2); [lia|idtac].
assert (H12 : max+1 <> max+2); [lia|idtac].
intro h; rewrite cA_m5_zero_x1 in h.
apply expf_m5_x1_x1_x2 in h. elimination h.
apply H10; rewrite h; tauto.
apply H11; rewrite h; tauto.
Qed.

End CH2_sec.

(* ================================ *)
(* ========== ########## ========== *)
(* ================================ *)

Lemma inv_hmap_CH2 :
  forall (x1:dart)(t1:tag)(p1:point)(x2:dart)(t2:tag)(p2:point)(max:dart),
  x1 <> x2 -> x1 <> nil -> x2 <> nil -> x1 <= max -> x2 <= max -> p1 <> p2 ->
  inv_hmap (fst (CH2 x1 t1 p1 x2 t2 p2 max)).
Proof.
intros x1 t1 p1 x2 t2 p2 max; intros h1 h2 h3 h4 h5 h6.
simpl fst; apply inv_hmap_CH2_m5; assumption.
Qed.

Lemma inv_gmap_CH2 :
  forall (x1:dart)(t1:tag)(p1:point)(x2:dart)(t2:tag)(p2:point)(max:dart),
  x1 <> x2 -> x1 <> nil -> x2 <> nil -> x1 <= max -> x2 <= max -> p1 <> p2 ->
  inv_gmap (fst (CH2 x1 t1 p1 x2 t2 p2 max)).
Proof.
intros x1 t1 p1 x2 t2 p2 max; intros h1 h2 h3 h4 h5 h6.
simpl fst; apply inv_gmap_CH2_m5; assumption.
Qed.

Lemma inv_poly_CH2 :
  forall (x1:dart)(t1:tag)(p1:point)(x2:dart)(t2:tag)(p2:point)(max:dart),
  x1 <> x2 -> x1 <> nil -> x2 <> nil -> x1 <= max -> x2 <= max -> p1 <> p2 ->
  inv_poly (fst (CH2 x1 t1 p1 x2 t2 p2 max)) (snd (CH2 x1 t1 p1 x2 t2 p2 max)).
Proof.
intros x1 t1 p1 x2 t2 p2 max; intros h1 h2 h3 h4 h5 h6.
simpl fst; simpl snd; apply inv_poly_m5; assumption.
Qed.

Lemma planar_CH2 :
  forall (x1:dart)(t1:tag)(p1:point)(x2:dart)(t2:tag)(p2:point)(max:dart),
  x1 <> x2 -> x1 <> nil -> x2 <> nil -> x1 <= max -> x2 <= max -> p1 <> p2 ->
  planar (fst (CH2 x1 t1 p1 x2 t2 p2 max)).
Proof.
intros x1 t1 p1 x2 t2 p2 max; intros h1 h2 h3 h4 h5 h6.
simpl fst; apply planar_CH2_m5; assumption.
Qed.

Lemma is_well_emb_CH2 :
  forall (x1:dart)(t1:tag)(p1:point)(x2:dart)(t2:tag)(p2:point)(max:dart),
  x1 <> x2 -> x1 <> nil -> x2 <> nil -> x1 <= max -> x2 <= max -> p1 <> p2 ->
  is_well_emb (fst (CH2 x1 t1 p1 x2 t2 p2 max)).
Proof.
intros x1 t1 p1 x2 t2 p2 max; intros h1 h2 h3 h4 h5 h6.
simpl fst; apply is_well_emb_m5; assumption.
Qed.

Lemma is_neq_point_CH2 :
  forall (x1:dart)(t1:tag)(p1:point)(x2:dart)(t2:tag)(p2:point)(max:dart),
  x1 <> x2 -> x1 <> nil -> x2 <> nil -> x1 <= max -> x2 <= max -> p1 <> p2 ->
  is_neq_point (fst (CH2 x1 t1 p1 x2 t2 p2 max)).
Proof.
intros x1 t1 p1 x2 t2 p2 max; intros h1 h2 h3 h4 h5 h6.
simpl fst; apply is_neq_point_m5; assumption.
Qed.

Lemma is_noalign_CH2 :
  forall (x1:dart)(t1:tag)(p1:point)(x2:dart)(t2:tag)(p2:point)(max:dart),
  x1 <> x2 -> x1 <> nil -> x2 <> nil -> x1 <= max -> x2 <= max -> p1 <> p2 ->
  is_noalign (fst (CH2 x1 t1 p1 x2 t2 p2 max)).
Proof.
intros x1 t1 p1 x2 t2 p2 max; intros h1 h2 h3 h4 h5 h6.
simpl fst; apply is_noalign_m5; assumption.
Qed.

Lemma is_convex_CH2 :
  forall (x1:dart)(t1:tag)(p1:point)(x2:dart)(t2:tag)(p2:point)(max:dart),
  x1 <> x2 -> x1 <> nil -> x2 <> nil -> x1 <= max -> x2 <= max -> p1 <> p2 ->
  is_convex (fst (CH2 x1 t1 p1 x2 t2 p2 max)) (snd (CH2 x1 t1 p1 x2 t2 p2 max)).
Proof.
intros x1 t1 p1 x2 t2 p2 max; intros h1 h2 h3 h4 h5 h6.
simpl fst; simpl snd; apply is_convex_m5; assumption.
Qed.

(* ===== *)

Lemma not_expf_m5_da_cA_m5_zero_da :
  forall (x1:dart)(t1:tag)(p1:point)(x2:dart)(t2:tag)(p2:point)(max:dart),
  x1 <> x2 -> x1 <> nil -> x2 <> nil -> x1 <= max -> x2 <= max -> p1 <> p2 ->
  ~ expf (fst (CH2 x1 t1 p1 x2 t2 p2 max)) (snd (CH2 x1 t1 p1 x2 t2 p2 max))
  (cA (fst (CH2 x1 t1 p1 x2 t2 p2 max)) zero (snd (CH2 x1 t1 p1 x2 t2 p2 max))).
Proof.
intros x1 t1 p1 x2 t2 p2 max; intros h1 h2 h3 h4 h5 h6.
simpl fst; simpl snd; apply not_expf_m5_x1_cA_m5_zero_x1; assumption.
Qed.

(* ================================ *)
(* ========== ########## ========== *)
(* ================================ *)

Lemma max_dart_not_exd : forall (m:fmap)(d:dart),
  max_dart m < d -> ~ exd m d.
Proof.
intros m d; induction m.
simpl; tauto. simpl.
elim le_lt_dec; intros h1 h2.
intro h; elimination h.
subst d0; lia.
apply IHm; assumption.
intro h; elimination h.
subst d0; lia.
apply IHm; try assumption.
lia. simpl; assumption.
Qed.

Lemma exd_fst_snd_CH2 :
  forall (x1:dart)(t1:tag)(p1:point)(x2:dart)(t2:tag)(p2:point)(max:dart),
  exd (fst (CH2 x1 t1 p1 x2 t2 p2 max)) (snd (CH2 x1 t1 p1 x2 t2 p2 max)).
Proof.
intros x1 t1 p1 x2 t2 p2 max; simpl fst; simpl snd.
do 4 apply exd_Merge. simpl. do 3 right. left. trivial.
Qed.

(* ================================ *)

Definition prec_CH (m:fmap) : Prop := 
  inv_hmap m /\ linkless m /\ is_neq_point m /\ is_noalign m.

Lemma inv_hmap_inv_poly_planar_well_emb_convex_CH :
  forall (m:fmap), prec_CH m ->
  inv_hmap (fst (CH m)) /\ inv_gmap (fst (CH m)) /\ inv_poly (fst (CH m)) (snd (CH m))
  /\ planar (fst (CH m)) /\ is_well_emb (fst (CH m)) /\ is_neq_point (fst (CH m)) /\
  is_noalign (fst (CH m)) /\ is_convex (fst (CH m)) (snd (CH m)).
Proof.
induction m.
 (* Case 1 : m = V *)
 intros [Hmap [Hless [Hemb Halign]]].
 simpl in *; intuition.
 unfold inv_gmap; simpl; intuition.
 unfold inv_poly; simpl; intuition.
 apply plf_planar; simpl; trivial.
 unfold is_well_emb; simpl; intuition.
 unfold is_convex; simpl; intuition.
 clear IHm.
 (* Case 2 : m = I *)
 induction m.
  (* Case 2.1 : m = I V *)
  intros [Hmap [Hless [Hemb Halign]]].
  simpl in *; unfold prec_I in *; simpl in *.
  destruct Hmap as [Hmap [H1 H2]].
  split; [idtac|split; [idtac|split]].
  repeat split; try assumption.
  unfold inv_gmap; intros k x; simpl.
  intro h; elim h; clear h; try tauto.
  intro h; subst x; eqdartdec; trivial.
  unfold inv_poly; intros k x; simpl.
  intro h; elim h; clear h; try tauto.
  intros [h1 h2]; subst d; tauto.
  split; [idtac|split; idtac].
  apply plf_planar; simpl; try trivial.
  unfold prec_I; simpl; repeat split; trivial.
  unfold is_well_emb; intros x y; simpl.
  intro h1; elim h1; clear h1; intro h1; try tauto.
  intro h2; elim h2; clear h2; intro h2; try tauto.
  intro h3; subst x; subst y; tauto.
  split; [idtac|split; idtac].
  unfold is_neq_point. intros x y.
  simpl. intros h1 h2.
  elimination h1; try tauto. subst x.
  elimination h2; try tauto. subst y.
  eqdartdec. unfold expv, MA1.MfcA.expo.
  intros h1 h2. apply h1. clear h1.
  split. simpl; tauto.
  exists 0. simpl. trivial.
  unfold is_noalign. intros x y z.
  simpl. intros h1 h2 h3.
  elimination h1; try tauto. subst x.
  elimination h2; try tauto. subst y.
  elimination h3; try tauto.
  unfold is_convex; intros x y; simpl in *.
  intros h1 h; unfold expf, MF.expo in h1.
  destruct h1 as [h1 [h2 h3]].
  simpl in *; elim h2; tauto. 
  clear IHm.
  (* Case 2.2 : m = I I *)
  intros [Hmap [Hless [Hnpt Halign]]]. simpl in *.
  destruct Hmap as [[Hmap [H1 H2]] [H3 H0]].
  assert (H4: ~ exd m d).
   intro h; apply H0; simpl; right; exact h.
  assert (H5: d0 <> d).
   intro h; apply H0; simpl; left; exact h.
(**)
assert (Hp1 : p0 <> p).
generalize (Hnpt d0 d); simpl; eqdartdec.
intro h; apply h; clear h; try tauto.
apply not_expv_I; try assumption.
simpl; unfold prec_I; tauto.
apply not_expv_I; try assumption.
apply not_exd_not_expv; assumption.
(**)
assert (Hp2 : forall (da:dart), exd m da -> p <> fpoint m da).
intros da hda.
assert (t1: d <> da). intro h; rewrite h in H4; contradiction.
assert (t2: d0 <> da). intro h; rewrite h in H2; contradiction.
generalize (Hnpt d da); simpl; eqdartdec.
intro h; apply h; clear h; try tauto.
apply not_expv_I; try assumption.
simpl; unfold prec_I; tauto.
apply not_expv_I; try assumption.
apply not_exd_not_expv; assumption.
(**)
assert (Hp3 : forall (da:dart), exd m da -> p0 <> fpoint m da).
intros da hda.
assert (t1: d <> da). intro h; rewrite h in H4; contradiction.
assert (t2: d0 <> da). intro h; rewrite h in H2; contradiction.
generalize (Hnpt d0 da); simpl; eqdartdec.
intro h; apply h; clear h; try tauto.
apply not_expv_I; try assumption.
simpl; unfold prec_I; tauto.
apply not_expv_I; try assumption.
apply not_exd_not_expv; assumption.
(**)
assert (Hp4 : forall (da:dart)(db:dart), exd m da -> exd m db -> ~ expv m da db -> fpoint m da <> fpoint m db).
intros da db hda hdb hc.
assert (t1: d <> da). intro h; rewrite h in H4; contradiction.
assert (t2: d0 <> da). intro h; rewrite h in H2; contradiction.
assert (t3: d <> db). intro h; rewrite h in H4; contradiction.
assert (t4: d0 <> db). intro h; rewrite h in H2; contradiction.
generalize (Hnpt da db); simpl; eqdartdec.
intro h; apply h; clear h; try tauto.
apply not_expv_I; try assumption.
simpl; unfold prec_I; tauto.
intro h; rewrite h in hc; apply hc.
apply expv_refl; assumption.
apply not_expv_I; try assumption.
intro h; rewrite h in hc; apply hc.
apply expv_refl; assumption.
(**)
assert (Ha0 : is_noalign m).
intros da db dc h1 h2 h3 h4 h5 h6.
assert (t1: d <> da). intro h; rewrite h in H4; contradiction.
assert (t2: d0 <> da). intro h; rewrite h in H2; contradiction.
assert (t3: d <> db). intro h; rewrite h in H4; contradiction.
assert (t4: d0 <> db). intro h; rewrite h in H2; contradiction.
assert (t5: d <> dc). intro h; rewrite h in H4; contradiction.
assert (t6: d0 <> dc). intro h; rewrite h in H2; contradiction.
generalize (Halign da db dc); simpl; eqdartdec.
intro h; apply h; clear h; try tauto.
(**)
clear H0 Hnpt.
(**)
elim (le_lt_dec d0 (max_dart m)).
 elim (le_lt_dec d (max_dart m)).
  (* 1 / 4 *)
  intros Hmax1 Hmax2.
  apply inv_hmap_inv_gmap_inv_poly_planar_well_emb_convex_CHI; try assumption.
apply exd_fst_snd_CH2.
apply inv_hmap_CH2; assumption.
apply inv_gmap_CH2; assumption.
apply inv_poly_CH2; assumption.
apply planar_CH2; assumption.
apply is_well_emb_CH2; assumption.
apply is_neq_point_CH2; assumption.
apply is_noalign_CH2; assumption.
apply is_convex_CH2; assumption.
apply not_expf_m5_da_cA_m5_zero_da; assumption.
(* Hw0 *)
intros da Hda.
apply not_eq_sym.
apply lt_0_neq.
lia.
(* Hw1 *)
intros da Hda; simpl fst.
do 4 rewrite <- exd_Merge.
simpl. intro h.
elimination h.
apply max_dart_not_exd with m da.
lia. assumption.
elimination h.
apply max_dart_not_exd with m da.
lia. assumption.
elimination h.
subst da; apply H4; assumption.
elimination h.
subst da; apply H2; assumption.
assumption.
(* Hw5 *)
intros da Hda; split; simpl fst.
apply max_dart_not_exd.
lia.
do 4 rewrite <- exd_Merge.
simpl. intro h.
elimination h.
subst da; lia.
elimination h.
subst da; lia.
elimination h.
subst da; lia.
elimination h.
subst da; lia.
assumption.
(* Hp1 *)
intros da db Hda; simpl fst.
do 4 rewrite <- exd_Merge.
do 4 rewrite fpoint_Merge.
simpl. intro Hdb.
elimination Hdb.
subst db. eqdartdec.
apply not_eq_sym; apply Hp2; assumption.
elimination Hdb.
subst db. eqdartdec.
elim eq_dart_dec; intro h0.
assert False; [lia|tauto].
apply not_eq_sym; apply Hp3; assumption.
elimination Hdb.
subst db. eqdartdec.
elim eq_dart_dec; intro t1.
apply not_eq_sym; apply Hp2; assumption.
elim eq_dart_dec; intro t2.
apply not_eq_sym; apply Hp3; assumption.
apply not_eq_sym; apply Hp2; assumption.
elimination Hdb.
subst db. eqdartdec.
elim eq_dart_dec; intro t1.
apply not_eq_sym; apply Hp2; assumption.
elim eq_dart_dec; intro t2.
apply not_eq_sym; apply Hp3; assumption.
apply not_eq_sym; apply Hp3; assumption.
tauto.
(* Hp2 *)
intros da db dc Hda Hdb Hdc Hp0.
assert (t1: da <> d).
intro h; apply H4; rewrite <- h; assumption.
assert (t2: da <> d0).
intro h; apply H2; rewrite <- h; assumption.
assert (t3: db <> d).
intro h; apply H4; rewrite <- h; assumption.
assert (t4: db <> d0).
intro h; apply H2; rewrite <- h; assumption.
simpl fst in Hdc.
do 4 rewrite <- exd_Merge in Hdc.
simpl in Hdc.
elimination Hdc.
subst dc.
simpl fst.
do 4 rewrite fpoint_Merge.
simpl fpoint. eqdartdec.
generalize (Halign da db d).
simpl. eqdartdec.
intro h; apply h.
do 2 right; assumption.
do 2 right; assumption.
left; trivial. assumption.
apply not_eq_sym; apply Hp2; assumption.
apply not_eq_sym; apply Hp2; assumption.
elimination Hdc.
subst dc.
simpl fst.
do 4 rewrite fpoint_Merge.
simpl fpoint. eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
generalize (Halign da db d0).
simpl. eqdartdec.
intro h; apply h.
do 2 right; assumption.
do 2 right; assumption.
right; left; trivial. assumption.
apply not_eq_sym; apply Hp3; assumption.
apply not_eq_sym; apply Hp3; assumption.
elimination Hdc.
subst dc.
simpl fst.
do 4 rewrite fpoint_Merge.
simpl fpoint. eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
generalize (Halign da db d).
simpl. eqdartdec.
intro h; apply h.
do 2 right; assumption.
do 2 right; assumption.
left; trivial. assumption.
apply not_eq_sym; apply Hp2; assumption.
apply not_eq_sym; apply Hp2; assumption.
elimination Hdc.
subst dc.
simpl fst.
do 4 rewrite fpoint_Merge.
simpl fpoint. eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
generalize (Halign da db d0).
simpl. eqdartdec.
intro h; apply h.
do 2 right; assumption.
do 2 right; assumption.
right; left; trivial. assumption.
apply not_eq_sym; apply Hp3; assumption.
apply not_eq_sym; apply Hp3; assumption.
tauto.
(* Hp3 *)
intros da db dc Hda Hdb Hdc Hp0.
assert (t1: da <> d).
intro h; apply H4; rewrite <- h; assumption.
assert (t2: da <> d0).
intro h; apply H2; rewrite <- h; assumption.
simpl fst in Hdb, Hdc, Hp0.
do 4 rewrite <- exd_Merge in Hdb.
do 4 rewrite <- exd_Merge in Hdc.
do 8 rewrite fpoint_Merge in Hp0.
simpl in Hdb, Hdc, Hp0.
generalize Hp0; clear Hp0.
elimination Hdb.
subst db.
elimination Hdc.
subst dc.
eqdartdec. tauto.
elimination Hdc.
subst dc.
simpl fst.
do 8 rewrite fpoint_Merge.
simpl fpoint. eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
generalize (Halign da d d0).
simpl. eqdartdec.
intro h; apply h.
do 2 right; assumption.
left; trivial.
right; left; trivial.
apply not_eq_sym; apply Hp2; assumption.
apply not_eq_sym; apply Hp3; assumption.
elimination Hdc.
subst dc.
eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
tauto.
elimination Hdc.
subst dc.
simpl fst.
do 8 rewrite fpoint_Merge.
simpl fpoint. eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
generalize (Halign da d d0).
simpl. eqdartdec.
intro h; apply h.
do 2 right; assumption.
left; trivial.
right; left; trivial.
apply not_eq_sym; apply Hp2; assumption.
apply not_eq_sym; apply Hp3; assumption.
tauto.
elimination Hdb.
subst db.
elimination Hdc.
subst dc.
simpl fst.
do 8 rewrite fpoint_Merge.
simpl fpoint.
eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
generalize (Halign da d0 d).
simpl. eqdartdec.
intro h; apply h.
do 2 right; assumption.
right; left; trivial.
left; trivial.
apply not_eq_sym; apply Hp3; assumption.
apply not_eq_sym; apply Hp2; assumption.
elimination Hdc.
subst dc.
eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
tauto.
elimination Hdc.
subst dc.
simpl fst.
do 8 rewrite fpoint_Merge.
simpl fpoint.
eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
elim eq_dart_dec; intro h3.
assert False; [lia|tauto].
generalize (Halign da d0 d).
simpl. eqdartdec.
intro h; apply h.
do 2 right; assumption.
right; left; trivial.
left; trivial.
apply not_eq_sym; apply Hp3; assumption.
apply not_eq_sym; apply Hp2; assumption.
elimination Hdc.
subst dc.
eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
elim eq_dart_dec; intro h3.
assert False; [lia|tauto].
tauto.
tauto.
elimination Hdb.
subst db.
elimination Hdc.
subst dc.
eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
tauto.
elimination Hdc.
subst dc.
simpl fst.
do 8 rewrite fpoint_Merge.
simpl fpoint.
eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
elim eq_dart_dec; intro h3.
assert False; [lia|tauto].
generalize (Halign da d d0).
simpl. eqdartdec.
intro h; apply h.
do 2 right; assumption.
left; trivial.
right; left; trivial.
apply not_eq_sym; apply Hp2; assumption.
apply not_eq_sym; apply Hp3; assumption.
elimination Hdc.
subst dc.
eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
tauto.
elimination Hdc.
subst dc.
simpl fst.
do 8 rewrite fpoint_Merge.
simpl fpoint. eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
elim eq_dart_dec; intro h3.
assert False; [lia|tauto].
elim eq_dart_dec; intro h4.
assert False; [lia|tauto].
generalize (Halign da d d0).
simpl. eqdartdec.
intro h; apply h.
do 2 right; assumption.
left; trivial.
right; left; trivial.
apply not_eq_sym; apply Hp2; assumption.
apply not_eq_sym; apply Hp3; assumption.
tauto.
elimination Hdb.
subst db.
elimination Hdc.
subst dc.
simpl fst.
do 8 rewrite fpoint_Merge.
simpl fpoint.
eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
generalize (Halign da d0 d).
simpl. eqdartdec.
intro h; apply h.
do 2 right; assumption.
right; left; trivial.
left; trivial.
apply not_eq_sym; apply Hp3; assumption.
apply not_eq_sym; apply Hp2; assumption.
elimination Hdc.
subst dc.
eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
elim eq_dart_dec; intro h3.
assert False; [lia|tauto].
tauto.
elimination Hdc.
subst dc.
simpl fst.
do 8 rewrite fpoint_Merge.
simpl fpoint.
eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
elim eq_dart_dec; intro h3.
assert False; [lia|tauto].
elim eq_dart_dec; intro h4.
assert False; [lia|tauto].
generalize (Halign da d0 d).
simpl. eqdartdec.
intro h; apply h.
do 2 right; assumption.
right; left; trivial.
left; trivial.
apply not_eq_sym; apply Hp3; assumption.
apply not_eq_sym; apply Hp2; assumption.
elimination Hdc.
subst dc.
eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
tauto.
tauto.
tauto.
(**)
  intros Hmax1 Hmax2.
  apply inv_hmap_inv_gmap_inv_poly_planar_well_emb_convex_CHI; try assumption.
apply exd_fst_snd_CH2.
apply inv_hmap_CH2; try assumption; try lia.
apply inv_gmap_CH2; try assumption; try lia.
apply inv_poly_CH2; try assumption; try lia.
apply planar_CH2; try assumption; try lia.
apply is_well_emb_CH2; try assumption; try lia.
apply is_neq_point_CH2; try assumption; try lia.
apply is_noalign_CH2; try assumption; try lia.
apply is_convex_CH2; try assumption; try lia.
apply not_expf_m5_da_cA_m5_zero_da; try assumption; try lia.
(* Hw0 *)
intros da Hda.
apply not_eq_sym.
apply lt_0_neq.
lia.
(* Hw1 *)
intros da Hda; simpl fst.
do 4 rewrite <- exd_Merge.
simpl. intro h.
elimination h.
apply max_dart_not_exd with m da.
lia. assumption.
elimination h.
apply max_dart_not_exd with m da.
lia. assumption.
elimination h.
subst da; apply H4; assumption.
elimination h.
subst da; apply H2; assumption.
assumption.
(* Hw5 *)
intros da Hda; split; simpl fst.
apply max_dart_not_exd.
lia.
do 4 rewrite <- exd_Merge.
simpl. intro h.
elimination h.
subst da; lia.
elimination h.
subst da; lia.
elimination h.
subst da; lia.
elimination h.
subst da; lia.
assumption.
(* Hp1 *)
intros da db Hda; simpl fst.
do 4 rewrite <- exd_Merge.
do 4 rewrite fpoint_Merge.
simpl. intro Hdb.
elimination Hdb.
subst db. eqdartdec.
apply not_eq_sym; apply Hp2; assumption.
elimination Hdb.
subst db. eqdartdec.
elim eq_dart_dec; intro h0.
assert False; [lia|tauto].
apply not_eq_sym; apply Hp3; assumption.
elimination Hdb.
subst db. eqdartdec.
elim eq_dart_dec; intro t1.
apply not_eq_sym; apply Hp2; assumption.
elim eq_dart_dec; intro t2.
apply not_eq_sym; apply Hp3; assumption.
apply not_eq_sym; apply Hp2; assumption.
elimination Hdb.
subst db. eqdartdec.
elim eq_dart_dec; intro t1.
apply not_eq_sym; apply Hp2; assumption.
elim eq_dart_dec; intro t2.
apply not_eq_sym; apply Hp3; assumption.
apply not_eq_sym; apply Hp3; assumption.
tauto.
(* Hp2 *)
intros da db dc Hda Hdb Hdc Hp0.
assert (t1: da <> d).
intro h; apply H4; rewrite <- h; assumption.
assert (t2: da <> d0).
intro h; apply H2; rewrite <- h; assumption.
assert (t3: db <> d).
intro h; apply H4; rewrite <- h; assumption.
assert (t4: db <> d0).
intro h; apply H2; rewrite <- h; assumption.
simpl fst in Hdc.
do 4 rewrite <- exd_Merge in Hdc.
simpl in Hdc.
elimination Hdc.
subst dc.
simpl fst.
do 4 rewrite fpoint_Merge.
simpl fpoint. eqdartdec.
generalize (Halign da db d).
simpl. eqdartdec.
intro h; apply h.
do 2 right; assumption.
do 2 right; assumption.
left; trivial. assumption.
apply not_eq_sym; apply Hp2; assumption.
apply not_eq_sym; apply Hp2; assumption.
elimination Hdc.
subst dc.
simpl fst.
do 4 rewrite fpoint_Merge.
simpl fpoint. eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
generalize (Halign da db d0).
simpl. eqdartdec.
intro h; apply h.
do 2 right; assumption.
do 2 right; assumption.
right; left; trivial. assumption.
apply not_eq_sym; apply Hp3; assumption.
apply not_eq_sym; apply Hp3; assumption.
elimination Hdc.
subst dc.
simpl fst.
do 4 rewrite fpoint_Merge.
simpl fpoint. eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
generalize (Halign da db d).
simpl. eqdartdec.
intro h; apply h.
do 2 right; assumption.
do 2 right; assumption.
left; trivial. assumption.
apply not_eq_sym; apply Hp2; assumption.
apply not_eq_sym; apply Hp2; assumption.
elimination Hdc.
subst dc.
simpl fst.
do 4 rewrite fpoint_Merge.
simpl fpoint. eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
generalize (Halign da db d0).
simpl. eqdartdec.
intro h; apply h.
do 2 right; assumption.
do 2 right; assumption.
right; left; trivial. assumption.
apply not_eq_sym; apply Hp3; assumption.
apply not_eq_sym; apply Hp3; assumption.
tauto.
(* Hp3 *)
intros da db dc Hda Hdb Hdc Hp0.
assert (t1: da <> d).
intro h; apply H4; rewrite <- h; assumption.
assert (t2: da <> d0).
intro h; apply H2; rewrite <- h; assumption.
simpl fst in Hdb, Hdc, Hp0.
do 4 rewrite <- exd_Merge in Hdb.
do 4 rewrite <- exd_Merge in Hdc.
do 8 rewrite fpoint_Merge in Hp0.
simpl in Hdb, Hdc, Hp0.
generalize Hp0; clear Hp0.
elimination Hdb.
subst db.
elimination Hdc.
subst dc.
eqdartdec. tauto.
elimination Hdc.
subst dc.
simpl fst.
do 8 rewrite fpoint_Merge.
simpl fpoint. eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
generalize (Halign da d d0).
simpl. eqdartdec.
intro h; apply h.
do 2 right; assumption.
left; trivial.
right; left; trivial.
apply not_eq_sym; apply Hp2; assumption.
apply not_eq_sym; apply Hp3; assumption.
elimination Hdc.
subst dc.
eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
tauto.
elimination Hdc.
subst dc.
simpl fst.
do 8 rewrite fpoint_Merge.
simpl fpoint. eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
generalize (Halign da d d0).
simpl. eqdartdec.
intro h; apply h.
do 2 right; assumption.
left; trivial.
right; left; trivial.
apply not_eq_sym; apply Hp2; assumption.
apply not_eq_sym; apply Hp3; assumption.
tauto.
elimination Hdb.
subst db.
elimination Hdc.
subst dc.
simpl fst.
do 8 rewrite fpoint_Merge.
simpl fpoint.
eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
generalize (Halign da d0 d).
simpl. eqdartdec.
intro h; apply h.
do 2 right; assumption.
right; left; trivial.
left; trivial.
apply not_eq_sym; apply Hp3; assumption.
apply not_eq_sym; apply Hp2; assumption.
elimination Hdc.
subst dc.
eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
tauto.
elimination Hdc.
subst dc.
simpl fst.
do 8 rewrite fpoint_Merge.
simpl fpoint.
eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
elim eq_dart_dec; intro h3.
assert False; [lia|tauto].
generalize (Halign da d0 d).
simpl. eqdartdec.
intro h; apply h.
do 2 right; assumption.
right; left; trivial.
left; trivial.
apply not_eq_sym; apply Hp3; assumption.
apply not_eq_sym; apply Hp2; assumption.
elimination Hdc.
subst dc.
eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
elim eq_dart_dec; intro h3.
assert False; [lia|tauto].
tauto.
tauto.
elimination Hdb.
subst db.
elimination Hdc.
subst dc.
eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
tauto.
elimination Hdc.
subst dc.
simpl fst.
do 8 rewrite fpoint_Merge.
simpl fpoint.
eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
elim eq_dart_dec; intro h3.
assert False; [lia|tauto].
generalize (Halign da d d0).
simpl. eqdartdec.
intro h; apply h.
do 2 right; assumption.
left; trivial.
right; left; trivial.
apply not_eq_sym; apply Hp2; assumption.
apply not_eq_sym; apply Hp3; assumption.
elimination Hdc.
subst dc.
eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
tauto.
elimination Hdc.
subst dc.
simpl fst.
do 8 rewrite fpoint_Merge.
simpl fpoint. eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
elim eq_dart_dec; intro h3.
assert False; [lia|tauto].
elim eq_dart_dec; intro h4.
assert False; [lia|tauto].
generalize (Halign da d d0).
simpl. eqdartdec.
intro h; apply h.
do 2 right; assumption.
left; trivial.
right; left; trivial.
apply not_eq_sym; apply Hp2; assumption.
apply not_eq_sym; apply Hp3; assumption.
tauto.
elimination Hdb.
subst db.
elimination Hdc.
subst dc.
simpl fst.
do 8 rewrite fpoint_Merge.
simpl fpoint.
eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
generalize (Halign da d0 d).
simpl. eqdartdec.
intro h; apply h.
do 2 right; assumption.
right; left; trivial.
left; trivial.
apply not_eq_sym; apply Hp3; assumption.
apply not_eq_sym; apply Hp2; assumption.
elimination Hdc.
subst dc.
eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
elim eq_dart_dec; intro h3.
assert False; [lia|tauto].
tauto.
elimination Hdc.
subst dc.
simpl fst.
do 8 rewrite fpoint_Merge.
simpl fpoint.
eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
elim eq_dart_dec; intro h3.
assert False; [lia|tauto].
elim eq_dart_dec; intro h4.
assert False; [lia|tauto].
generalize (Halign da d0 d).
simpl. eqdartdec.
intro h; apply h.
do 2 right; assumption.
right; left; trivial.
left; trivial.
apply not_eq_sym; apply Hp3; assumption.
apply not_eq_sym; apply Hp2; assumption.
elimination Hdc.
subst dc.
eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
tauto.
tauto.
tauto.
(**)
elim (le_lt_dec d d0).
(**)
  intros Hmax1 Hmax2.
  apply inv_hmap_inv_gmap_inv_poly_planar_well_emb_convex_CHI; try assumption.
apply exd_fst_snd_CH2.
apply inv_hmap_CH2; try assumption; try lia.
apply inv_gmap_CH2; try assumption; try lia.
apply inv_poly_CH2; try assumption; try lia.
apply planar_CH2; try assumption; try lia.
apply is_well_emb_CH2; try assumption; try lia.
apply is_neq_point_CH2; try assumption; try lia.
apply is_noalign_CH2; try assumption; try lia.
apply is_convex_CH2; try assumption; try lia.
apply not_expf_m5_da_cA_m5_zero_da; try assumption; try lia.
(* Hw0 *)
intros da Hda.
apply not_eq_sym.
apply lt_0_neq.
lia.
(* Hw1 *)
intros da Hda; simpl fst.
do 4 rewrite <- exd_Merge.
simpl. intro h.
elimination h.
apply max_dart_not_exd with m da.
lia. assumption.
elimination h.
apply max_dart_not_exd with m da.
lia. assumption.
elimination h.
subst da; apply H4; assumption.
elimination h.
subst da; apply H2; assumption.
assumption.
(* Hw5 *)
intros da Hda; split; simpl fst.
apply max_dart_not_exd.
lia.
do 4 rewrite <- exd_Merge.
simpl. intro h.
elimination h.
subst da; lia.
elimination h.
subst da; lia.
elimination h.
subst da; lia.
elimination h.
subst da; lia.
assumption.
(* Hp1 *)
intros da db Hda; simpl fst.
do 4 rewrite <- exd_Merge.
do 4 rewrite fpoint_Merge.
simpl. intro Hdb.
elimination Hdb.
subst db. eqdartdec.
apply not_eq_sym; apply Hp2; assumption.
elimination Hdb.
subst db. eqdartdec.
elim eq_dart_dec; intro h0.
assert False; [lia|tauto].
apply not_eq_sym; apply Hp3; assumption.
elimination Hdb.
subst db. eqdartdec.
elim eq_dart_dec; intro t1.
apply not_eq_sym; apply Hp2; assumption.
elim eq_dart_dec; intro t2.
apply not_eq_sym; apply Hp3; assumption.
apply not_eq_sym; apply Hp2; assumption.
elimination Hdb.
subst db. eqdartdec.
elim eq_dart_dec; intro t1.
apply not_eq_sym; apply Hp2; assumption.
elim eq_dart_dec; intro t2.
apply not_eq_sym; apply Hp3; assumption.
apply not_eq_sym; apply Hp3; assumption.
tauto.
(* Hp2 *)
intros da db dc Hda Hdb Hdc Hp0.
assert (t1: da <> d).
intro h; apply H4; rewrite <- h; assumption.
assert (t2: da <> d0).
intro h; apply H2; rewrite <- h; assumption.
assert (t3: db <> d).
intro h; apply H4; rewrite <- h; assumption.
assert (t4: db <> d0).
intro h; apply H2; rewrite <- h; assumption.
simpl fst in Hdc.
do 4 rewrite <- exd_Merge in Hdc.
simpl in Hdc.
elimination Hdc.
subst dc.
simpl fst.
do 4 rewrite fpoint_Merge.
simpl fpoint. eqdartdec.
generalize (Halign da db d).
simpl. eqdartdec.
intro h; apply h.
do 2 right; assumption.
do 2 right; assumption.
left; trivial. assumption.
apply not_eq_sym; apply Hp2; assumption.
apply not_eq_sym; apply Hp2; assumption.
elimination Hdc.
subst dc.
simpl fst.
do 4 rewrite fpoint_Merge.
simpl fpoint. eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
generalize (Halign da db d0).
simpl. eqdartdec.
intro h; apply h.
do 2 right; assumption.
do 2 right; assumption.
right; left; trivial. assumption.
apply not_eq_sym; apply Hp3; assumption.
apply not_eq_sym; apply Hp3; assumption.
elimination Hdc.
subst dc.
simpl fst.
do 4 rewrite fpoint_Merge.
simpl fpoint. eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
generalize (Halign da db d).
simpl. eqdartdec.
intro h; apply h.
do 2 right; assumption.
do 2 right; assumption.
left; trivial. assumption.
apply not_eq_sym; apply Hp2; assumption.
apply not_eq_sym; apply Hp2; assumption.
elimination Hdc.
subst dc.
simpl fst.
do 4 rewrite fpoint_Merge.
simpl fpoint. eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
generalize (Halign da db d0).
simpl. eqdartdec.
intro h; apply h.
do 2 right; assumption.
do 2 right; assumption.
right; left; trivial. assumption.
apply not_eq_sym; apply Hp3; assumption.
apply not_eq_sym; apply Hp3; assumption.
tauto.
(* Hp3 *)
intros da db dc Hda Hdb Hdc Hp0.
assert (t1: da <> d).
intro h; apply H4; rewrite <- h; assumption.
assert (t2: da <> d0).
intro h; apply H2; rewrite <- h; assumption.
simpl fst in Hdb, Hdc, Hp0.
do 4 rewrite <- exd_Merge in Hdb.
do 4 rewrite <- exd_Merge in Hdc.
do 8 rewrite fpoint_Merge in Hp0.
simpl in Hdb, Hdc, Hp0.
generalize Hp0; clear Hp0.
elimination Hdb.
subst db.
elimination Hdc.
subst dc.
eqdartdec. tauto.
elimination Hdc.
subst dc.
simpl fst.
do 8 rewrite fpoint_Merge.
simpl fpoint. eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
generalize (Halign da d d0).
simpl. eqdartdec.
intro h; apply h.
do 2 right; assumption.
left; trivial.
right; left; trivial.
apply not_eq_sym; apply Hp2; assumption.
apply not_eq_sym; apply Hp3; assumption.
elimination Hdc.
subst dc.
eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
tauto.
elimination Hdc.
subst dc.
simpl fst.
do 8 rewrite fpoint_Merge.
simpl fpoint. eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
generalize (Halign da d d0).
simpl. eqdartdec.
intro h; apply h.
do 2 right; assumption.
left; trivial.
right; left; trivial.
apply not_eq_sym; apply Hp2; assumption.
apply not_eq_sym; apply Hp3; assumption.
tauto.
elimination Hdb.
subst db.
elimination Hdc.
subst dc.
simpl fst.
do 8 rewrite fpoint_Merge.
simpl fpoint.
eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
generalize (Halign da d0 d).
simpl. eqdartdec.
intro h; apply h.
do 2 right; assumption.
right; left; trivial.
left; trivial.
apply not_eq_sym; apply Hp3; assumption.
apply not_eq_sym; apply Hp2; assumption.
elimination Hdc.
subst dc.
eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
tauto.
elimination Hdc.
subst dc.
simpl fst.
do 8 rewrite fpoint_Merge.
simpl fpoint.
eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
elim eq_dart_dec; intro h3.
assert False; [lia|tauto].
generalize (Halign da d0 d).
simpl. eqdartdec.
intro h; apply h.
do 2 right; assumption.
right; left; trivial.
left; trivial.
apply not_eq_sym; apply Hp3; assumption.
apply not_eq_sym; apply Hp2; assumption.
elimination Hdc.
subst dc.
eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
elim eq_dart_dec; intro h3.
assert False; [lia|tauto].
tauto.
tauto.
elimination Hdb.
subst db.
elimination Hdc.
subst dc.
eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
tauto.
elimination Hdc.
subst dc.
simpl fst.
do 8 rewrite fpoint_Merge.
simpl fpoint.
eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
elim eq_dart_dec; intro h3.
assert False; [lia|tauto].
generalize (Halign da d d0).
simpl. eqdartdec.
intro h; apply h.
do 2 right; assumption.
left; trivial.
right; left; trivial.
apply not_eq_sym; apply Hp2; assumption.
apply not_eq_sym; apply Hp3; assumption.
elimination Hdc.
subst dc.
eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
tauto.
elimination Hdc.
subst dc.
simpl fst.
do 8 rewrite fpoint_Merge.
simpl fpoint. eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
elim eq_dart_dec; intro h3.
assert False; [lia|tauto].
elim eq_dart_dec; intro h4.
assert False; [lia|tauto].
generalize (Halign da d d0).
simpl. eqdartdec.
intro h; apply h.
do 2 right; assumption.
left; trivial.
right; left; trivial.
apply not_eq_sym; apply Hp2; assumption.
apply not_eq_sym; apply Hp3; assumption.
tauto.
elimination Hdb.
subst db.
elimination Hdc.
subst dc.
simpl fst.
do 8 rewrite fpoint_Merge.
simpl fpoint.
eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
generalize (Halign da d0 d).
simpl. eqdartdec.
intro h; apply h.
do 2 right; assumption.
right; left; trivial.
left; trivial.
apply not_eq_sym; apply Hp3; assumption.
apply not_eq_sym; apply Hp2; assumption.
elimination Hdc.
subst dc.
eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
elim eq_dart_dec; intro h3.
assert False; [lia|tauto].
tauto.
elimination Hdc.
subst dc.
simpl fst.
do 8 rewrite fpoint_Merge.
simpl fpoint.
eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
elim eq_dart_dec; intro h3.
assert False; [lia|tauto].
elim eq_dart_dec; intro h4.
assert False; [lia|tauto].
generalize (Halign da d0 d).
simpl. eqdartdec.
intro h; apply h.
do 2 right; assumption.
right; left; trivial.
left; trivial.
apply not_eq_sym; apply Hp3; assumption.
apply not_eq_sym; apply Hp2; assumption.
elimination Hdc.
subst dc.
eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
tauto.
tauto.
tauto.
(**)
  intros Hmax1 Hmax2.
  apply inv_hmap_inv_gmap_inv_poly_planar_well_emb_convex_CHI; try assumption.
apply exd_fst_snd_CH2.
apply inv_hmap_CH2; try assumption; try lia.
apply inv_gmap_CH2; try assumption; try lia.
apply inv_poly_CH2; try assumption; try lia.
apply planar_CH2; try assumption; try lia.
apply is_well_emb_CH2; try assumption; try lia.
apply is_neq_point_CH2; try assumption; try lia.
apply is_noalign_CH2; try assumption; try lia.
apply is_convex_CH2; try assumption; try lia.
apply not_expf_m5_da_cA_m5_zero_da; try assumption; try lia.
(* Hw0 *)
intros da Hda.
apply not_eq_sym.
apply lt_0_neq.
lia.
(* Hw1 *)
intros da Hda; simpl fst.
do 4 rewrite <- exd_Merge.
simpl. intro h.
elimination h.
apply max_dart_not_exd with m da.
lia. assumption.
elimination h.
apply max_dart_not_exd with m da.
lia. assumption.
elimination h.
subst da; apply H4; assumption.
elimination h.
subst da; apply H2; assumption.
assumption.
(* Hw5 *)
intros da Hda; split; simpl fst.
apply max_dart_not_exd.
lia.
do 4 rewrite <- exd_Merge.
simpl. intro h.
elimination h.
subst da; lia.
elimination h.
subst da; lia.
elimination h.
subst da; lia.
elimination h.
subst da; lia.
assumption.
(* Hp1 *)
intros da db Hda; simpl fst.
do 4 rewrite <- exd_Merge.
do 4 rewrite fpoint_Merge.
simpl. intro Hdb.
elimination Hdb.
subst db. eqdartdec.
apply not_eq_sym; apply Hp2; assumption.
elimination Hdb.
subst db. eqdartdec.
elim eq_dart_dec; intro h0.
assert False; [lia|tauto].
apply not_eq_sym; apply Hp3; assumption.
elimination Hdb.
subst db. eqdartdec.
elim eq_dart_dec; intro t1.
apply not_eq_sym; apply Hp2; assumption.
elim eq_dart_dec; intro t2.
apply not_eq_sym; apply Hp3; assumption.
apply not_eq_sym; apply Hp2; assumption.
elimination Hdb.
subst db. eqdartdec.
elim eq_dart_dec; intro t1.
apply not_eq_sym; apply Hp2; assumption.
elim eq_dart_dec; intro t2.
apply not_eq_sym; apply Hp3; assumption.
apply not_eq_sym; apply Hp3; assumption.
tauto.
(* Hp2 *)
intros da db dc Hda Hdb Hdc Hp0.
assert (t1: da <> d).
intro h; apply H4; rewrite <- h; assumption.
assert (t2: da <> d0).
intro h; apply H2; rewrite <- h; assumption.
assert (t3: db <> d).
intro h; apply H4; rewrite <- h; assumption.
assert (t4: db <> d0).
intro h; apply H2; rewrite <- h; assumption.
simpl fst in Hdc.
do 4 rewrite <- exd_Merge in Hdc.
simpl in Hdc.
elimination Hdc.
subst dc.
simpl fst.
do 4 rewrite fpoint_Merge.
simpl fpoint. eqdartdec.
generalize (Halign da db d).
simpl. eqdartdec.
intro h; apply h.
do 2 right; assumption.
do 2 right; assumption.
left; trivial. assumption.
apply not_eq_sym; apply Hp2; assumption.
apply not_eq_sym; apply Hp2; assumption.
elimination Hdc.
subst dc.
simpl fst.
do 4 rewrite fpoint_Merge.
simpl fpoint. eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
generalize (Halign da db d0).
simpl. eqdartdec.
intro h; apply h.
do 2 right; assumption.
do 2 right; assumption.
right; left; trivial. assumption.
apply not_eq_sym; apply Hp3; assumption.
apply not_eq_sym; apply Hp3; assumption.
elimination Hdc.
subst dc.
simpl fst.
do 4 rewrite fpoint_Merge.
simpl fpoint. eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
generalize (Halign da db d).
simpl. eqdartdec.
intro h; apply h.
do 2 right; assumption.
do 2 right; assumption.
left; trivial. assumption.
apply not_eq_sym; apply Hp2; assumption.
apply not_eq_sym; apply Hp2; assumption.
elimination Hdc.
subst dc.
simpl fst.
do 4 rewrite fpoint_Merge.
simpl fpoint. eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
generalize (Halign da db d0).
simpl. eqdartdec.
intro h; apply h.
do 2 right; assumption.
do 2 right; assumption.
right; left; trivial. assumption.
apply not_eq_sym; apply Hp3; assumption.
apply not_eq_sym; apply Hp3; assumption.
tauto.
(* Hp3 *)
intros da db dc Hda Hdb Hdc Hp0.
assert (t1: da <> d).
intro h; apply H4; rewrite <- h; assumption.
assert (t2: da <> d0).
intro h; apply H2; rewrite <- h; assumption.
simpl fst in Hdb, Hdc, Hp0.
do 4 rewrite <- exd_Merge in Hdb.
do 4 rewrite <- exd_Merge in Hdc.
do 8 rewrite fpoint_Merge in Hp0.
simpl in Hdb, Hdc, Hp0.
generalize Hp0; clear Hp0.
elimination Hdb.
subst db.
elimination Hdc.
subst dc.
eqdartdec. tauto.
elimination Hdc.
subst dc.
simpl fst.
do 8 rewrite fpoint_Merge.
simpl fpoint. eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
generalize (Halign da d d0).
simpl. eqdartdec.
intro h; apply h.
do 2 right; assumption.
left; trivial.
right; left; trivial.
apply not_eq_sym; apply Hp2; assumption.
apply not_eq_sym; apply Hp3; assumption.
elimination Hdc.
subst dc.
eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
tauto.
elimination Hdc.
subst dc.
simpl fst.
do 8 rewrite fpoint_Merge.
simpl fpoint. eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
generalize (Halign da d d0).
simpl. eqdartdec.
intro h; apply h.
do 2 right; assumption.
left; trivial.
right; left; trivial.
apply not_eq_sym; apply Hp2; assumption.
apply not_eq_sym; apply Hp3; assumption.
tauto.
elimination Hdb.
subst db.
elimination Hdc.
subst dc.
simpl fst.
do 8 rewrite fpoint_Merge.
simpl fpoint.
eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
generalize (Halign da d0 d).
simpl. eqdartdec.
intro h; apply h.
do 2 right; assumption.
right; left; trivial.
left; trivial.
apply not_eq_sym; apply Hp3; assumption.
apply not_eq_sym; apply Hp2; assumption.
elimination Hdc.
subst dc.
eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
tauto.
elimination Hdc.
subst dc.
simpl fst.
do 8 rewrite fpoint_Merge.
simpl fpoint.
eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
elim eq_dart_dec; intro h3.
assert False; [lia|tauto].
generalize (Halign da d0 d).
simpl. eqdartdec.
intro h; apply h.
do 2 right; assumption.
right; left; trivial.
left; trivial.
apply not_eq_sym; apply Hp3; assumption.
apply not_eq_sym; apply Hp2; assumption.
elimination Hdc.
subst dc.
eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
elim eq_dart_dec; intro h3.
assert False; [lia|tauto].
tauto.
tauto.
elimination Hdb.
subst db.
elimination Hdc.
subst dc.
eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
tauto.
elimination Hdc.
subst dc.
simpl fst.
do 8 rewrite fpoint_Merge.
simpl fpoint.
eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
elim eq_dart_dec; intro h3.
assert False; [lia|tauto].
generalize (Halign da d d0).
simpl. eqdartdec.
intro h; apply h.
do 2 right; assumption.
left; trivial.
right; left; trivial.
apply not_eq_sym; apply Hp2; assumption.
apply not_eq_sym; apply Hp3; assumption.
elimination Hdc.
subst dc.
eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
tauto.
elimination Hdc.
subst dc.
simpl fst.
do 8 rewrite fpoint_Merge.
simpl fpoint. eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
elim eq_dart_dec; intro h3.
assert False; [lia|tauto].
elim eq_dart_dec; intro h4.
assert False; [lia|tauto].
generalize (Halign da d d0).
simpl. eqdartdec.
intro h; apply h.
do 2 right; assumption.
left; trivial.
right; left; trivial.
apply not_eq_sym; apply Hp2; assumption.
apply not_eq_sym; apply Hp3; assumption.
tauto.
elimination Hdb.
subst db.
elimination Hdc.
subst dc.
simpl fst.
do 8 rewrite fpoint_Merge.
simpl fpoint.
eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
generalize (Halign da d0 d).
simpl. eqdartdec.
intro h; apply h.
do 2 right; assumption.
right; left; trivial.
left; trivial.
apply not_eq_sym; apply Hp3; assumption.
apply not_eq_sym; apply Hp2; assumption.
elimination Hdc.
subst dc.
eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
elim eq_dart_dec; intro h3.
assert False; [lia|tauto].
tauto.
elimination Hdc.
subst dc.
simpl fst.
do 8 rewrite fpoint_Merge.
simpl fpoint.
eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
elim eq_dart_dec; intro h3.
assert False; [lia|tauto].
elim eq_dart_dec; intro h4.
assert False; [lia|tauto].
generalize (Halign da d0 d).
simpl. eqdartdec.
intro h; apply h.
do 2 right; assumption.
right; left; trivial.
left; trivial.
apply not_eq_sym; apply Hp3; assumption.
apply not_eq_sym; apply Hp2; assumption.
elimination Hdc.
subst dc.
eqdartdec.
elim eq_dart_dec; intro h1.
assert False; [lia|tauto].
elim eq_dart_dec; intro h2.
assert False; [lia|tauto].
tauto.
tauto.
tauto.
(**)
unfold prec_CH.
simpl linkless.
tauto.
(**)
unfold prec_CH.
simpl linkless.
tauto.
Qed.

(* ================================ *)
(* ========== ########## ========== *)
(* ================================ *)

Theorem inv_hmap_CH : forall (m:fmap),
  prec_CH m -> inv_hmap (fst (CH m)).
Proof.
intros m h.
generalize (inv_hmap_inv_poly_planar_well_emb_convex_CH m h).
intros [h1 [h2 [h3 [h4 [h5 [h6 [h7 h8]]]]]]]; assumption.
Qed.

Theorem inv_gmap_CH : forall (m:fmap),
  prec_CH m -> inv_gmap (fst (CH m)).
Proof.
intros m h.
generalize (inv_hmap_inv_poly_planar_well_emb_convex_CH m h).
intros [h1 [h2 [h3 [h4 [h5 [h6 [h7 h8]]]]]]]; assumption.
Qed.

Theorem inv_poly_CH : forall (m:fmap),
  prec_CH m -> inv_poly (fst (CH m)) (snd (CH m)).
Proof.
intros m h.
generalize (inv_hmap_inv_poly_planar_well_emb_convex_CH m h).
intros [h1 [h2 [h3 [h4 [h5 [h6 [h7 h8]]]]]]]; assumption.
Qed.

Theorem planar_CH : forall (m:fmap),
  prec_CH m -> planar (fst (CH m)).
Proof.
intros m h.
generalize (inv_hmap_inv_poly_planar_well_emb_convex_CH m h).
intros [h1 [h2 [h3 [h4 [h5 [h6 [h7 h8]]]]]]]; assumption.
Qed.

Theorem is_well_emb_CH : forall (m:fmap),
  prec_CH m -> is_well_emb (fst (CH m)).
Proof.
intros m h.
generalize (inv_hmap_inv_poly_planar_well_emb_convex_CH m h).
intros [h1 [h2 [h3 [h4 [h5 [h6 [h7 h8]]]]]]]; assumption.
Qed.

Theorem is_neq_point_CH : forall (m:fmap),
  prec_CH m -> is_neq_point (fst (CH m)).
Proof.
intros m h.
generalize (inv_hmap_inv_poly_planar_well_emb_convex_CH m h).
intros [h1 [h2 [h3 [h4 [h5 [h6 [h7 h8]]]]]]]; assumption.
Qed.

Theorem is_noalign_CH : forall (m:fmap),
  prec_CH m -> is_noalign (fst (CH m)).
Proof.
intros m h.
generalize (inv_hmap_inv_poly_planar_well_emb_convex_CH m h).
intros [h1 [h2 [h3 [h4 [h5 [h6 [h7 h8]]]]]]]; assumption.
Qed.

Theorem is_convex_CH : forall (m:fmap),
  prec_CH m -> is_convex (fst (CH m)) (snd (CH m)).
Proof.
intros m h.
generalize (inv_hmap_inv_poly_planar_well_emb_convex_CH m h).
intros [h1 [h2 [h3 [h4 [h5 [h6 [h7 h8]]]]]]]; assumption.
Qed.
