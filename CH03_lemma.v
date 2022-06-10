(* ================================ *)
(* ========= CH03_lemma.v ========= *)
(* ================================ *)

Require Export CH02_def.

(* ================================ *)
(* ========== ########## ========== *)
(* ================================ *)

Definition inv_gmap (m:fmap) : Prop :=
  forall (k:dim)(x:dart), exd m x -> cA m k (cA m k x) = x.

Definition inv_poly (m:fmap)(d:dart) : Prop :=
  forall (k:dim)(x:dart), eqc m d x -> x <> cA m k x.

Definition is_well_emb (m:fmap) : Prop :=
  forall (x:dart)(y:dart), exd m x -> exd m y -> x <> y ->
  let px := fpoint m x in let py := fpoint m y in
  (expv m x y -> px = py) /\ (expe m x y -> px <> py).

Definition is_neq_point (m:fmap) : Prop :=
  forall (x:dart)(y:dart), exd m x -> exd m y ->
  let px := fpoint m x in let py := fpoint m y in
  ~ expv m x y -> px <> py.

Definition is_noalign (m:fmap) : Prop :=
  forall (x:dart)(y:dart)(z:dart), exd m x -> exd m y -> exd m z ->
  let px := fpoint m x in let py := fpoint m y in let pz := fpoint m z in
  px <> py -> px <> pz -> py <> pz -> ~ align px py pz.

Definition is_convex (m:fmap)(d:dart) : Prop :=
  forall (x:dart)(y:dart), expf m d x -> exd m y ->
  let px := fpoint m x in let py := fpoint m y in
  let px0 := fpoint m (cA m zero x) in
  px <> py -> px0 <> py -> ccw px px0 py.

(* ================================ *)
(* ========== ########## ========== *)
(* ================================ *)

Ltac elimination H := elim H; clear H; intro H.

Ltac eqdartdec := repeat
  let H := fresh in
  match goal with
  | [ |- context [(if (eq_dart_dec ?d ?d) then ?A else ?B)]] =>
    elim (eq_dart_dec d d); [intro H; clear H | tauto]
  | [_:?d1=?d2 |- context [(if (eq_dart_dec ?d1 ?d2) then ?A else ?B)]] =>
    elim (eq_dart_dec d1 d2); [intro H; clear H | contradiction]
  | [_:?d1=?d2 |- context [(if (eq_dart_dec ?d2 ?d1) then ?A else ?B)]] =>
    elim (eq_dart_dec d1 d2); [intro H; clear H | contradiction]
  | [_:?d1<>?d2 |- context [(if (eq_dart_dec ?d1 ?d2) then ?A else ?B)]] =>
    elim (eq_dart_dec d1 d2); [contradiction | intro H; clear H]
  | [H0:?d1<>?d2 |- context [(if (eq_dart_dec ?d2 ?d1) then ?A else ?B)]] =>
    elim (eq_dart_dec d2 d1); [intro H; apply sym_not_eq in H0; contradiction | intro H; clear H]
  end.

(* ================================ *)
(* ========== ########## ========== *)
(* ================================ *)

Lemma fixpoint_cA : forall (m:fmap)(k:dim)(x:dart),
  inv_hmap m -> exd m x -> ~ succ m k x -> ~ pred m k x -> cA m k x = x.
Proof.
intros m k x h1 h2 h3 h4.
apply proj1 with (cA_1 m k x = x).
apply fixpt_cA_cA_1; assumption.
Qed.

Lemma succ_bottom : forall (m:fmap)(k:dim)(x:dart),
  inv_hmap m -> succ m k x \/ pred m k x -> succ m k (bottom m k x).
Proof.
intro m; induction m; intros k x h1.
(* Cas 1 : m = V *)
simpl in *; tauto.
(* Cas 2 : m = I *)
simpl in h1; unfold prec_I in h1.
intro h0; destruct h1 as [h1 [h2 h3]].
unfold succ, pred in *; simpl in *.
elim (eq_dart_dec d x); intro h; try subst d.
assert False; [idtac|tauto]. elimination h0.
apply h3; apply succ_exd with k; assumption.
apply h3; apply pred_exd with k; assumption.
apply IHm; assumption.
(* Cas 3 : m = L *)
simpl in h1; unfold prec_L in h1.
destruct h1 as [h1 [h2 [h3 [h4 [h5 h6]]]]].
unfold succ, pred; simpl in *.
elim eq_dim_dec; intro h; try subst d.
elim (eq_dart_dec d0 x); intro hd0; try subst d0.
elim (eq_dart_dec d1 x); intro hd1; try subst d1.
assert False; [idtac|tauto].
apply h6; apply fixpoint_cA; assumption.
intro h0; clear h0.
elim (eq_dart_dec d1 (bottom m k x)); intro hbx.
elim (eq_dart_dec x (bottom m k x)); intro h.
apply exd_not_nil with m; assumption.
apply IHm; try assumption. right.
elim (pred_dec m k x); try trivial.
intro hp; apply nopred_bottom in hp; try assumption.
apply sym_eq in hp; contradiction.
elim (eq_dart_dec x (bottom m k x)); intro h.
apply exd_not_nil with m; assumption.
apply IHm; try assumption. right.
elim (pred_dec m k x); try trivial.
intro hp; apply nopred_bottom in hp; try assumption.
apply sym_eq in hp; contradiction.
elim (eq_dart_dec d1 x); intro hd1; try subst d1.
intro h0; clear h0.
elim (eq_dart_dec x (bottom m k x)); intro hbx.
elim (eq_dart_dec d0 (bottom m k d0)); intro h.
apply exd_not_nil with m; assumption.
apply IHm; try assumption. right.
elim (pred_dec m k d0); try trivial.
intro hp; apply nopred_bottom in hp; try assumption.
apply sym_eq in hp; contradiction.
apply nopred_bottom in h5; try assumption.
apply sym_eq in h5; contradiction.
intro h0.
elim (eq_dart_dec d1 (bottom m k x)); intro hbx.
elim (eq_dart_dec d0 (bottom m k d0)); intro h.
apply exd_not_nil with m; assumption.
apply IHm; try assumption. right.
elim (pred_dec m k d0); try trivial.
intro hp; apply nopred_bottom in hp; try assumption.
apply sym_eq in hp; contradiction.
elim (eq_dart_dec d0 (bottom m k x)); intro h.
apply exd_not_nil with m; assumption.
apply IHm; try assumption.
apply IHm; try assumption.
Qed.

Lemma neq_succ : forall (m:fmap)(k:dim)(x:dart),
  inv_hmap m -> exd m x -> x <> A m k x.
Proof.
intros m k x h1 h2; induction m.
(* Cas 1 : m = V *)
simpl in *; tauto.
(* Cas 2 : m = I *)
simpl in *; unfold prec_I in h1.
destruct h1 as [h1 [h3 h4]].
elimination h2; try subst d.
rewrite not_exd_A_nil; try assumption.
apply IHm; assumption.
(* Cas 3 : m = L *)
simpl in *; unfold prec_L in h1.
destruct h1 as [h1 [h3 [h4 [h5 [h6 h7]]]]].
elim eq_dim_dec; intro h; try subst d.
elim eq_dart_dec; intro h; try subst d0.
intro h; subst d1; apply h7.
apply fixpoint_cA; assumption.
apply IHm; assumption.
apply IHm; assumption.
Qed.

Lemma neq_succ_succ : forall (m:fmap)(k:dim)(x:dart),
  inv_hmap m -> exd m x -> x <> A m k (A m k x).
Proof.
intros m k x h1 h2; induction m.
(* Cas 1 : m = V *)
simpl in *; tauto.
(* Cas 2 : m = I *)
simpl in *; unfold prec_I in h1.
destruct h1 as [h1 [h3 h4]].
elimination h2; try subst d.
rewrite not_exd_A_nil; try assumption.
intro h0; apply h4; apply exd_A_exd with k; assumption.
apply IHm; assumption.
(* Cas 3 : m = L *)
simpl in *; unfold prec_L in h1.
destruct h1 as [h1 [h3 [h4 [h5 [h6 h7]]]]].
elim eq_dim_dec; intro h; try subst d.
elim (eq_dart_dec d0 x); intro hd0; try subst d0.
elim (eq_dart_dec x d1); intro hd1; try subst d1.
intro h; apply h7; apply fixpoint_cA; assumption.
intro h; apply h7; clear IHm h3 h7.
rewrite cA_bottom; try assumption.
subst x; rewrite bottom_A; try assumption.
apply nopred_bottom; assumption.
unfold succ; apply exd_not_nil with m; assumption.
elim (eq_dart_dec d0 (A m k x)); intro hd1.
intro h; subst x; apply h7; clear IHm h2 h7.
rewrite cA_bottom; try assumption.
subst d0; rewrite bottom_A; try assumption.
apply nopred_bottom; assumption.
unfold succ; apply exd_not_nil with m; assumption.
apply IHm; assumption.
apply IHm; assumption.
Qed.

(* ===== *)

Lemma not_succ_not_succ_B :
  forall (m:fmap)(k:dim)(d:dart)(x:dart),
  inv_hmap m -> ~ succ m k d -> ~ succ (B m k x) k d.
Proof.
intros m k d x hmap.
induction m; simpl in *; try trivial.
unfold succ; simpl; apply IHm; tauto.
simpl in hmap; unfold prec_L in hmap.
unfold succ; simpl.
elim eq_dim_dec; intro hdim; try subst d0.
elim eq_dart_dec; intros h1 h0.
assert False; [idtac|tauto].
apply h0; apply exd_not_nil with m; tauto.
elim eq_dart_dec; intro h2; try assumption.
simpl; elim eq_dim_dec; intro hk; try tauto.
eqdartdec; apply IHm; tauto.
simpl; elim eq_dim_dec; intro hk.
contradiction. apply IHm; tauto.
Qed.

Lemma not_pred_not_pred_B :
  forall (m:fmap)(k:dim)(d:dart)(x:dart),
  inv_hmap m -> ~ pred m k d -> ~ pred (B m k x) k d.
Proof.
intros m k d x hmap.
induction m; simpl in *; try trivial.
unfold pred; simpl; apply IHm; tauto.
simpl in hmap; unfold prec_L in hmap.
unfold pred; simpl.
elim eq_dim_dec; intro hdim; try subst d0.
elim eq_dart_dec; intros h1 h0.
assert False; [idtac|tauto].
apply h0; apply exd_not_nil with m; tauto.
elim eq_dart_dec; intro h2; try assumption.
simpl; elim eq_dim_dec; intro hk; try tauto.
eqdartdec; apply IHm; tauto.
simpl; elim eq_dim_dec; intro hk.
contradiction. apply IHm; tauto.
Qed.

Lemma crack_succ :
  forall (m:fmap)(k:dim)(x:dart)(y:dart), 
  inv_hmap m -> exd m x -> exd m y -> crack m k x y -> 
  (succ m k x \/ succ m k y).
Proof.
intros m k x y H1 H2 H3 H0.
elim (succ_dec m k x); [tauto | intro h1].
elim (succ_dec m k y); [tauto | intro h2].
assert (h3: top m k x = x).
 apply nosucc_top; assumption.
assert (h4 : top m k y = y).
 apply nosucc_top; assumption.
assert False; [idtac|tauto].
unfold crack in H0.
generalize H0; clear H0.
elim eq_dim_dec; intros hk H0.
unfold cracke, MA0.crack in H0.
elim H0; intros h5 h6; apply h5.
rewrite <- h3; rewrite <- h4.
subst k; apply expe_top; tauto.
unfold crackv, MA1.crack in H0.
elim H0; intros h5 h6; apply h5.
rewrite <- h3; rewrite <- h4.
assert (h: k = one).
induction k; tauto.
subst k; apply expv_top; tauto.
Qed.

Lemma eqc_Split :
  forall (m:fmap)(k:dim)(x y z t : dart),
  inv_hmap m -> exd m x -> exd m y -> crack m k x y ->
  eqc (Split m k x y) z t -> eqc m z t.
Proof.
intros m k x y z t hmap hx hy h0.
unfold Split in |- *.
elim succ_dec; intro h1.
elim succ_dec; intro h2.
intro h; apply eqc_B_eqc in h.
simpl in h; elimination h.
apply eqc_B_eqc in h; assumption.
elimination h; destruct h as [t1 t2].
apply eqc_B_eqc in t1; try assumption.
apply eqc_B_eqc in t2; try assumption.
apply eqc_trans with x.
apply eqc_trans with (top m k x); try assumption.
apply eqc_symm; apply eqc_top; assumption.
apply eqc_trans with (bottom m k x); try assumption.
apply eqc_bottom; assumption.
apply eqc_B_eqc in t1; try assumption.
apply eqc_B_eqc in t2; try assumption.
apply eqc_trans with x.
apply eqc_trans with (bottom m k x); try assumption.
apply eqc_symm; apply eqc_bottom; assumption.
apply eqc_trans with (top m k x); try assumption.
apply eqc_top; assumption.
simpl; unfold prec_L; simpl; repeat split.
apply inv_hmap_B; assumption.
apply exd_B; apply exd_top; assumption.
apply exd_B; apply exd_bottom; assumption.
apply not_succ_not_succ_B; try assumption.
apply not_succ_top; assumption.
apply not_pred_not_pred_B; try assumption.
apply not_pred_bottom; assumption.
rewrite cA_B; try assumption.
elim eq_dart_dec; intro t1.
intro t0; rewrite t1 in h1.
apply not_succ_top with m k x; assumption.
eqdartdec; apply not_eq_sym.
apply Del01.succ_bottom; assumption.
unfold succ; simpl.
elim eq_dim_dec; intro hdim; try tauto.
elim eq_dart_dec; intro t1.
apply exd_not_nil with m; try assumption.
apply exd_bottom; assumption.
rewrite A_B_bis; try assumption.
unfold crack in h0.
generalize h0; clear h0.
elim eq_dim_dec; intro hk.
unfold cracke, MA0.crack; intro h0.
apply not_eq_sym; tauto.
unfold crackv, MA1.crack; intro h0.
apply not_eq_sym; tauto.
apply eqc_B_eqc; try assumption.
apply eqc_B_eqc; try assumption.
generalize (crack_succ m k x y hmap hx hy h0).
intro h; elim h; clear h; tauto.
Qed.

(* ================================ *)

Lemma exd_Iter_MA1McAMdf : forall (m:fmap)(x:dart)(i:nat),
  inv_hmap m -> exd m x -> exd m (Iter (MA1.McAMd.f m) i x).
Proof.
intros m0 x0 i h1 h2.
induction i; simpl; try assumption.
pose (u:= (Iter (MA1.McAMd.f m0) i x0)).
fold u; fold u in IHi.
unfold MA1.McAMd.f, Md1.kd.
apply -> exd_cA; assumption.
Qed.

Lemma Iter_MA1McAMdf_I :
  forall (m:fmap)(d:dart)(t:tag)(p:point)(x:dart)(y:dart)(i:nat),
  inv_hmap m -> ~ exd m d -> exd m x ->
  Iter (MA1.McAMd.f (I m d t p)) i x = Iter (MA1.McAMd.f m) i x.
Proof.
intros m0 d0 t0 p0 x0 y0 i h1 h2 h3.
induction i; simpl; trivial.
pose (u:= (Iter (MA1.McAMd.f m0) i x0)).
pose (z:= (Iter (MA1.McAMd.f (I m0 d0 t0 p0)) i x0)).
fold u z; fold u z in IHi.
unfold MA1.McAMd.f, Md1.kd; simpl.
elim eq_dart_dec; intro h.
assert False; [idtac|tauto].
apply h2; rewrite h; rewrite IHi.
unfold u; apply exd_Iter_MA1McAMdf; assumption.
rewrite IHi; trivial.
Qed.

Lemma Iter_MA1McAMdf_I_id :
  forall (m:fmap)(d:dart)(t:tag)(p:point)(i:nat),
  Iter (MA1.McAMd.f (I m d t p)) i d = d.
Proof.
intros m0 d0 t0 p0 i.
induction i; simpl; trivial; rewrite IHi.
unfold MA1.McAMd.f, Md1.kd; simpl; eqdartdec; trivial.
Qed.

(* ===== *)

Lemma expv_I :
  forall (m:fmap)(d:dart)(t:tag)(p:point)(x:dart)(y:dart),
  inv_hmap m -> ~ exd m d -> expv (I m d t p) x y ->
  (d = x /\ d = y) \/ expv m x y.
Proof.
intros m0 d0 t0 p0 x0 y0 h1 h2.
unfold expv, MA1.MfcA.expo, MA1.MfcA.f.
intros [h3 h4]; elim h4; clear h4; intros i hi.
simpl in h3; elimination h3; try subst d0.
left; rewrite Iter_MA1McAMdf_I_id in hi; tauto.
right; split; try assumption; exists i.
rewrite Iter_MA1McAMdf_I in hi; assumption.
Qed.

Lemma not_expv_I :
  forall (m:fmap)(d:dart)(t:tag)(p:point)(x:dart)(y:dart),
  inv_hmap m -> ~ exd m d -> x <> y -> ~ expv m x y ->
  ~ expv (I m d t p) x y.
Proof.
intros m0 d0 t0 p0 x0 y0 h1 h2 h3 h4 h5.
generalize (expv_I m0 d0 t0 p0 x0 y0 h1 h2 h5).
intros h6; elimination h6.
apply h3; intuition;subst;intuition.
apply h4; assumption.
Qed.

Lemma expv_expv_I :
  forall (m:fmap)(d:dart)(t:tag)(p:point)(x:dart)(y:dart),
  inv_hmap m -> ~ exd m d -> expv m x y -> expv (I m d t p) x y.
Proof.
intros m d t p x y h1 h2 h3.
unfold expv, MA1.MfcA.expo in *.
destruct h3 as [h3 h4].
elim h4; clear h4; intros i hi.
split. simpl; right; assumption.
exists i; unfold MA1.MfcA.f.
rewrite Iter_MA1McAMdf_I; assumption.
Qed.

Lemma not_expv_I_not_expv :
  forall (m:fmap)(d:dart)(t:tag)(p:point)(x:dart)(y:dart),
  inv_hmap m -> ~ exd m d -> ~ expv (I m d t p) x y -> ~ expv m x y.
Proof.
intros m d t p x y h1 h2 h3 h.
apply h3; clear h3.
apply expv_expv_I; assumption.
Qed.

(* ===== *)

Lemma expv_refl : forall (m:fmap)(x:dart),
  inv_hmap m -> exd m x -> expv m x x.
Proof.
intros m x h1 h2.
unfold expv, MA1.MfcA.expo.
split. assumption.
exists 0; simpl; trivial.
Qed.

Lemma expv_symm : forall (m:fmap)(x:dart)(y:dart),
  inv_hmap m -> expv m x y -> expv m y x.
Proof.
intros m x y h1 h2.
apply expv_symm; assumption.
Qed.

Lemma not_exd_not_expv : forall (m:fmap)(x:dart)(y:dart),
  ~ exd m x -> ~ expv m x y.
Proof.
intros m0 x0 y0 h1.
unfold expv, MA1.MfcA.expo; tauto.
Qed.

(* ================================ *)

Lemma exd_MA0McAMdf : forall (m:fmap)(x:dart)(i:nat),
  inv_hmap m -> exd m x -> exd m (Iter (MA0.McAMd.f m) i x).
Proof.
intros m0 x0 i h1 h2.
induction i; simpl; try assumption.
pose (u:= (Iter (MA0.McAMd.f m0) i x0)).
fold u; fold u in IHi.
unfold MA0.McAMd.f, Md0.kd.
apply -> exd_cA; assumption.
Qed.

Lemma Iter_MA0McAMdf_I :
  forall (m:fmap)(d:dart)(t:tag)(p:point)(x:dart)(y:dart)(i:nat),
  inv_hmap m -> ~ exd m d -> exd m x ->
  Iter (MA0.McAMd.f (I m d t p)) i x = Iter (MA0.McAMd.f m) i x.
Proof.
intros m0 d0 t0 p0 x0 y0 i h1 h2 h3.
induction i; simpl; trivial.
pose (u:= (Iter (MA0.McAMd.f m0) i x0)).
pose (z:= (Iter (MA0.McAMd.f (I m0 d0 t0 p0)) i x0)).
fold u z; fold u z in IHi.
unfold MA0.McAMd.f, Md0.kd; simpl.
elim eq_dart_dec; intro h.
assert False; [idtac|tauto].
apply h2; rewrite h; rewrite IHi.
unfold u; apply exd_MA0McAMdf; assumption.
rewrite IHi; trivial.
Qed.

Lemma Iter_MA0McAMdf_I_id :
  forall (m:fmap)(d:dart)(t:tag)(p:point)(i:nat),
  Iter (MA0.McAMd.f (I m d t p)) i d = d.
Proof.
intros m0 d0 t0 p0 i.
induction i; simpl; trivial; rewrite IHi.
unfold MA0.McAMd.f, Md0.kd; simpl; eqdartdec; trivial.
Qed.

(* ===== *)

Lemma expe_I : forall (m:fmap)(d:dart)(t:tag)(p:point)(x:dart)(y:dart),
  inv_hmap m -> ~ exd m d -> expe (I m d t p) x y ->
  (d = x /\ d = y) \/ expe m x y.
Proof.
intros m0 d0 t0 p0 x0 y0 h1 h2.
unfold expe, MA0.MfcA.expo, MA0.MfcA.f.
intros [h3 h4]; elim h4; clear h4; intros i hi.
simpl in h3; elimination h3; try subst d0.
left; rewrite Iter_MA0McAMdf_I_id in hi; tauto.
right; split; try assumption; exists i.
rewrite Iter_MA0McAMdf_I in hi; assumption.
Qed.

Lemma not_expe_I : forall (m:fmap)(d:dart)(t:tag)(p:point)(x:dart)(y:dart),
  inv_hmap m -> ~ exd m d -> x <> y -> ~ expe m x y ->
  ~ expe (I m d t p) x y.
Proof.
intros m0 d0 t0 p0 x0 y0 h1 h2 h3 h4 h5.
generalize (expe_I m0 d0 t0 p0 x0 y0 h1 h2 h5).
intros h6; elimination h6.
apply h3; intuition;subst;intuition.
apply h4; assumption.
Qed.

Lemma expe_expe_I :
  forall (m:fmap)(d:dart)(t:tag)(p:point)(x:dart)(y:dart),
  inv_hmap m -> ~ exd m d -> expe m x y -> expe (I m d t p) x y.
Proof.
intros m d t p x y h1 h2 h3.
unfold expe, MA0.MfcA.expo in *.
destruct h3 as [h3 h4].
elim h4; clear h4; intros i hi.
split. simpl; right; assumption.
exists i; unfold MA0.MfcA.f.
rewrite Iter_MA0McAMdf_I; assumption.
Qed.

Lemma not_expe_I_not_expe :
  forall (m:fmap)(d:dart)(t:tag)(p:point)(x:dart)(y:dart),
  inv_hmap m -> ~ exd m d -> ~ expe (I m d t p) x y -> ~ expe m x y.
Proof.
intros m d t p x y h1 h2 h3 h.
apply h3; clear h3.
apply expe_expe_I; assumption.
Qed.

(* ===== *)

Lemma expe_refl : forall (m:fmap)(x:dart),
  inv_hmap m -> exd m x -> expe m x x.
Proof.
intros m x h1 h2.
unfold expe, MA0.MfcA.expo.
split. assumption.
exists 0; simpl; trivial.
Qed.

Lemma expe_symm : forall (m:fmap)(x:dart)(y:dart),
  inv_hmap m -> expe m x y -> expe m y x.
Proof.
intros m x y h1 h2.
apply expe_symm; assumption.
Qed.

Lemma not_exd_not_expe : forall (m:fmap)(x:dart)(y:dart),
  ~ exd m x -> ~ expe m x y.
Proof.
intros m0 x0 y0 h1.
unfold expe, MA0.MfcA.expo; tauto.
Qed.

(* ================================ *)

Lemma subst_cA_cA_1 : forall (m:fmap)(k:dim)(x:dart)(y:dart),
  inv_hmap m -> exd m y -> x = cA m k y -> y = cA_1 m k x.
Proof.
intros m k x y H1 H2 H3; subst x; rewrite cA_1_cA; intuition.
Qed.

Lemma subst_cA_1_cA : forall (m:fmap)(k:dim)(x:dart)(y:dart),
  inv_hmap m -> exd m y -> x = cA_1 m k y -> y = cA m k x.
Proof.
intros m k x y H1 H2 H3; subst x; rewrite cA_cA_1; intuition.
Qed.

Lemma bij_eq_cA : forall (m:fmap)(k:dim)(x:dart)(y:dart),
  inv_hmap m -> exd m x -> exd m y -> 
  (x = y <-> cA m k x = cA m k y).
Proof.
intros m k a b h1 h2 h3; split; intro h0.
elim (eq_dart_dec (cA m k a) (cA m k b)); subst b; tauto.
elim (eq_dart_dec a b); try trivial.
intro h; assert False; [idtac|tauto].
apply subst_cA_cA_1 in h0; try assumption.
rewrite cA_1_cA in h0; try assumption.
apply sym_eq in h0; contradiction.
Qed.

Lemma bij_neq_cA : forall (m:fmap)(k:dim)(x:dart)(y:dart),
  inv_hmap m -> exd m x -> exd m y -> 
  (x <> y <-> cA m k x <> cA m k y).
Proof.
intros m k a b h1 h2 h3; split; intro h0.
elim (eq_dart_dec (cA m k a) (cA m k b)); try trivial.
intro h; assert False; [idtac|tauto].
apply subst_cA_cA_1 in h; try assumption.
rewrite cA_1_cA in h; try assumption.
apply sym_eq in h; contradiction.
elim (eq_dart_dec a b); try trivial.
intro h; assert False; [idtac|tauto].
subst a; tauto.
Qed.

(* ================================ *)

Lemma not_exd_Iter_cF_I :
  forall (m:fmap)(x:dart)(t:tag)(p:point)(i:nat),
  inv_hmap m -> ~ exd m x -> Iter (cF (I m x t p)) i x = x.
Proof.
intros m x t p i H1 H2.
induction i; simpl; trivial.
rewrite IHi; unfold cF.
simpl; eqdartdec; trivial.
Qed.

Lemma Iter_cF_i_nil : forall (m:fmap)(i:nat),
  inv_hmap m -> Iter (cF m) i nil = nil.
Proof.
intros m i h0; induction i; simpl.
trivial. rewrite IHi; unfold cF.
apply not_exd_cA_1; try assumption.
intro h; apply exd_not_nil in h; try assumption.
apply h; clear h.
apply not_exd_cA_1; try assumption.
apply not_exd_nil; assumption.
Qed.

(* ===== *)

Lemma exd_Iter_cF_1 : forall (m:fmap)(d:dart)(i:nat),
  inv_hmap m -> exd m d -> exd m (Iter (cF_1 m) i d).
Proof.
intros m d i h1 h2.
induction i; simpl; try assumption.
apply -> exd_cF_1; assumption.
Qed.

Lemma expf_Iter_cF_1 : forall (m:fmap)(d:dart)(i:nat),
  inv_hmap m -> exd m d -> expf m d (Iter (cF_1 m) i d).
Proof.
intros m d i h1 h2.
induction i.
(* Cas 1 = 0 *)
simpl; apply expf_refl; assumption.
(* Cas 2 = S i *)
apply expf_trans with (Iter (cF_1 m) i d).
assumption. simpl.
pose (di := Iter (cF_1 m) i d). fold di.
assert (H: di = cF m (cF_1 m di)).
rewrite cF_cF_1; try tauto.
apply exd_Iter_cF_1; assumption.
rewrite H at 1; clear H. apply expf_symm.
unfold expf; split. assumption.
unfold MF.expo, MF.f, McF.f; split.
apply -> exd_cF_1; try assumption.
apply exd_Iter_cF_1; assumption.
exists 1; simpl; trivial.
Qed.

Lemma eqc_Iter_cF_1 : forall (m:fmap)(d:dart)(i:nat),
  inv_hmap m -> exd m d -> eqc m d (Iter (cF_1 m) i d).
Proof.
intros m d i h1 h2.
apply expf_eqc; try assumption.
generalize (expf_Iter_cF_1 m d i h1 h2).
unfold expf; tauto.
Qed.

Lemma Iter_cF_1_Iter_cF : forall (m:fmap)(d:dart)(i:nat),
  inv_hmap m -> exd m d -> Iter (cF_1 m) i (Iter (cF m) i d) = d.
Proof.
intros m d i h1 h2.
induction i.
(* Cas 1 = 0 *)
simpl; trivial.
(* Cas 2 = S i *)
assert (h: forall (x:dart),
 cF_1 m (Iter (cF_1 m) i x) = Iter (cF_1 m) i (cF_1 m x)).
 intro x; clear IHi.
 induction i; simpl.
 trivial. rewrite IHi; trivial.
simpl; rewrite h.
rewrite cF_1_cF; try assumption.
apply exd_Iter_cF; assumption.
Qed.

(* ================================ *)
(* ========== ########## ========== *)
(* ================================ *)

Lemma eq_cA_cA_1 : forall (m:fmap)(k:dim)(x:dart),
  inv_hmap m -> inv_gmap m -> cA m k x = cA_1 m k x.
Proof.
intros m k x H1 H2.
elim (exd_dec m x); intro h1.
generalize (H2 k x h1); intro h2.
rewrite <- h2 at 2.
rewrite cA_1_cA; intuition.
apply -> exd_cA; assumption.
rewrite not_exd_cA; try assumption.
rewrite not_exd_cA_1; try assumption.
trivial.
Qed.

Lemma succ_not_succ_cA :
  forall (m:fmap)(k:dim)(d:dart)(x:dart),
  inv_hmap m -> inv_gmap m -> succ m k x -> ~ succ m k (cA m k x).
Proof.
intros m k d x H1 H2 H3 H0.
assert (forall x:dart, succ m k x -> cA m k x = A m k x).
intros da h; rewrite (A_cA m k da (A m k da)); try tauto.
apply succ_exd with k; assumption.
apply succ_exd_A; assumption.
assert (h1: cA m k x = A m k x).
apply H; assumption.
assert (h2: cA m k (cA m k x) = A m k (A m k x)).
rewrite h1 in *; apply H; assumption.
rewrite H2 in h2; try assumption.
apply neq_succ_succ with m k x; try assumption.
apply succ_exd in H3; assumption.
apply succ_exd in H3; assumption.
Qed.

Lemma expf_cA_cA : forall (m:fmap)(x:dart),
  inv_hmap m -> inv_gmap m -> exd m x ->
  expf m (cA m zero x) (cA m one x).
Proof.
intros m x H1 H2 H3.
unfold expf; split.
assumption.
unfold MF.expo; split.
apply -> exd_cA; assumption.
exists 1; simpl.
unfold MF.f, McF.f, cF.
rewrite <- eq_cA_cA_1; try assumption.
rewrite <- eq_cA_cA_1; try assumption.
rewrite H2; try assumption.
trivial.
Qed.

Lemma expf_d0_x0_bis : forall (m:fmap)(d:dart)(i:nat),
  inv_hmap m -> inv_gmap m -> expf m d (Iter (cF m) i d) ->
  expf m (cA m zero d) (cA m zero (Iter (cF m) i d)).
Proof.
intros m d i H1 H2 H3.
assert (exd m d). unfold expf, MF.expo in *; tauto.
induction i; simpl in *.
apply expf_refl; try assumption.
apply -> exd_cA; try assumption.
apply expf_trans with (cA m zero (Iter (cF m) i d)).
apply IHi; unfold expf, MF.expo, MF.f, McF.f.
repeat split; try assumption.
exists i; trivial. apply expf_symm.
unfold expf, MF.expo, MF.f, McF.f.
repeat split; try assumption.
apply -> exd_cA; try assumption.
apply expf_symm in H3.
unfold expf, MF.expo in H3.
destruct H3 as [h1 [h2 h3]]; assumption.
exists 1%nat; simpl.
unfold cF at 1; unfold cF at 1.
rewrite cA_1_cA; try assumption.
rewrite <- eq_cA_cA_1; try assumption.
rewrite cA_cA_1; try assumption.
rewrite <- eq_cA_cA_1; tauto.
apply -> exd_cA_1; try assumption.
apply exd_Iter_cF; assumption.
apply -> exd_cA_1; try assumption.
apply -> exd_cA_1; try assumption.
apply exd_Iter_cF; assumption.
Qed.

Lemma expf_d0_x0 : forall (m:fmap)(d:dart)(x:dart),
  inv_hmap m -> inv_gmap m -> expf m d x ->
  expf m (cA m zero d) (cA m zero x).
Proof.
intros m d x H1 H2 H.
unfold expf, MF.expo, MF.f, McF.f in H.
destruct H as [h1 [h2 h3]].
elim h3; clear h3; intros i hi.
rewrite <- hi.
apply expf_d0_x0_bis; try assumption.
unfold expf, MF.expo, MF.f, McF.f.
repeat split; try assumption.
exists i; trivial.
Qed.

(* ===== *)

Lemma Iter_cA_m_one_i_x : forall (m:fmap)(x:dart)(i:nat),
  inv_hmap m -> inv_gmap m -> exd m x ->
  Iter (MA1.MfcA.f m) i x = x \/ Iter (MA1.MfcA.f m) i x = cA m one x.
Proof.
intros m x i h1 h2 hx; induction i.
simpl; left; tauto. elimination IHi.
right; simpl; rewrite IHi; tauto.
left; simpl; rewrite IHi.
unfold MA1.MfcA.f, MA1.McAMd.f, Md1.kd.
apply h2; assumption.
Qed.

Lemma expv_x_y_eq_x_cA_m_one_x : forall (m:fmap)(x:dart)(y:dart),
  inv_hmap m -> inv_gmap m -> expv m x y -> x = y \/ cA m one x = y.
Proof.
intros m x y h1 h2 h.
unfold expv in h.
unfold MA1.MfcA.expo in h.
destruct h as [t1 t2].
elim t2; clear t2; intros i hi.
generalize (Iter_cA_m_one_i_x m x i h1 h2 t1).
intro h; elimination h; rewrite h in hi.
left; assumption. right; assumption.
Qed.

(* ================================ *)

Lemma inv_poly_succ_or_pred :
  forall (m:fmap)(k:dim)(d:dart)(x:dart),
  inv_hmap m -> inv_poly m d -> eqc m d x ->
  succ m k x \/ pred m k x.
Proof.
intros m k d x H1 H2 H3.
elim (succ_dec m k x); intro h1.
left; assumption.
elim (pred_dec m k x); intro h2.
right; assumption.
assert False; [idtac|tauto].
assert (exd m x).
apply eqc_exd_exd in H3; tauto.
apply H2 with k x; try assumption.
apply sym_eq; apply fixpoint_cA; assumption.
Qed.

Lemma succ_or_succ_cA :
  forall (m:fmap)(k:dim)(d:dart)(x:dart),
  inv_hmap m -> inv_poly m d -> eqc m d x ->
  succ m k x \/ succ m k (cA m k x).
Proof.
intros m k d x H1 H2 H3.
elim (succ_dec m k x); intro h.
left; assumption. right.
rewrite cA_bottom; try assumption.
apply succ_bottom; try assumption.
apply inv_poly_succ_or_pred with d; assumption.
apply eqc_exd_exd in H3; tauto.
Qed.

(* ================================ *)
(* ========== ########## ========== *)
(* ================================ *)

Lemma fpoint_B :
  forall (m:fmap)(k:dim)(x:dart)(y:dart),
  fpoint (B m k x) y = fpoint m y.
Proof.
intros m k x y.
induction m; simpl; try trivial.
elim eq_dart_dec; intro h; try trivial.
elim eq_dim_dec; intro h1; try subst d.
elim eq_dart_dec; intro h2; try trivial.
simpl; assumption.
Qed.

Lemma fpoint_Shift :
  forall (m:fmap)(k:dim)(x:dart)(y:dart),
  fpoint (Shift m k x) y = fpoint m y.
Proof.
intros m k x y; unfold Shift; simpl; apply fpoint_B.
Qed.

Lemma fpoint_Split :
  forall (m:fmap)(k:dim)(x:dart)(y:dart)(z:dart),
  fpoint (Split m k x y) z = fpoint m z.
Proof.
intros m k x y z; unfold Split.
elim succ_dec; intro h1; try apply fpoint_B.
elim succ_dec; intro h2; try apply fpoint_B.
simpl; elim eq_dim_dec; intro h3; try tauto.
elim eq_dart_dec; intro h4; try apply fpoint_B.
simpl; rewrite fpoint_B; apply fpoint_B.
Qed.

Lemma fpoint_Merge :
  forall (m:fmap)(k:dim)(x:dart)(y:dart)(z:dart),
  fpoint (Merge m k x y) z = fpoint m z.
Proof.
intros m k x y z; unfold Merge; simpl.
elim pred_dec; elim succ_dec; intros h1 h2; trivial.
rewrite fpoint_Shift; apply fpoint_Shift.
apply fpoint_Shift. apply fpoint_Shift.
Qed.

(* ================================ *)

Lemma cA_one_fpoint : forall (m:fmap)(d:dart),
  inv_hmap m -> is_well_emb m -> exd m d ->
  fpoint m (cA m one d) = fpoint m d.
Proof.
intros m d h1 h2 h3; apply eq_sym.
elim (eq_dart_dec d (cA m one d));
intro h. rewrite h at 1; trivial.
assert (h4: exd m (cA m one d)).
apply exd_cA; assumption.
generalize (h2 d (cA m one d) h3 h4 h).
intros [t1 t2]; apply t1; clear t1 t2.
unfold expv, MA1.MfcA.expo; split.
assumption. exists 1; simpl.
unfold MA1.MfcA.f, MA1.McAMd.f, Md1.kd.
trivial.
Qed.

Lemma cA_1_one_fpoint : forall (m:fmap)(d:dart),
  inv_hmap m -> is_well_emb m -> exd m d ->
  fpoint m (cA_1 m one d) = fpoint m d.
Proof.
intros m d h1 h2 h3.
elim (eq_dart_dec (cA_1 m one d) d);
intro h. rewrite h; trivial.
assert (h4: exd m (cA_1 m one d)).
apply exd_cA_1; assumption.
generalize (h2 (cA_1 m one d) d h4 h3 h).
intros [t1 t2]; apply t1; clear t1 t2.
unfold expv, MA1.MfcA.expo; split.
assumption. exists 1; simpl.
unfold MA1.MfcA.f, MA1.McAMd.f, Md1.kd.
rewrite cA_cA_1; try assumption. trivial.
Qed.

(* ================================ *)

Lemma cA_zero_fpoint : forall (m:fmap)(d:dart),
  inv_hmap m -> inv_poly m d -> is_well_emb m -> exd m d ->
  fpoint m (cA m zero d) <> fpoint m d.
Proof.
intros m d h1 h2 h3 h4; apply not_eq_sym.
assert (h5: exd m (cA m zero d)).
apply exd_cA; assumption.
assert (h6: d <> cA m zero d).
apply h2; apply eqc_refl; assumption.
generalize (h3 d (cA m zero d) h4 h5 h6).
intros [t1 t2]; apply t2; clear t1 t2.
unfold expe, MA1.MfcA.expo; split.
assumption. exists 1; simpl.
unfold MA0.MfcA.f, MA0.McAMd.f, Md0.kd.
trivial.
Qed.
