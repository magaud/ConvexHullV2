(* ================================ *)
(* ========== CH02_def.v ========== *)
(* ================================ *)

Require Export CH01_ccw.

Open Scope nat_scope.

(* ================================ *)
(* ========== ########## ========== *)
(* ================================ *)

Definition invisible_succ (m:fmap)(d:dart)(p:point) : Prop :=
  (ccw (fpoint m d) (fpoint m (cA m zero d)) p).

Definition invisible_pred (m:fmap)(d:dart)(p:point) : Prop :=
  (ccw (fpoint m (cA_1 m zero d)) (fpoint m d) p).

Definition visible_succ (m:fmap)(d:dart)(p:point) : Prop :=
  (ccw (fpoint m d) p (fpoint m (cA m zero d))).

Definition visible_pred (m:fmap)(d:dart)(p:point) : Prop :=
  (ccw (fpoint m (cA_1 m zero d)) p (fpoint m d)).

(* ================================ *)

Lemma invisible_succ_dec : forall (m:fmap)(d:dart)(p:point),
   {invisible_succ m d p} + {~ invisible_succ m d p}.
Proof.
intros m d p.
unfold invisible_succ.
generalize (ccw_dec (fpoint m d) (fpoint m (cA m zero d)) p).
tauto.
Qed.

Lemma invisible_pred_dec : forall (m:fmap)(d:dart)(p:point),
   {invisible_pred m d p} + {~ invisible_pred m d p}.
Proof.
intros m d p.
unfold invisible_pred.
generalize (ccw_dec (fpoint m (cA_1 m zero d)) (fpoint m d) p).
tauto.
Qed.

Lemma visible_succ_dec : forall (m:fmap)(d:dart)(p:point), 
   {visible_succ m d p} + {~ visible_succ m d p}.
Proof.
intros m d p.
unfold visible_succ.
generalize (ccw_dec (fpoint m d) p (fpoint m (cA m zero d))).
tauto.
Qed.

Lemma visible_pred_dec : forall (m:fmap)(d:dart)(p:point), 
   {visible_pred m d p} + {~ visible_pred m d p}.
Proof.
intros m d p.
unfold visible_pred.
generalize (ccw_dec (fpoint m (cA_1 m zero d)) p (fpoint m d)).
tauto.
Qed.

(* ================================ *)
(* ========== ########## ========== *)
(* ================================ *)

Definition left_dart (m:fmap)(d:dart)(p:point) : Prop :=
  invisible_succ m (cF_1 m d) p /\ visible_succ m d p.

Definition right_dart (m:fmap)(d:dart)(p:point) : Prop :=
  visible_pred m d p /\ invisible_pred m (cF_1 m d) p.

(* ================================ *)

Lemma left_dart_dec : forall (m:fmap)(d:dart)(p:point),
  {left_dart m d p} + {~ left_dart m d p}.
Proof.
intros m d p; unfold left_dart.
generalize (invisible_succ_dec m (cF_1 m d) p).
generalize (visible_succ_dec m d p).
tauto.
Qed.

Lemma right_dart_dec : forall (m:fmap)(d:dart)(p:point),
  {right_dart m d p} + {~ right_dart m d p}.
Proof.
intros m d p; unfold right_dart.
generalize (visible_pred_dec m d p).
generalize (invisible_pred_dec m (cF_1 m d) p).
tauto.
Qed.

(* ================================ *)

Function search_left (m:fmap)(d:dart)(p:point)(i:nat)
  {measure (fun n:nat => (degreef m d) - n) i} : dart :=
  if (le_lt_dec (degreef m d) i) then nil else
  let di := Iter (cF m) i d in
  if (left_dart_dec m di p) then di else search_left m d p (i+1).
Proof.
intros m d p i H1 H2 H3 H4; omega.
Qed.

Function search_right (m:fmap)(d:dart)(p:point)(i:nat)
  {measure (fun n:nat => (degreef m d) - n) i} : dart :=
  if (le_lt_dec (degreef m d) i) then nil else
  let di := (Iter (cF m) i d) in let di0 := (cA m zero di) in
  if (right_dart_dec m di0 p) then di0 else search_right m d p (i+1).
Proof.
intros m d p i H1 H2 H3 H4; omega.
Qed.

(* ================================ *)
(* ========== ########## ========== *)
(* ================================ *)

Fixpoint max_dart (m:fmap) {struct m} : dart :=
  match m with
    V => 0
  | I m0 x t p =>
    if (le_lt_dec x (max_dart m0)) then (max_dart m0) else x
  | L m0 k x y => max_dart m0
  end.

(* ================================ *)

Definition mapdart := (fmap * dart)%type.

Definition CH2 (x1:dart)(t1:tag)(p1:point)(x2:dart)(t2:tag)(p2:point)(max:dart) : mapdart :=
  let m1 := I (I (I (I V x1 t1 p1) x2 t2 p2) (max+1) t1 p1) (max+2) t2 p2 in
  let m2 := Merge (Merge m1 one (max+1) x1) one (max+2) x2 in
  (Merge (Merge m2 zero x1 (max+2)) zero x2 (max+1), x1).

Definition CHID (md:mapdart)(x:dart)(t:tag)(p:point)(max:dart) : mapdart :=
  let m := fst md in let d := snd md in
  let l := search_left m d p 0 in
  if (eq_dart_dec l nil) then (I m x t p, d)
  else let r := search_right m l p 0 in
       let l0 := cA m zero l in
       let r_0 := cA_1 m zero r in
       let m1 := Split m zero l l0 in
       let m2 := if (eq_dart_dec l0 r) then m1
                 else Split m1 zero r_0 r in
       let m3 := (I (I m2 x t p) max t p) in
       let m4 := Merge m3 one max x in
       let m5 := Merge m4 zero l max in
       let m6 := Merge m5 zero x r in (m6, x).

Fixpoint CHI (m:fmap)(md:mapdart)(max:dart) {struct m} : mapdart :=
  match m with
  | I m0 x t p => (CHI m0 (CHID md x t p max) (max+1))
  | _ => md
  end.

Definition CH (m:fmap) : mapdart :=
  match m with
  | I (I m0 x1 t1 p1) x2 t2 p2 =>
    CHI m0 (CH2 x1 t1 p1 x2 t2 p2 (max_dart m)) ((max_dart m)+3)
  | _ => (m,nil)
  end.

(*
Fixpoint delete (m:fmap)(mr:fmap)(d:dart) {struct m} : fmap :=
  match m with
    V => V
  | I m0 x t p =>
    if (eqc_dec mr x d) then I (delete m0 mr d) x t p
    else delete m0 mr d
  | L m0 k x y =>
    if (eqc_dec mr x d) then L (delete m0 mr d) k x y
    else delete m0 mr d
  end.

Definition convexhull (m:fmap) : fmap :=
  let m0 := CH m in delete (fst m0) (fst m0) (snd m0).
*)

(* ================================ *)
(* ========== ########## ========== *)
(* ================================ *)

Extraction Language Ocaml.
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Constant R => "float". 
Extract Constant R0 => "0.0".
Extract Constant R1 => "1.0".
Extract Constant Rplus => "fun x y -> x+.y".
Extract Constant Rmult => "fun x y -> x*.y".
Extract Constant Ropp => "fun x -> -.x".
Extract Constant total_order_T => "fun x y -> if (x<y) then (Inleft true) else if (x=y) then (Inleft false) else (Inright)".
Extraction "fmaps" CH.
