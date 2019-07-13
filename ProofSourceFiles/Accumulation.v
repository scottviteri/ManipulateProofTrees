Module Accum.

Require Import Finite. Import FiniteTypes.
Require Import Le. Require Import Lt. Require Import Plus.
Require Import Omega.
Require Import Classical. Require Import ClassicalDescription.
Require Import Description.

Definition exchange (T : Type) (x y : T) (k : T) :=
  If k = x then y else If k = y then x else k.
Lemma and_idem (A : Prop) :
  A -> A /\ A.
Proof.
  tauto.
Qed.
Lemma exchange_bijective (T : Type) (x y : T) :
  bijection (exchange T x y).
Proof.
  apply bijection_inversible.
  exists (exchange T x y). apply and_idem.
  intro k. unfold exchange.
  destruct (excluded_middle_informative (k = x)).
  rewrite If_l with (P := y = y). case_if.
  congruence. auto. auto.
  destruct (excluded_middle_informative (k = y)).
  rewrite If_l. auto. auto.
  rewrite If_r. rewrite If_r. auto. auto. auto.
Qed.
Lemma exchange_1 (T : Type) (x y : T) :
  exchange T x y x = y.
Proof.
  unfold exchange. apply If_l. auto.
Qed.
Lemma exchange_2 (T : Type) (x y : T) :
  exchange T x y y = x.
Proof.
  unfold exchange. case_if. auto. apply If_l. auto.
Qed.
Lemma lt_not_eq :
  forall n m : nat, n < m -> n <> m.
Proof.
  intros n m H. apply lt_not_le in H. contradict H. destruct H. auto.
Qed.
Theorem induction_double (P : nat -> Prop) :
  P O -> P (S O) -> (forall n, P n -> P (S n) -> P (S (S n))) -> forall n, P n.
Proof.
  intros H0 H1 Hnext.
  assert (forall n, P n /\ P (S n)).
  simple induction n.
  auto. intros n0 H. destruct H. auto.
  intro n. apply H.
Qed.

Section Acc.
Variable T : Type.
Variable mult : T -> T -> T.
Infix "*" := mult.
Hypothesis mult_com :
  forall x y : T, x * y = y * x.
Hypothesis mult_assoc :
  forall x y z : T, x * (y * z) = (x * y) * z.
Variable e : T.
Hypothesis e_idemp : e * e = e.
Hypothesis e_img_neutral :
  forall x y : T, e * (x * y) = (x * y).

Lemma pr_ex (n : nat) (n' : nat) (k : Fints n') (Heq : n = S n') :
  `k < n.
Proof.
  rewrite Heq.
  apply (lt_S `k n' (proj2_sig k)).
Qed.
Lemma pr_ex2 (n : nat) (n' : nat) (Heq : n = S n') :
  n' < n.
Proof.
  rewrite Heq. apply lt_n_Sn.
Qed.
Fixpoint pr (n : nat) (f : Fints n -> T) :=
  match n as n' return n = n' -> T with
    | O => fun _ => e
    | S n' =>
      fun Heq =>
        (pr n' (fun (k : Fints n') =>
           f (exist (fun p => p < n) `k (pr_ex n n' k Heq))))
      * (f (exist (fun p => p < n) n' (pr_ex2 n n' Heq)))
  end (eq_refl n).
Lemma pr_ext :
  forall (n : nat) (f f' : Fints n -> T),
    (forall k : Fints n, f k = f' k) -> pr n f = pr n f'.
Proof.
  simple induction n.
  intros. simpl. auto.
  intros n0 H f f' Heq. simpl.
  f_equal. apply H. intro k.
  apply Heq. apply Heq.
Qed.

Definition prod (n : nat) (I : Type)
    (b : Fints n -> I) (Hb : bijection b) (f : I -> T) :=
  pr n (fun x => f (b x)).
Lemma prod_elim_last (n : nat) (I : Type)
    (b : Fints (S n) -> I) (Hb : bijection b) (f : I -> T) :
  prod (S n) I b Hb f =
  prod n _ _ (bijection_restriction2 Hb) (fun x => f `x) *
    (f (b (Fints_last n))).
Proof.
  unfold prod. simpl. f_equal.
  apply pr_ext. intro k. f_equal. f_equal. unfold Fints_coerce.
  apply proj1_inj. auto.
  f_equal. f_equal. unfold Fints_last. apply proj1_inj. auto.
Qed.

Theorem prod_unique_n :
  forall (n  : nat) (I : Type) (f : I -> T) 
     (b  : Fints n -> I) (Hb  : bijection b )
     (b' : Fints n -> I) (Hb' : bijection b'),
  prod n I b Hb f = prod n I b' Hb' f.
Proof.
  apply (induction_double (fun n => forall (I : Type) (f : I -> T) 
     (b  : Fints n -> I) (Hb  : bijection b )
     (b' : Fints n -> I) (Hb' : bijection b'),
  prod n I b Hb f = prod n I b' Hb' f)).
  intros. unfold prod. auto.
  intros. unfold prod. unfold pr. f_equal. f_equal.
  assert (exists x, b x = b' (exist (fun p : nat => p < 1) 0 (pr_ex2 1 0 eq_refl))).
  apply Hb. destruct H as [x H]. rewrite <- H. f_equal.
  destruct x as [x' Hx']. apply proj1_inj. simpl. clear H. apply le_S_n in Hx'. apply le_n_0_eq. auto.
  intros n1 H' H I f b Hb b' Hb'.
  remember (S n1) as n0.
  do 2 (rewrite prod_elim_last).
  remember (bijection_restriction2 Hb) as Hc. clear HeqHc.
  remember (fun k : Fints n0 =>
   exist (fun p : I => p <> b (Fints_last n0))
     (b (Fints_coerce (le_n_Sn n0) k)) (bijection_restriction1 Hb k)) as c.
  clear Heqc.
  remember (bijection_restriction2 Hb') as Hc'. clear HeqHc'.
  remember (fun k : Fints n0 =>
   exist (fun p : I => p <> b' (Fints_last n0))
     (b' (Fints_coerce (le_n_Sn n0) k)) (bijection_restriction1 Hb' k)) as c'.
  clear Heqc'.
  destruct (classic (b (Fints_last n0) = b' (Fints_last n0))).
  f_equal. destruct H0. auto. destruct H0. auto. 
  assert (Hbijc : bijection c). auto.
  destruct Hbijc as [Hinjc Hsurjc].
  assert (Hbijc' : bijection c'). auto.
  destruct Hbijc' as [Hinjc' Hsurjc'].
  remember (exist (fun p => p <> b (Fints_last n0)) (b' (Fints_last n0)) (not_eq_sym H0)) as y.
  remember (exist (fun p => p <> b' (Fints_last n0)) (b (Fints_last n0)) H0) as y'.
  destruct (Hsurjc y) as [x Hx].
  destruct (Hsurjc' y') as [x' Hx'].
  destruct n0 as [ | n1'].
  discriminate.
  assert (n1 = n1'). injection Heqn0. auto. destruct H1.
  remember (compose c (exchange _ x (Fints_last n1))) as d.
  assert (Hd : bijection d).
  rewrite Heqd.
  apply bij_compose. auto. apply exchange_bijective.
  assert (prod (S n1) {p : I | p <> b (Fints_last (S n1))} c Hc
  (fun x0 : {p : I | p <> b (Fints_last (S n1))} => f `x0) = 
         prod (S n1) {p : I | p <> b (Fints_last (S n1))} d Hd
  (fun x0 : {p : I | p <> b (Fints_last (S n1))} => f `x0)).
  apply H. rewrite H1.
  remember (compose c' (exchange _ x' (Fints_last n1))) as d'.
  assert (Hd' : bijection d').
  rewrite Heqd'.
  apply bij_compose. auto. apply exchange_bijective.
  assert (prod (S n1) {p : I | p <> b' (Fints_last (S n1))} c' Hc'
  (fun x0 : {p : I | p <> b' (Fints_last (S n1))} => f `x0) = 
         prod (S n1) {p : I | p <> b' (Fints_last (S n1))} d' Hd'
  (fun x0 : {p : I | p <> b' (Fints_last (S n1))} => f `x0)).
  apply H. rewrite H2.
  rewrite prod_elim_last. rewrite prod_elim_last.
  rewrite <- mult_assoc. rewrite mult_com with (y := f (b (Fints_last (S n1)))).
  rewrite mult_assoc. f_equal. f_equal.
  assert (ex_d''1 : forall k : Fints n1, proj1_sig (d' (Fints_coerce (le_n_Sn n1) k)) <> b (Fints_last (S n1))).
  intro k. assert (b (Fints_last (S n1)) = proj1_sig (d' (Fints_last n1))).
  rewrite Heqd'. unfold compose. rewrite exchange_2. rewrite Hx'.
  rewrite Heqy'. auto.
  rewrite H3. apply proj1_inj_neg. apply injection_iff_neg. apply Hd'.
  apply proj1_inj_neg. simpl. destruct k as [k' Hk'].
  simpl. apply lt_not_eq. auto.
  assert (ex_d''2 : forall k : Fints n1,
    (exist (fun p : I => p <> b (Fints_last (S n1)))
                  (proj1_sig (d' (Fints_coerce (le_n_Sn n1) k)))
                  (ex_d''1 k)) <> (d (Fints_last n1))).
  intro k. apply proj1_inj_neg. simpl. rewrite Heqd. unfold compose.
  rewrite exchange_2. rewrite Hx. rewrite Heqy. simpl.
  remember (d' (Fints_coerce (le_n_Sn n1) k)) as l.
  destruct l as [l' Hl']. auto.
  remember (fun k : Fints n1 =>
    exist (fun p : {p : I | p <> b (Fints_last (S n1))} => p <> d (Fints_last n1))
      (exist (fun p : I => p <> b (Fints_last (S n1)))
                  (proj1_sig (d' (Fints_coerce (le_n_Sn n1) k)))
                  (ex_d''1 k))
      (ex_d''2 k)) as d''.
  assert (Hd'' : bijection d'').
  split. intros x1 x2 He. rewrite Heqd'' in He.
  apply proj1_inj in He. simpl in He. apply proj1_inj in He. simpl in He.
  apply proj1_inj in He. apply Hd' in He. unfold Fints_coerce in He.
  apply proj1_inj in He. simpl in He. apply proj1_inj in He. auto. 
  intro y0.
  assert (``y0 <> (b' (Fints_last (S n1)))).
  destruct y0 as [y0' Hy0']. simpl. rewrite Heqd in Hy0'.
  unfold compose in Hy0'.  rewrite exchange_2 in Hy0'. rewrite Hx in Hy0'.
  rewrite Heqy in Hy0'. apply proj1_inj_neg in Hy0'. auto.
  assert (exists x0, d' x0 = exist (fun p => p <> b' (Fints_last (S n1))) ``y0 H3).
  apply Hd'. destruct H4 as [x0 H4].
  destruct x0 as [x0' Hx0'].
  assert (x0' <= n1). apply le_S_n. auto.
  apply le_lt_or_eq in H5. destruct H5.
  exists (exist (fun p => p < n1) x0' H5).
  rewrite Heqd''. apply proj1_inj. simpl. apply proj1_inj. simpl.
  apply proj1_inj in H4. simpl in H4. rewrite <- H4. 
  apply proj1_inj. f_equal. unfold Fints_coerce. apply proj1_inj. auto.
  destruct y0 as [y0' Hy0']. destruct y0' as [y0'' Hy0''].
  simpl in *. apply proj1_inj in H4. simpl in H4. exfalso.
  clear Hy0'. rewrite <- H4 in Hy0''. clear H4. clear H3.
  rewrite Heqd' in Hy0''. unfold compose in Hy0''.
  assert ((Fints_last n1) = (exist (fun p : nat => p < S n1) x0' Hx0')).
  unfold Fints_last. apply proj1_inj. auto.
  clear H5. rewrite H3 in Hy0''. rewrite exchange_2 in Hy0''.
  rewrite Hx' in Hy0''. rewrite Heqy' in Hy0''. auto.
  rewrite H' with (b' := d'') (Hb' := Hd'').
  repeat (unfold prod). apply pr_ext.
  intro k. f_equal. simpl. rewrite Heqd''. auto.
  rewrite Heqd'. unfold compose. unfold exchange.
  assert ((If Fints_last n1 = x' then Fints_last n1
     else (If Fints_last n1 = Fints_last n1 then x' else Fints_last n1)) = x').
  case_if. auto. apply If_l. auto. rewrite H3. rewrite Hx'.
  rewrite Heqy'. simpl. auto.
  f_equal. rewrite Heqd. unfold compose. unfold exchange.
  assert ((If Fints_last n1 = x then Fints_last n1
     else (If Fints_last n1 = Fints_last n1 then x else Fints_last n1)) = x).
  case_if. auto. apply If_l. auto. rewrite H3. rewrite Hx.
  rewrite Heqy. simpl. auto.
Qed.

Theorem prod_unique :
  forall (I : Type) (f : I -> T)
         (n  : nat) (b  : Fints n  -> I) (Hb  : bijection b )
         (n' : nat) (b' : Fints n' -> I) (Hb' : bijection b'),
  prod n I b Hb f = prod n' I b' Hb' f.
Proof.
  intros.
  assert (n = n').
  apply cardinality_unique with (T := I).
  unfold cardinality. apply inv_bijection. exists b. auto.
  unfold cardinality. apply inv_bijection. exists b'. auto.
  destruct H. apply prod_unique_n.
Qed.

Lemma product_exists (I : Type) (H : finite I) (f : I -> T) :
  exists ! p : T,
    (forall (n : nat) (b : Fints n -> I) (Hb : bijection b), p = prod n I b Hb f).
Proof.
  apply unique_existence with (P := fun p =>
    forall (n : nat) (b : Fints n -> I) (Hb : bijection b), p = prod n I b Hb f).
  destruct H as [n H]. apply inv_bijection in H. destruct H as [b Hb].
  split.
  exists (prod n I b Hb f). apply prod_unique.
  intros p1 p2 H1 H2.
  transitivity (prod n I b Hb f). auto. auto.
Qed.

Definition product (I : Type) (H : finite I) (f : I -> T) :=
  proj1_sig (constructive_definite_description (fun p =>
    forall (n : nat) (b : Fints n -> I) (Hb : bijection b), p = prod n I b Hb f)
  (product_exists I H f)).

Lemma product_any (I : Type) (H : finite I) (f : I -> T)
    (n : nat) (b : Fints n -> I) (Hb : bijection b) :
  product I H f = prod n I b Hb f.
Proof.
  unfold product.
  remember (constructive_definite_description
    (fun p : T =>
     forall (n0 : nat) (b0 : Fints n0 -> I) (Hb0 : bijection b0),
     p = prod n0 I b0 Hb0 f) (product_exists I H f)) as p.
  destruct p. simpl. apply e0.
Qed.

Lemma product_ext (I : Type) (H : finite I) (f g : I -> T) :
  (forall i: I, f i = g i) -> product I H f = product I H g.
Proof.
  assert (finite I). auto.
  destruct H0 as [n H0]. apply inv_bijection in H0. destruct H0 as [b Hb].
  intro He. repeat (rewrite (product_any I H _ n b Hb)). unfold prod.
  apply pr_ext. auto.
Qed.

Lemma product_n (n : nat) (f : Fints (S n) -> T) :
  product _ (Fints_finite (S n)) f = product _ (Fints_finite n)
    (fun k => f (Fints_coerce (le_n_Sn n) k)) * f (Fints_last n).
Proof.
  rewrite (product_any (Fints (S n)) (Fints_finite (S n)) f
           (S n) (fun x => x) (id_bijection (Fints (S n)))).
  rewrite (product_any (Fints n) (Fints_finite n)
          (fun k => f (Fints_coerce (le_n_Sn n) k))
           n (fun x => x) (id_bijection (Fints n))).
  unfold prod. simpl. f_equal.
  apply pr_ext. intro k. f_equal. unfold Fints_coerce.
  apply proj1_inj. auto.
  f_equal. unfold Fints_last. apply proj1_inj. auto.
Qed.

Lemma product_bij (I : Type) (HI : finite I) (f : I -> T)
                  (J : Type) (HJ : finite J) (b : J -> I) (Hb : bijection b) :
  product I HI f = product J HJ (compose f b).
Proof.
  assert (exists n, exists a : Fints n -> J, bijection a).
  destruct HJ as [n HJ]. exists n. apply inv_bijection in HJ.
  destruct HJ as [a Ha]. exists a. auto.
  destruct H as [n H]. destruct H as [a Ha].
  rewrite (product_any I HI f n (compose b a) (bij_compose Hb Ha)).
  rewrite (product_any J HJ (compose f b) n a Ha).
  unfold prod. unfold compose. auto.
Qed.

Lemma empty_product (f : Fints 0 -> T) :
  product _ (Fints_finite 0) f = e.
Proof.
  rewrite (product_any _ _ _ _ (fun x => x) (id_bijection _)).
  unfold prod. auto.
Qed.

Lemma product_e_neutral_n (n : nat) (f : Fints n -> T) :
  e * (product _ (Fints_finite n) f) = product _ (Fints_finite n) f.
Proof.
  destruct n as [ | n'].
  rewrite empty_product. apply e_idemp.
  rewrite product_n. apply e_img_neutral.
Qed.

Lemma product_e_neutral (I : Type) (HI : finite I) (f : I -> T) :
  e * (product I HI f) = product I HI f.
Proof.
  assert (finite I). auto.
  destruct H as [n H]. apply inv_bijection in H. destruct H as [b Hb].
  repeat (rewrite (product_bij I HI _ (Fints n) (Fints_finite n) b Hb)).
  apply product_e_neutral_n.
Qed.

Lemma product_mul_n :
  forall (n : nat) (f g : (Fints n) -> T),
    product _ (Fints_finite n) (fun k => f k * g k) =
    product _ (Fints_finite n) f * product _ (Fints_finite n) g.
Proof.
  simple induction n.
  intros f g.
  repeat (rewrite empty_product).
  symmetry. apply e_idemp.
  intros n0 H f g.
  repeat (rewrite product_n). rewrite H.
  repeat (rewrite mult_assoc). f_equal. repeat (rewrite <- mult_assoc). f_equal.
  apply mult_com.
Qed.

Lemma product_mul (I : Type) (HI : finite I) (f g : I -> T) :
  product I HI (fun x => f x * g x) =
  product I HI f * product I HI g.
Proof.
  assert (finite I). auto.
  destruct H as [n H]. apply inv_bijection in H. destruct H as [b Hb].
  repeat (rewrite (product_bij I HI _ (Fints n) (Fints_finite n) b Hb)).
  rewrite <- product_mul_n. unfold compose. auto.
Qed.

Lemma product_property_conservation_n (P : T -> Prop)
    (Hc : forall x y : T, P x -> P y -> P (x * y)) (He : P e) :
  forall (n : nat) (f : (Fints n) -> T),
    (forall k : Fints n, P (f k)) -> P (product _ (Fints_finite n) f).
Proof.
  simple induction n. intros. rewrite empty_product. apply He.
  intros n0 H f HP.
  rewrite product_n. apply Hc. apply H. auto. auto.
Qed.
Lemma product_property_conservation (P : T -> Prop)
    (Hc : forall x y : T, P x -> P y -> P (x * y)) (He : P e)
    (I : Type) (HI : finite I) (f : I -> T) :
  (forall x, P (f x)) -> P (product I HI f).
Proof.
  assert (finite I). auto.
  destruct H as [n H]. apply inv_bijection in H. destruct H as [b Hb].
  repeat (rewrite (product_bij I HI _ (Fints n) (Fints_finite n) b Hb)).
  intro H. apply product_property_conservation_n. auto. auto.
  unfold compose. auto.
Qed.

Lemma product_eq_n (R : T -> T -> Prop)
    (Hc : forall x1 x2 y1 y2 : T, R x1 x2 -> R y1 y2 -> R (x1 * y1) (x2 * y2))
    (He : R e e) :
  forall (n : nat) (f g : (Fints n) -> T), 
    (forall k : (Fints n), R (f k) (g k)) ->
      R (product _ (Fints_finite n) f) (product _ (Fints_finite n) g).
Proof.
  simple induction n.
  intros. repeat (rewrite empty_product). auto.
  intros n0 H f g Heq.
  repeat (rewrite product_n). apply Hc. apply H. auto. auto.
Qed.
Lemma product_eq (R : T -> T -> Prop)
    (Hc : forall x1 x2 y1 y2 : T, R x1 x2 -> R y1 y2 -> R (x1 * y1) (x2 * y2))
    (He : R e e)
    (I : Type) (HI : finite I) (f g : I -> T) :
  (forall x, R (f x) (g x)) -> R (product I HI f) (product I HI g).
Proof.
  assert (finite I). auto.
  destruct H as [n H]. apply inv_bijection in H. destruct H as [b Hb].
  repeat (rewrite (product_bij I HI _ (Fints n) (Fints_finite n) b Hb)).
  intro H. apply product_eq_n. auto. auto. unfold compose. auto.
Qed.

Lemma product_split_ex1 (n m : nat) (k : Fints n) :
  `k < n + m.
Proof.
  destruct k as [k' Hk']. simpl. omega.
Qed.
Lemma product_split_ex2 (n m : nat) (k : Fints m) :
  `k + n < n + m.
Proof.
  destruct k as [k' Hk']. simpl. omega.
Qed.

Lemma product_split_n :
  forall (n : nat) (m : nat) (f : (Fints (n + m)) -> T),
    product _ (Fints_finite (n + m)) f =
  (product _ (Fints_finite n) (fun k => f (exist _ `k (product_split_ex1 n m k)))) *
  (product _ (Fints_finite m) (fun k => f (exist _ (`k + n) (product_split_ex2 n m k)))).
Proof.
  simple induction m.
  intro f. rewrite empty_product.
  rewrite mult_com. rewrite product_e_neutral.
  remember (product_split_ex1 n 0) as H.
  clear HeqH.
  generalize f. generalize H. rewrite <- plus_n_O.
  intros. apply product_ext. intro. f_equal. apply proj1_inj. auto.
  intros m0 H. remember (product_split_ex1 n (S m0)) as H1.
  remember (product_split_ex2 n (S m0)) as H2.
  clear HeqH1. clear HeqH2. generalize H1 H2.
  rewrite <- plus_n_Sm. intros.
  repeat (rewrite product_n). rewrite mult_assoc. f_equal.
  rewrite H. f_equal.
  apply product_ext. intro. f_equal. unfold Fints_coerce.
  apply proj1_inj. auto.
  apply product_ext. intro. f_equal. unfold Fints_coerce.
  apply proj1_inj. auto.
  f_equal. unfold Fints_last. apply proj1_inj. simpl. apply plus_comm.
Qed.

Lemma product_split (I : Type) (HI : finite I) (f : I -> T) (P : I -> Prop) :
  product I HI f =
   (product {x : I | P x} (subtype_finite HI _) (fun x => f `x)) * 
   (product {x : I | ~ P x} (subtype_finite HI _) (fun x => f `x)).
Proof.
  assert (Hn : finite {x : I | P x}). apply subtype_finite. auto.
  destruct Hn as [n Hn]. apply inv_bijection in Hn. destruct Hn as [b Hb].
  assert (Hm : finite {x : I | ~ P x}). apply subtype_finite. auto.
  destruct Hm as [m Hm]. apply inv_bijection in Hm. destruct Hm as [c Hc].
  remember (choose_bijection P Hb Hc) as a.
  assert (Ha : bijection a). rewrite Heqa. apply choose_bij.
  rewrite (product_bij _ _ _ _ (Fints_finite (n + m)) a Ha).
  rewrite (product_bij _ _ _ _ (Fints_finite n) b Hb).
  rewrite (product_bij _ _ _ _ (Fints_finite m) c Hc).
  rewrite product_split_n.
  f_equal.
  apply product_ext. intro k. unfold compose.
  f_equal. rewrite Heqa. unfold choose_bijection. simpl.
  destruct k as [k' Hk']. simpl.
  destruct (excluded_middle_informative (k' < n)).
  f_equal. f_equal. apply proj1_inj. auto.
  contradiction.
  apply product_ext. intro k. unfold compose.
  f_equal. rewrite Heqa. unfold choose_bijection. simpl.
  destruct k as [k' Hk']. simpl.
  destruct (excluded_middle_informative (k' + n < n)).
  omega.
  f_equal. f_equal. apply proj1_inj. simpl. omega.
Qed.

Variable a : T.
Hypothesis integral : forall x y : T, x <> a -> y <> a -> x * y <> a.
Hypothesis e_not_a : e <> a.

Lemma product_integral (I : Type) (HI : finite I) (f : I -> T) :
  (forall x, f x <> a) -> product I HI f <> a.
Proof.
  intro H.
  apply product_property_conservation. auto. auto. auto.
Qed.

End Acc.

Section Acc_morph.
Variable T : Type.
Variable multT : T -> T -> T.
Infix "*" := multT.
Hypothesis multT_com :
  forall x y : T, x * y = y * x.
Hypothesis multT_assoc :
  forall x y z : T, x * (y * z) = (x * y) * z.
Variable eT : T.
Variable S : Type.
Variable multS : S -> S -> S.
Infix "×" := multS (at level 40).
Hypothesis multS_com :
  forall x y : S, x × y = y × x.
Hypothesis multS_assoc :
  forall x y z : S, x × (y × z) = (x × y) × z.
Variable eS : S.
Variable morph : T -> S.
Hypothesis morphism :
  forall x y : T, morph (x * y) = morph x × morph y.
Hypothesis morph_e :
  morph eT = eS.

Lemma product_morph_n :
  forall (n : nat) (f : (Fints n) -> T),
    morph (product T multT multT_com multT_assoc eT _ (Fints_finite n) f) =
    product S multS multS_com multS_assoc eS _ (Fints_finite n) (compose morph f).
Proof.
  simple induction n.
  intro f.
  repeat (rewrite empty_product). apply morph_e.
  intros n0 H f.
  repeat (rewrite product_n). rewrite morphism.
  unfold compose. f_equal. rewrite H. unfold compose. auto.
Qed.

Lemma product_morph (I : Type) (HI : finite I) (f : I -> T) :
    morph (product T multT multT_com multT_assoc eT I HI f) =
    product S multS multS_com multS_assoc eS I HI (compose morph f).
Proof.
  assert (finite I). auto.
  destruct H as [n H]. apply inv_bijection in H. destruct H as [b Hb].
  repeat (rewrite (product_bij _ _ _ _ _ I HI _ (Fints n) (Fints_finite n) b Hb)).
  apply product_morph_n.
Qed.

End Acc_morph.

Lemma disjoint_union_cardinality_sum_n :
  forall (n : nat) (T : Type) (f : T -> Fints n) (c : Fints n -> nat),
    (forall k : Fints n, cardinality {x : T | f x = k} (c k)) ->
       cardinality T (product nat plus plus_comm plus_assoc 0 _ (Fints_finite n) c).
Proof.
  simple induction n.
  intros. rewrite empty_product. exists f. split.
  intro x. destruct (f x). exfalso. omega.
  intro y. destruct y. exfalso. omega.
  intros n0 H T f c Hc.
  rewrite product_n.
  assert (cardinality {x : T | f x = Fints_last n0} (c (Fints_last n0))). auto.
  assert (cardinality {x : T | ~ (f x = Fints_last n0)} (product nat plus plus_comm plus_assoc 0 (Fints n0) (Fints_finite n0)
     (fun k : Fints n0 => c (Fints_coerce (le_n_Sn n0) k)))).
  assert (forall x : {x : T | f x <> Fints_last n0}, proj1_sig (f `x) < n0).
  intro x. destruct x as [x' Hx']. simpl.
  assert (proj1_sig (f x') < S n0). destruct (f x'). auto.
  assert (proj1_sig (f x') <> n0). apply proj1_inj_neg in Hx'.
  unfold Fints_last in Hx'. simpl in Hx'. auto. omega.
  apply H with (f := fun x => exist _ (proj1_sig (f `x)) (H1 x)).
  intro k.
  destruct (Hc (Fints_coerce (le_n_Sn n0) k)) as [b Hb].
  assert (forall x : {x : {x : T | f x <> Fints_last n0} |
    exist (fun p : nat => p < n0) (proj1_sig (f `x)) (H1 x) = k}, f ``x = Fints_coerce (le_n_Sn n0) k).
  intro x. destruct x as [x' Hx']. destruct x' as [x'' Hx''].
  simpl in *. unfold Fints_coerce. apply proj1_inj. simpl.
  rewrite <- Hx'. simpl. auto.
  exists (fun x => b (exist _ ``x (H2 x))).
  destruct Hb as [Hbinj Hbsurj].
  split.
  intros x1 x2 He. apply Hbinj in He. apply proj1_inj in He. simpl in He.
  apply proj1_inj in He. apply proj1_inj. auto.
  intro y. destruct (Hbsurj y) as [x Hx]. destruct x as [x' Hx'].
  assert (f x' <> Fints_last n0). unfold Fints_last. rewrite Hx'.
  unfold Fints_coerce. apply proj1_inj_neg. simpl. destruct k. simpl. omega.
  assert (exist _ (proj1_sig (f (proj1_sig (exist _ x' H3)))) (H1 (exist _ x' H3)) = k).
  apply proj1_inj. simpl. rewrite Hx'. unfold Fints_coerce. auto.
  exists (exist _ (exist _ x' H3) H4).
  simpl. rewrite <- Hx. f_equal. apply proj1_inj. auto.
  rewrite (plus_comm _ (c (Fints_last n0))).
  apply disjoint_union_cardinality with (P := fun x => f x = Fints_last n0).
  auto. auto.
Qed.

Lemma disjoint_union_cardinality_sum (I T : Type) (HI : finite I) (f : T -> I) (c : I -> nat) :
    (forall i : I, cardinality {x : T | f x = i} (c i)) ->
       cardinality T (product nat plus plus_comm plus_assoc 0 I HI c).
Proof.
  intro H.
  assert (finite I). auto.
  destruct H0 as [n H0]. destruct H0 as [b Hb].
  assert (Hb' : inversible b). apply bijection_inversible. auto.
  destruct Hb' as [b' Hb']. destruct Hb' as [Hb'id Hbid].
  assert (Hb' : bijection b'). apply bijection_inversible. exists b. auto.
  rewrite (product_bij _ _ _ _ _ I HI _ (Fints n) (Fints_finite n) b' Hb').
  apply disjoint_union_cardinality_sum_n with (f := fun x => b (f x)).
  intro k.
  apply (card_subtype (fun x => b (f x) = k) (fun x => f x = b' k)).
  intro x. split. intro He. rewrite <- (Hb'id (f x)). f_equal. auto.
  intro He. rewrite <- (Hbid k). f_equal. auto.
  unfold compose. auto.
Qed.

End Accum.