Require Import ZArith.
Require Import Zhints.
Require Import Zpow_facts.
Require Import BinInt. Import Z.
Require Import Znat.
Require Import Zeuclid. Import ZEuclid.
Require Import Znumtheory.
Require Import Finite. Import FiniteTypes.
Require Import Accumulation. Import Accum.
Require Import Classical.

Lemma Zpos_induction (P : Z -> Prop) :
  P 0 ->
  (forall n : Z, 0 <= n -> P n -> P (succ n)) ->
  (forall n : Z, 0 <= n -> P n).
Proof.
  intros P0 Psucc.
  assert (forall n : nat, P (Z.of_nat n)).
  simple induction n. auto.
  intro n0. rewrite Nat2Z.inj_succ. apply Psucc. apply Nat2Z.is_nonneg.
  intros n Hpos. rewrite <- Z2Nat.id by auto. apply H.
Qed.

Lemma prime_divide_pow :
  forall x p n : Z, 0 <= n -> prime p -> (p | x ^ n) -> (p | x).
Proof.
  intros x p.
  apply (Zpos_induction (fun n => prime p -> (p | x ^ n) -> (p | x))).
  simpl. intros _ H. destruct H. exists (x * x0). rewrite <- Zmult_assoc.
  rewrite <- H. omega.
  intros n Hpos Hrec Hprime Hdiv.
  rewrite pow_succ_r in Hdiv by auto. apply prime_mult in Hdiv.
  destruct Hdiv. auto. auto. auto.
Qed.

Lemma power_plus :
  forall x m n, 0 <= n -> 0 <= m -> x ^ (n + m) = x ^ n * x ^ m.
Proof.
  intros x m.
  apply (Zpos_induction (fun n => 0 <= m -> x ^ (n + m) = x ^ n * x ^ m)).
  intro H. rewrite pow_0_r. rewrite mul_1_l. auto.
  intros n Hnpos Hrec Hmpos.
  rewrite add_succ_l. rewrite pow_succ_r. rewrite pow_succ_r by auto.
  rewrite <- Zmult_assoc. f_equal. auto. omega.
Qed.

Lemma one_pow :
  forall n, 0 <= n -> 1 ^ n = 1.
Proof.
  apply (Zpos_induction (fun n => 1 ^ n = 1)).
  auto. intros n Hpos Hrec. rewrite pow_succ_r by auto. rewrite Hrec. omega.
Qed.

Lemma power_power :
  forall x m n, 0 <= n -> 0 <= m -> (x ^ n) ^ m = x ^ (n * m).
Proof.
  intros x m.
  apply (Zpos_induction (fun n => 0 <= m -> (x ^ n) ^ m = x ^ (n * m))).
  intro. simpl. apply one_pow. auto.
  intros n Hnpos Hrec Hmpos. rewrite pow_succ_r by auto.
  rewrite Zmult_power by auto. rewrite Zmult_succ_l.
  rewrite power_plus. rewrite Zmult_comm. f_equal.
  auto. rewrite <- mul_0_l with (n := m).
  apply Zmult_le_compat_r. auto. auto. auto.
Qed.

Lemma minus_one_pow_even :
  forall n : Z, 0 <= n -> Even n -> (-1) ^ n = 1.
Proof.
  intros n Hpos Heven. destruct Heven.
  rewrite H.
  rewrite <- power_power by omega. apply one_pow. omega.
Qed.

Lemma minus_one_pow_odd :
  forall n : Z, 0 <= n -> Odd n -> (-1) ^ n = -1.
Proof.
  intros n Hpos Hodd. destruct Hodd.
  rewrite H. rewrite power_plus by omega.
  rewrite <- power_power by omega. rewrite one_pow. auto. omega.
Qed.  

Lemma even_mod :
  forall n : Z, Even n <-> n mod 2 = 0.
Proof.
  intro n. split.
  intro Heven. destruct Heven. rewrite H. rewrite Zmult_mod.
  auto.
  intro Hmod. exists (n / 2). apply Z_div_exact_2. omega. auto.
Qed.

Lemma odd_mod :
  forall n : Z, Odd n <-> n mod 2 = 1.
Proof.
  intro n. split.
  intro Hodd. destruct Hodd. rewrite H. rewrite Zplus_comm.
  rewrite Zmult_comm. rewrite Z_mod_plus_full. auto.
  intro Hmod. exists (n / 2). rewrite <- Hmod. apply Z_div_mod_eq.
  omega.
Qed.

Lemma even_or_odd n :
  Even n \/ Odd n.
Proof.
  rewrite <- Zeven_equiv. rewrite <- Zodd_equiv.
  destruct (Zeven_odd_dec n). auto. auto.
Qed.

Lemma minus_one_pow_mod_2 :
  forall n m : Z, 0 <= n -> 0 <= m -> ((-1) ^ n = (-1) ^ m <-> n mod 2 = m mod 2).
Proof.
  intros n m Hnpos Hmpos.
  destruct (even_or_odd n). assert (n mod 2 = 0). apply even_mod. auto.
  rewrite H0. rewrite minus_one_pow_even; [ | omega | auto].
  destruct (even_or_odd m). assert (m mod 2 = 0). apply even_mod. auto.
  rewrite H2. rewrite minus_one_pow_even; [ | omega | auto].
  tauto.
  assert (m mod 2 = 1). apply odd_mod. auto.
  rewrite H2. rewrite minus_one_pow_odd; [ | omega | auto].
  split. intro. discriminate. intro. discriminate.
  assert (n mod 2 = 1). apply odd_mod. auto.
  rewrite H0. rewrite minus_one_pow_odd; [ | omega | auto].
  destruct (even_or_odd m). assert (m mod 2 = 0). apply even_mod. auto.
  rewrite H2. rewrite minus_one_pow_even; [ | omega | auto].
  split. intro. discriminate. intro. discriminate.
  assert (m mod 2 = 1). apply odd_mod. auto.
  rewrite H2. rewrite minus_one_pow_odd; [ | omega | auto].
  tauto.
Qed.

Definition m1_pow (n : Z) := -2 * (n mod 2) + 1.
Lemma m1_pow_1_or_m1 :
  forall n : Z, m1_pow n = 1 \/ m1_pow n = -1.
Proof.
  intro n.
  destruct (even_or_odd n).
  left. unfold m1_pow. assert (n mod 2 = 0). apply even_mod. auto. omega.
  right. unfold m1_pow. assert (n mod 2 = 1). apply odd_mod. auto. omega.
Qed.
Lemma m1_pow_compatible :
  forall n : Z, n >= 0 -> (-1) ^ n = m1_pow n.
Proof.
  intros n H. destruct (even_or_odd n).
  rewrite minus_one_pow_even by (omega || auto).
  unfold m1_pow. assert (n mod 2 = 0). apply even_mod. auto. omega.
  rewrite minus_one_pow_odd by (omega || auto).
  unfold m1_pow. assert (n mod 2 = 1). apply odd_mod. auto. omega.
Qed.
Lemma m1_pow_morphism :
  forall n m : Z, m1_pow (n + m) = m1_pow n * m1_pow m.
Proof.
  intros n m. unfold m1_pow. rewrite Zplus_mod.
  destruct (even_or_odd n). assert (n mod 2 = 0). apply even_mod. auto. repeat (rewrite H0).
  destruct (even_or_odd m). assert (m mod 2 = 0). apply even_mod. auto. repeat (rewrite H2).
  auto. assert (m mod 2 = 1). apply odd_mod. auto. repeat (rewrite H2). auto.
  assert (n mod 2 = 1). apply odd_mod. auto. repeat (rewrite H0).
  destruct (even_or_odd m). assert (m mod 2 = 0). apply even_mod. auto. repeat (rewrite H2).
  auto. assert (m mod 2 = 1). apply odd_mod. auto. repeat (rewrite H2). auto.
Qed.

Lemma minus_mod :
  forall n m, 0 < n < m -> (-n) mod m = m - n.
Proof.
  intros n m H.
  assert (0 < m). omega.
  assert (0 <= m - n < m). split. omega. omega.
  assert ((m - n) mod m = m - n).
  apply Zmod_small. auto.
  rewrite <- H2. rewrite <- Zminus_mod_idemp_l.
  rewrite Z_mod_same. auto. omega.
Qed.

Lemma mod_eq_div :
  forall a b n, n <> 0 -> (a mod n = b mod n <-> (n | a - b)).
Proof.
  intros a b n Hnnz.
  split.
  intro H. apply Zmod_divide. auto. rewrite Zminus_mod.
  rewrite H. rewrite Zminus_diag. auto.
  intro H. destruct H.
  assert (a = b + x * n). omega.
  rewrite H0. apply Z_mod_plus_full.
Qed.

Lemma not_0_inversible_mod_p :
  forall a p, prime p -> a mod p <> 0 -> exists b, (b * a) mod p = 1.
Proof.
  intros a p Hprime Hanz.
  assert (rel_prime p a).
  apply prime_rel_prime. auto. intro H. apply Zdivide_mod in H. contradiction.
  apply rel_prime_bezout in H. destruct H.
  exists v. assert ((u * p + v * a) mod p = 1 mod p). f_equal. auto.
  rewrite Zmod_1_l in H0 by (destruct Hprime; omega).
  rewrite <- Zplus_mod_idemp_l in H0.
  rewrite Zmult_mod in H0. rewrite Z_mod_same in H0 by (destruct Hprime; omega).
  rewrite Zmult_0_r in H0. rewrite Zmod_0_l in H0. auto.
Qed.

Lemma simpl_mod_p :
  forall a b c p, prime p -> a mod p <> 0 -> (a * b) mod p = (a * c) mod p -> b mod p = c mod p.
Proof.
  intros a b c p Hprime Hanz Heq.
  destruct (not_0_inversible_mod_p a p Hprime Hanz).
  assert (((x * a) mod p * b) mod p = ((x * a) mod p * c) mod p).
  repeat (rewrite Zmult_mod_idemp_l). repeat (rewrite <- Zmult_assoc).
  rewrite <- Zmult_mod_idemp_r. rewrite Heq. rewrite Zmult_mod_idemp_r. auto.
  repeat (rewrite H in H0). repeat (rewrite mul_1_l in H0). auto. 
Qed.

Lemma over_2 : 
  forall a, a mod 2 = 1 -> (a - 1) / 2 = a / 2.
Proof.
  intros a Hodd.
  apply mul_reg_l with (p := 2). omega.
  assert (2 * ((a - 1) / 2) = a - 1 - (a - 1) mod 2).
  rewrite Zmod_eq_full. omega. omega.
  assert (2 * (a / 2) = a - a mod 2).
  rewrite Zmod_eq_full. omega. omega.
  rewrite H. rewrite H0. rewrite Hodd. rewrite <- Zminus_mod_idemp_l.
  rewrite Hodd. simpl. rewrite Zmod_0_l. omega.
Qed.

Section Z_over_pZ.
Variable p : Z.
Hypothesis p_prime : prime p.
Definition ZpZmult (x y : Z) := (x *  y) mod p.
Lemma ZpZmult_comm :
  forall (x y : Z), ZpZmult x y = ZpZmult y x.
Proof.
  intros. unfold ZpZmult. rewrite Zmult_comm. auto.
Qed.
Lemma ZpZmult_assoc :
  forall (x y z : Z), ZpZmult x (ZpZmult y z) = ZpZmult (ZpZmult x y) z.
Proof.
  intros. unfold ZpZmult.
  rewrite Zmult_mod_idemp_l. rewrite Zmult_mod_idemp_r. rewrite Zmult_assoc.
  auto.
Qed.
Lemma one_idemp :
  ZpZmult 1 1 = 1.
Proof.
  unfold ZpZmult. simpl. apply Zmod_1_l. destruct p_prime. omega.
Qed.
Lemma mod_1_mod :
  forall x y : Z, ZpZmult x y = ZpZmult (ZpZmult x y) 1.
Proof.
  intros x y. unfold ZpZmult.
  rewrite Zmult_1_r. symmetry. apply Zmod_mod.
Qed.
End Z_over_pZ.

Lemma card_interval_full :
  forall a b : Z, a <= b + 1 -> 
    cardinality {u : Z | a <= u <= b} (Z.to_nat (b - a + 1)).
Proof.
  intros a b Hsmall.
  assert (forall u : {u : Z | a <= u <= b}, (Z.to_nat (`u - a) < Z.to_nat (b - a + 1))%nat).
  intro u. destruct u as [u' Hu']. simpl.
  apply Z2Nat.inj_lt. omega. omega. omega.
  exists (fun u => exist _ (Z.to_nat (`u - a)) (H u)).
  apply bijection_inversible.
  assert (forall x : {x : nat | (x < Z.to_nat (b - a + 1)) % nat}, a <= a + Z.of_nat `x <= b).
  intro x. destruct x as [x' Hx']. unfold proj1_sig.
  assert (0 <= Z.of_nat x' < b - a + 1). split. apply Nat2Z.is_nonneg.
  apply Nat2Z.inj_lt in Hx'. rewrite Z2Nat.id in Hx'. auto. omega.
  omega.
  exists (fun x => exist _ (a + Z.of_nat `x) (H0 x)).
  split.
  intro x. destruct x as [x' Hx']. apply proj1_inj. unfold proj1_sig.
  rewrite Z2Nat.id. omega. omega.
  intro y. destruct y as [y' Hy']. apply proj1_inj. unfold proj1_sig.
  rewrite <- Nat2Z.id. f_equal. omega.
Qed.

Lemma card_interval :
  forall a b : Z, a <= b -> 
    cardinality {u : Z | a <= u <= b} (Z.to_nat (b - a + 1)).
Proof.
  intros a b H.
  apply card_interval_full. omega.
Qed.

Section FLT.
Variable p : Z.
Hypothesis p_prime : prime p.
Variable a : Z.
Hypothesis a_not_0 : a mod p <> 0.

Let f (u : {u : Z | 1 <= u <= p - 1}) := (a * `u) mod p.
Let f'_exists :
  forall u, 1 <= f u <= p - 1.
Proof with ((destruct p_prime; omega) || auto).
  intro u. destruct u as [u' Hu']. unfold f. simpl.
  assert (0 <= (a * u' mod p) < p).
  apply mod_pos_bound...
  assert (a * u' mod p <> 0).
  intro H1. apply Zmod_divide in H1... apply prime_mult in H1...
  destruct H1. apply Zdivide_mod in H0. contradiction.
  apply Zdivide_mod in H0. rewrite Zmod_small in H0...
  omega.
Qed.
Let f' u := exist (fun k => 1 <= k <= p - 1) (f u) (f'_exists u).
Let f'_injective :
  injection f'.
Proof.
  intros u1 u2 H. destruct u1 as [u1' Hu1']. destruct u2 as [u2' Hu2'].
  unfold f' in H. apply proj1_inj in H. simpl in H.
  apply proj1_inj. simpl. unfold f in H. simpl in H.
  apply simpl_mod_p in H. repeat (rewrite Zmod_small in H by omega). auto.
  auto. auto.
Qed.
Let f'_surjective :
  surjection f'.
Proof with ((destruct p_prime; omega) || auto).
  intro y. destruct y as [y' Hy'].
  destruct (not_0_inversible_mod_p a p p_prime a_not_0) as [a' Ha'].
  assert (1 <= (a' * y') mod p <= p - 1).
  assert (0 <= (a' * y') mod p < p). apply mod_pos_bound...
  assert ((a' * y') mod p <> 0). intro H1.
  assert ((a * (a' * y')) mod p = 0). rewrite Zmult_mod. rewrite H1.
  rewrite Zmult_0_r. rewrite Zmod_0_l. auto.
  rewrite Zmult_assoc in H0. rewrite Zmult_comm with (m := a') in H0.
  rewrite <- Zmult_mod_idemp_l in H0. rewrite Ha' in H0.
  rewrite Zmult_1_l in H0. rewrite Zmod_small in H0. omega. omega.
  omega.
  exists (exist _ ((a' * y') mod p) H).
  unfold f'. unfold f. simpl. apply proj1_inj. simpl.
  rewrite Zmult_mod_idemp_r. rewrite Zmult_assoc. rewrite Zmult_comm with (m := a').
  rewrite <- Zmult_mod_idemp_l. rewrite Ha'. rewrite Zmult_1_l.
  apply Zmod_small. omega.
Qed.
Let card_U :
  cardinality {u : Z | 1 <= u <= p - 1} (Z.to_nat (p - 1)).
Proof.
  assert (cardinality {u : Z | 1 <= u <= p - 1} (Z.to_nat (p - 1 - 1 + 1))).
  apply card_interval. destruct p_prime; omega.
  assert (p - 1 - 1 + 1 = p - 1). omega. rewrite H0 in H. auto.
Qed.
Let U_finite :
  finite {u : Z | 1 <= u <= p - 1}.
Proof.
  exists (Z.to_nat (p - 1)). apply card_U.
Qed.

Let P' := product Z (ZpZmult p) (ZpZmult_comm p) (ZpZmult_assoc p) 1 _  U_finite (fun x => `x).
Let P'_not_0 :
  P' mod p <> 0.
Proof.
  unfold P'. apply product_property_conservation.
  intros x y Hxnz Hynz. unfold ZpZmult. rewrite Zmod_mod.
  intro H. apply Zmod_divide in H. apply prime_mult in H.
  destruct H. apply Zdivide_mod in H. contradiction. apply Zdivide_mod in H. contradiction.
  auto. destruct p_prime; omega. rewrite Zmod_1_l. omega. destruct p_prime; omega.
  intro x. destruct x. simpl.  rewrite Zmod_small. omega. omega.
Qed.
Let P'1 :
  product Z (ZpZmult p) (ZpZmult_comm p) (ZpZmult_assoc p) 1 _  U_finite (compose (proj1_sig (P := fun k => 1 <= k <= p - 1)) f') = 
  (ZpZmult p) (product Z (ZpZmult p) (ZpZmult_comm p) (ZpZmult_assoc p) 1 _  U_finite (fun x => `x))
              (product Z (ZpZmult p) (ZpZmult_comm p) (ZpZmult_assoc p) 1 _  U_finite (fun x => a)).
Proof.
  unfold compose. unfold f'. simpl.
  rewrite <- product_mul. apply product_ext.
  intro i. unfold f. unfold ZpZmult. f_equal. apply Zmult_comm.
  apply one_idemp. auto.
Qed.
Let P'2 :
  product Z (ZpZmult p) (ZpZmult_comm p) (ZpZmult_assoc p) 1 _  U_finite (compose (proj1_sig (P := fun k => 1 <= k <= p - 1)) f') = P'.
Proof.
  unfold P'. rewrite <- product_bij with (b := f') (HI := U_finite). auto.
  split. apply f'_injective. apply f'_surjective.
Qed.
Let P'3 :
  (product Z (ZpZmult p) (ZpZmult_comm p) (ZpZmult_assoc p) 1 _  U_finite (fun x => a)) mod p = (a ^ (p - 1)) mod p.
Proof.
  assert (cardinality {u : Z | 1 <= u <= p - 1} (Z.to_nat (p - 1))).
  apply card_U.
  apply inv_bijection in H. destruct H as [b Hb].
  rewrite (product_bij _ _ _ _ _ _ _ _ _ (Fints_finite (Z.to_nat (p - 1))) b Hb).
  transitivity (a ^ (Z.of_nat (Z.to_nat (p - 1))) mod p).
  unfold compose. remember (Z.to_nat (p - 1)) as n.
  generalize n. simple induction n0.
  rewrite empty_product. auto.
  intros n1 H. rewrite product_n. rewrite Nat2Z.inj_succ.
  unfold ZpZmult. rewrite Zmod_mod. rewrite Zmult_mod. unfold ZpZmult in H.
  rewrite H. rewrite <- Zmult_mod. f_equal.
  rewrite pow_succ_r. apply Zmult_comm. apply Nat2Z.is_nonneg.
  rewrite Z2Nat.id. auto. destruct p_prime; omega.
Qed.
Theorem FLT :
  (a ^ (p - 1)) mod p = 1.
Proof.
  assert (
  (ZpZmult p) (product Z (ZpZmult p) (ZpZmult_comm p) (ZpZmult_assoc p) 1 _  U_finite (compose (proj1_sig (P := fun k => 1 <= k <= p - 1)) f')) 1 = 
  (ZpZmult p) P'
              (product Z (ZpZmult p) (ZpZmult_comm p) (ZpZmult_assoc p) 1 _  U_finite (fun x => a))).
  unfold P'. rewrite P'1. symmetry. apply mod_1_mod.
  rewrite P'2 in H.
  unfold ZpZmult in H.
  apply simpl_mod_p in H.
  fold (ZpZmult p) in H.
  rewrite P'3 in H. rewrite Zmod_1_l in H. auto.
  destruct p_prime; omega. auto. apply P'_not_0.
Qed.
End FLT.
Definition inverse (p : Z) (a : Z) :=
  (a ^ (p - 2)) mod p.
Lemma p_inverse :
  forall p a : Z, prime p -> a mod p <> 0 -> (a * (inverse p a)) mod p = 1.
Proof.
  intros p a Hprime Hanz.
  unfold inverse. rewrite Zmult_mod_idemp_r.
  rewrite <- pow_succ_r by (destruct Hprime; omega).
  unfold succ. assert (p - 2 + 1 = p - 1). omega. rewrite H. apply FLT.
  auto. auto.
Qed.
Lemma inv_not_0 : 
  forall p a : Z, prime p -> a mod p <> 0 -> (inverse p a) mod p <> 0.
Proof.
  intros p a Hprime Hanz H. assert ((a * inverse p a) mod p = 1). apply p_inverse.
  auto. auto. rewrite Zmult_mod in H0. rewrite H in H0. rewrite Zmult_0_r in H0.
  rewrite Zmod_0_l in H0. discriminate.
Qed.
Lemma inv_inv :
  forall p a : Z, prime p -> a mod p <> 0 -> (inverse p (inverse p a)) = a mod p.
Proof.
  intros p a Hprime Hanz.
  assert (inverse p (inverse p a) mod p = inverse p (inverse p a)).
  unfold inverse. apply Zmod_mod. rewrite <- H.
  assert (inverse p a mod p <> 0). apply inv_not_0. auto. auto.
  apply simpl_mod_p with (a := (inverse p a)). auto. auto.
  rewrite p_inverse by auto. rewrite Zmult_comm. rewrite p_inverse by auto. auto.
Qed.
Lemma inv_bounds :
  forall p a : Z, prime p -> a mod p <> 0 -> 1 <= inverse p a <= p - 1.
Proof.
  intros. assert (inverse p a <> 0). unfold inverse. rewrite <- Zmod_mod. 
  apply inv_not_0. auto. auto.
  assert (0 <= inverse p a < p). apply Zmod_pos_bound. destruct H; omega. omega.
Qed.
Lemma inv_mod :
  forall p a : Z, prime p -> inverse p a = inverse p (a mod p).
Proof.
  intros. unfold inverse. apply Zpower_mod. destruct H; omega.
Qed.
Lemma inv_prod : 
  forall p a b : Z, prime p -> ((inverse p a) * (inverse p b)) mod p = inverse p (a * b).
Proof.
  intros. unfold inverse. rewrite <- Zmult_mod.
  rewrite Zmult_power. auto. destruct H; omega.
Qed.
 
Section Wilson.
Variable p : Z.
Hypothesis p_prime : prime p.
Hypothesis p_odd : p mod 2 = 1.
Let p_not_2 :
  p <> 2.
Proof.
  intro. rewrite H in p_odd. rewrite Z_mod_same in p_odd. omega. omega.
Qed.
Let U_finite :
  finite {x : Z | 1 <= x <= p - 1}.
Proof.
  exists (Z.to_nat (p - 1 - 1 + 1)). apply card_interval. destruct p_prime; omega.
Qed.  
Theorem Wilson :
  product Z (ZpZmult p) (ZpZmult_comm p) (ZpZmult_assoc p) 1 _ U_finite (fun x => `x)
    = -1 mod p.
Proof.
  rewrite product_split with (P := fun x => `x = inverse p `x);
  [ | (apply one_idemp; auto) | (intros; symmetry; rewrite ZpZmult_comm with (x := 1); apply mod_1_mod) ].
  assert (1 <= 1 <= p - 1). destruct p_prime; omega.
  assert (proj1_sig (exist (fun x => 1 <= x <= p - 1) 1 H) =
      inverse p (proj1_sig (exist (fun x => 1 <= x <= p - 1) 1 H))).
  simpl. unfold inverse. rewrite one_pow by (destruct p_prime; omega).
  rewrite Zmod_1_l by (destruct p_prime; omega). auto.
  assert (1 <= p - 1 <= p - 1). destruct p_prime; omega.
   assert (proj1_sig (exist (fun x => 1 <= x <= p - 1) (p - 1) H1) =
      inverse p (proj1_sig (exist (fun x => 1 <= x <= p - 1) (p - 1) H1))).
  simpl. unfold inverse. transitivity ((-1) ^ (p - 2) mod p).
  rewrite minus_one_pow_odd. rewrite <- minus_mod. f_equal. omega. omega.
  apply odd_mod. rewrite Zminus_mod. rewrite Z_mod_same. rewrite p_odd. auto. omega.
  rewrite Zpower_mod. f_equal. f_equal. rewrite <- minus_mod. f_equal. omega. omega.
  assert ((0 < 2)%nat). omega. remember (exist (fun x => (x < 2)%nat) (0%nat) H3) as F2Zero.
  assert ((1 < 2)%nat). omega. remember (exist (fun x => (x < 2)%nat) (1%nat) H4) as F2One.  
  remember (fun a : (Fints 2) =>
    If a = F2Zero then exist (fun k => `k = inverse p `k) (exist (fun x => 1 <= x <= p - 1) 1 H) H0 else
                       exist _ (exist (fun x => 1 <= x <= p - 1) (p - 1) H1) H2) as b.
  assert (bijection b).
  apply bijection_inversible.
  exists (fun x => If ``x = 1 then F2Zero else F2One).
  split. intro a. rewrite Heqb. ex_mid_destruct. ex_mid_destruct. auto.
  simpl in e. exfalso. assert (p <> 2). apply p_not_2. omega.
  ex_mid_destruct. simpl in n. omega. simpl in n. destruct a as [a' Ha'].
  apply proj1_inj. rewrite HeqF2One. simpl. apply proj1_inj_neg in n0.
  rewrite HeqF2Zero in n0. simpl in n0. omega.
  intro x. rewrite Heqb. ex_mid_destruct. ex_mid_destruct.
  apply proj1_inj. simpl. apply proj1_inj. simpl. auto.
  rewrite HeqF2One in e. rewrite HeqF2Zero in e. discriminate.
  ex_mid_destruct. contradict n. auto.
  destruct x as [x' Hx']. destruct x' as [x'' Hx'']. apply proj1_inj. simpl.
  apply proj1_inj. simpl in *.
  assert (x'' mod p <> 0). rewrite Zmod_small. omega. omega.
  assert ((x'' * (inverse p x'') - 1) mod p = 0).
  rewrite Zminus_mod. rewrite p_inverse. rewrite Zminus_mod_idemp_r.
  simpl. rewrite Zmod_0_l. auto. auto. auto.
  rewrite <- Hx' in H6.
  assert ((x'' - 1) * (x'' + 1) mod p = 0). rewrite <- H6.
  f_equal. rewrite Zmult_minus_distr_r. repeat (rewrite Zmult_plus_distr_r).
  omega. apply Zmod_divide in H7. apply prime_mult in H7.
  destruct H7. apply Zdivide_mod in H7. rewrite Zmod_small in H7. omega.
  omega. apply Zdivide_mod in H7. assert (((x'' + 1) - 1) mod p = p - 1).
  rewrite Zminus_mod. rewrite H7. rewrite Zmod_1_l. apply minus_mod.
  omega. omega. rewrite Zmod_small in H8. omega. omega. auto. omega.
  rewrite product_bij with (b := b) (HJ := Fints_finite 2) by auto.
  rewrite product_n. rewrite product_n. rewrite empty_product.
  unfold compose. rewrite Heqb.
  rewrite If_l by (unfold Fints_coerce; unfold Fints_last; rewrite HeqF2Zero; apply proj1_inj; auto).
  rewrite If_r by (rewrite HeqF2Zero; unfold Fints_last; apply proj1_inj_neg; simpl; auto). simpl.
  rewrite one_idemp by auto.
  rewrite product_split with (P := fun x => ``x < inverse p ``x);
  [ | (apply one_idemp; auto) | (intros; symmetry; rewrite ZpZmult_comm with (x := 1); apply mod_1_mod) ].
  assert (c_ex1 : forall x : {x : Z | 1 <= x <= p - 1},
    1 <= inverse p `x <= p - 1).
  intro x. destruct x as [x' Hx'].
  simpl in *. apply inv_bounds. auto. rewrite Zmod_small. omega. omega.
  remember (fun x => exist (fun k => 1 <= k <= p - 1) (inverse p `x) (c_ex1 x)) as c1.
  assert (c_ex2 : forall x : {x : {x : Z | 1 <= x <= p - 1} | `x <> inverse p `x},
            proj1_sig (c1 `x) <>
       inverse p (proj1_sig (c1 `x))).
  rewrite Heqc1.
  intro x. destruct x as [x' Hx']. destruct x' as [x'' Hx''].
  simpl in *. rewrite inv_inv. rewrite Zmod_small. auto. omega. auto. rewrite Zmod_small. omega. omega.
  remember (fun x => exist (fun k => `k <> inverse p `k) (c1 `x) (c_ex2 x)) as c2.
  assert (c_ex3 : forall x : {x : {x : {x : Z | 1 <= x <= p - 1} | `x <> inverse p `x} |
        ``x < inverse p ``x},
    ~ (proj1_sig (proj1_sig (c2 `x)) < inverse p (proj1_sig (proj1_sig (c2 `x))))).
  rewrite Heqc2. simpl. rewrite Heqc1. simpl.
  intro x. destruct x as [x' Hx']. destruct x' as [x'' Hx'']. destruct x'' as [x''' Hx'''].
  simpl in *. rewrite inv_inv. rewrite Zmod_small. omega. omega. auto. rewrite Zmod_small. omega. omega.
  remember (fun x => exist (fun k => ~ ``k < inverse p ``k) (c2 `x) (c_ex3 x)) as c3.
  assert (bijection c3).
  apply bijection_inversible.
  assert (c'_ex : forall x : {x : {x : {x : Z | 1 <= x <= p - 1} | `x <> inverse p `x} |
     ~ ``x < inverse p ``x},
    proj1_sig (proj1_sig (c2 `x)) < inverse p (proj1_sig (proj1_sig (c2 `x)))).
  rewrite Heqc2. simpl. rewrite Heqc1. simpl.
  intro x. destruct x as [x' Hx']. destruct x' as [x'' Hx'']. destruct x'' as [x''' Hx'''].
  simpl in *. rewrite inv_inv. rewrite Zmod_small. omega. omega. auto. rewrite Zmod_small. omega. omega.
  remember (fun x => exist (fun k => ``k < inverse p ``k) (c2 `x) (c'_ex x)) as c'.
  assert (forall x, c2 (c2 x) = x). intro x.
  destruct x as [x' Hx']. destruct x' as [x'' Hx''].
  rewrite Heqc2. apply proj1_inj. simpl. rewrite Heqc1. apply proj1_inj. simpl.
  rewrite inv_inv. apply Zmod_small. omega. auto. rewrite Zmod_small. omega. omega.
  exists c'. split.
  intro x. rewrite Heqc3. rewrite Heqc'. apply proj1_inj. simpl. auto.
  intro y. rewrite Heqc3. rewrite Heqc'. apply proj1_inj. simpl. auto.
  rewrite product_bij with (b := c3) (HJ :=
    (subtype_finite
           (subtype_finite U_finite
              (fun x : {x : Z | 1 <= x <= p - 1} => `x <> inverse p `x))
           (fun x : {x : {x : Z | 1 <= x <= p - 1} | `x <> inverse p `x} =>
            ``x < inverse p ``x))) by auto.
  rewrite <- product_mul by (apply one_idemp; auto).
  rewrite product_ext with (g := fun x => 1).
  unfold ZpZmult. rewrite Zmult_1_l. rewrite <- Zmult_1_r with (n := -1).
  rewrite <- Zmult_mod_idemp_l with (a := -1). f_equal.
  f_equal. rewrite Zmod_small by omega. rewrite <- minus_mod. auto. omega.
  apply product_property_conservation. intros. rewrite H7. rewrite H8. apply one_idemp.
  auto. auto. auto.
  intro x. destruct x as [x' Hx']. destruct x' as [x'' Hx'']. destruct x'' as [x''' Hx'''].
  simpl in *. unfold compose. rewrite Heqc3. simpl. rewrite Heqc2. simpl.
  rewrite Heqc1. simpl. unfold ZpZmult. apply p_inverse. auto. rewrite Zmod_small. omega. omega.
Qed.
End Wilson.

Definition legendre (p a : Z) :=
  If a mod p = 0 then 0 else
  If exists y, (y ^ 2) mod p = a mod p then 1 else -1.

Lemma pow_0_l :
  forall n : Z, 0 < n -> 0 ^ n = 0.
Proof.
  intros n H. rewrite (Zsucc_pred n). rewrite pow_succ_r. omega. omega.
Qed.

Section Eulers_criterion.
Variable p : Z.
Hypothesis p_prime : prime p.
Hypothesis p_odd : p mod 2 = 1.
Variable a : Z.
Let p_not_2 : 
  p <> 2.
Proof.
  intro. rewrite H in p_odd. rewrite Z_mod_same in p_odd. omega. omega.
Qed.
Let if_a_0 :
  a mod p = 0 -> 0 mod p = (a ^ ((p - 1) / 2)) mod p.
Proof.
  intro H.
  rewrite Zpower_mod. rewrite H.
  assert ((p - 1) / 2 >= 2 / 2). apply Z_div_ge. omega. destruct p_prime; omega.
  rewrite Z_div_same in H0. assert (0 < (p - 1) / 2). omega. rewrite pow_0_l by auto.
  auto. omega. destruct p_prime; omega.
Qed.
Let if_a_square :
  a mod p <> 0 -> (exists y, (y ^ 2) mod p = a mod p) ->
    1 mod p = (a ^ ((p - 1) / 2)) mod p.
Proof.
  intros H Hsq. destruct Hsq as [y Hsq].
  assert (y mod p <> 0). intro Hc. rewrite Zpower_mod in Hsq by (destruct p_prime; omega).
  rewrite Hc in Hsq. rewrite pow_0_l in Hsq. rewrite Zmod_0_l in Hsq. congruence.
  omega.
  rewrite Zpower_mod by (destruct p_prime; omega). rewrite <- Hsq.
  rewrite <- Zpower_mod by (destruct p_prime; omega).
  rewrite power_power.
  symmetry. rewrite Zmod_1_l by (destruct p_prime; omega).
  assert (2 * ((p - 1) / 2) = p - 1). symmetry. apply Z_div_exact_2. omega.
  rewrite <- Zminus_mod_idemp_l. rewrite p_odd. auto.
  rewrite H1. apply FLT. auto. auto. omega. apply Z_div_pos. omega. destruct p_prime; omega.
Qed.
Let if_a_not_square :
  a mod p <> 0 -> (forall y, (y * y) mod p <> a mod p) ->
    -1 mod p = (a ^ ((p - 1) / 2)) mod p.
Proof.
  intros Hanz Hnotsq.
  remember (fun x : {x : Z | 1 <= x <= p - 1} => ((inverse p `x) * a) mod p) as f.
  assert (forall x : {x : Z | 1 <= x <= p - 1}, 1 <= f x <= p - 1).
  intro x. destruct x as [x' Hx']. rewrite Heqf. simpl.
  assert (0 <= (inverse p x' * a) mod p < p). apply mod_pos_bound. destruct p_prime; omega.
  assert ((inverse p x' * a) mod p <> 0). intro H1.
  apply Zmod_divide in H1. apply prime_mult in H1. destruct H1.
  apply Zdivide_mod in H0. assert (inverse p x' mod p <> 0).
  apply inv_not_0. auto. rewrite Zmod_small. omega. omega. contradiction.
  apply Zdivide_mod in H0. contradiction. auto. destruct p_prime; omega.
  omega.
  remember (fun x => exist (fun k => 1 <= k <= p - 1) (f x) (H x)) as f'.
  assert (forall x, f' (f' x) = x). intro x. rewrite Heqf'. generalize H. rewrite Heqf.
  intro. apply proj1_inj. simpl. destruct Heqf.
  rewrite <- inv_mod. rewrite <- inv_prod. rewrite Zmult_mod_idemp_l.
  rewrite <- Zmult_assoc. rewrite Zmult_mod. rewrite inv_inv. rewrite Zmult_comm with (m := a).
  rewrite p_inverse. rewrite Zmult_1_r. repeat (rewrite Zmod_mod). destruct x. simpl. rewrite Zmod_small.
  auto. omega. auto. auto. auto. destruct x. simpl. rewrite Zmod_small. omega. omega. auto. auto.
  assert (forall x, proj1_sig (f' x) <> `x).
  intro x. destruct x as [x' Hx']. rewrite Heqf'. simpl. rewrite Heqf. simpl. intro H1.
  assert ((x' * ((inverse p x' * a) mod p)) mod p = a mod p).
  rewrite Zmult_mod_idemp_r. rewrite Zmult_assoc. rewrite <- Zmult_mod_idemp_l.
  rewrite p_inverse. f_equal. omega. auto. rewrite Zmod_small. omega. omega.
  rewrite H1 in H2. apply (Hnotsq x'). auto.
  assert (finite {x : Z | 1 <= x <= p - 1}).
  exists (Z.to_nat (p - 1 - 1 + 1)). apply card_interval. destruct p_prime; omega.
  assert (product Z (ZpZmult p) (ZpZmult_comm p) (ZpZmult_assoc p) 1 _ H2 (fun x => `x)
    = -1 mod p). rewrite <- Wilson with (p_prime := p_prime).
  f_equal. apply proof_irrelevance. auto.
  rewrite product_split with (P := fun x => proj1_sig (f' x) < `x) in H3;
  [ | (apply one_idemp; auto) | (intros; symmetry; rewrite ZpZmult_comm with (x := 1); apply mod_1_mod) ].
  assert (forall x : {x : {x : Z | 1 <= x <= p - 1} | proj1_sig (f' x) < `x},
    ~ (proj1_sig (f' (f' `x)) < (proj1_sig (f' `x)))).
  intro x. destruct x as [x' Hx']. rewrite H0. simpl. omega.
  remember (fun x => exist (fun k => ~ (proj1_sig (f' k) < `k)) (f' `x) (H4 x)) as b.
  assert (bijection b).
  apply bijection_inversible.
  assert (forall x : {x : {x : Z | 1 <= x <= p - 1} | ~ (proj1_sig (f' x) < `x)},
    proj1_sig (f' (f' `x)) < proj1_sig (f' `x)).
  intro x. destruct x as [x' Hx']. rewrite H0. simpl.
  assert (proj1_sig (f' x') <> `x'). apply H1. omega.
  exists (fun x => exist _ (f' `x) (H5 x)).
  split. intro x. apply proj1_inj. simpl. rewrite Heqb. simpl. apply H0.
  intro y. apply proj1_inj. simpl. rewrite Heqb. simpl. apply H0.
  rewrite product_bij with (b := b) (HJ := (subtype_finite H2
             (fun x : {x : Z | 1 <= x <= p - 1} => proj1_sig (f' x) < `x))) in H3.
  rewrite <- product_mul in H3. unfold compose in H3.
  rewrite Heqb in H3. simpl in H3.
  rewrite product_ext with (g := fun x => a mod p) in H3.
  destruct (subtype_finite H2
          (fun x : {x : Z | 1 <= x <= p - 1} => proj1_sig (f' x) < `x)) as [n Hn].
  assert (cardinality 
             {x : {x : Z | 1 <= x <= p - 1} | ~ proj1_sig (f' x) < `x} n).
  apply card_bijection with (b := b). auto. auto.
  assert (cardinality {x : Z | 1 <= x <= p - 1} (n + n)).
  apply disjoint_union_cardinality with (P := fun x => proj1_sig (f' x) < `x).
  auto. auto. assert ((n + n = Z.to_nat (p - 1))%nat).
  apply cardinality_unique with (T := {x : Z | 1 <= x <= p - 1}).
  auto. assert (Z.to_nat (p - 1) = Z.to_nat (p - 1 - 1 + 1)).
  f_equal. omega. rewrite H8. apply card_interval. destruct p_prime; omega.
  assert (n = Z.to_nat ((p - 1) / 2)).
  assert (p - 1 = (p - 1) / 2 + (p - 1) / 2).
  rewrite <- Zmult_1_r. rewrite Zmult_plus_distr_l. rewrite <- Zmult_plus_distr_r.
  rewrite Zmult_comm. apply Z_div_exact_2. omega. rewrite <- Zminus_mod_idemp_l.
  rewrite p_odd. rewrite Zmod_0_l. auto.
  rewrite H9 in H8. rewrite Z2Nat.inj_add in H8. omega.
  apply Z_div_pos. omega. destruct p_prime; omega. apply Z_div_pos. omega. destruct p_prime; omega.
  assert (product Z (ZpZmult p) (ZpZmult_comm p) (ZpZmult_assoc p) 1
       {x : {x : Z | 1 <= x <= p - 1} | proj1_sig (f' x) < `x}
       (ex_intro
          (fun n0 : nat =>
           cardinality {x : {x : Z | 1 <= x <= p - 1} | proj1_sig (f' x) < `x} n0) n
          Hn)
       (fun _ : {x : {x : Z | 1 <= x <= p - 1} | proj1_sig (f' x) < `x} => a mod p) = 
    a ^ ((p - 1) / 2) mod p).
  assert (Hc : cardinality {x : {x : Z | 1 <= x <= p - 1} | proj1_sig (f' x) < `x} n). auto.
  apply inv_bijection in Hc. destruct Hc as [c Hc].
  rewrite product_bij with (b := c) (HJ := Fints_finite n) by auto. unfold compose.
  assert (Z.of_nat n = (p - 1) / 2). rewrite <- Z2Nat.id. f_equal. auto.
  apply Z_div_pos. omega. destruct p_prime; omega.
  rewrite <- H10.
  generalize n. simple induction n0.
  rewrite empty_product. rewrite Zmod_1_l. auto. destruct p_prime; omega.
  intros n1 Hr. rewrite product_n. rewrite Hr. rewrite Nat2Z.inj_succ.
  rewrite Zpower_succ_r. unfold ZpZmult. rewrite <- Zmult_mod. f_equal. apply Zmult_comm.
  apply Nat2Z.is_nonneg.
  rewrite <- H10. rewrite H3. f_equal.
  intro x. destruct x as [x' Hx']. destruct x' as [x'' Hx''].
  unfold ZpZmult. simpl. rewrite Heqf'. simpl. rewrite Heqf. simpl.
  rewrite Zmult_mod_idemp_r. rewrite Zmult_assoc.
  rewrite <- Zmult_mod_idemp_l. rewrite p_inverse. f_equal. omega. auto.
  rewrite Zmod_small. omega. omega. apply one_idemp. auto. auto.
Qed.
Theorem Eulers_criterion :
  (legendre p a) mod p = a ^ ((p - 1) / 2) mod p.
Proof.
  
  unfold legendre.
  case_if. auto.
  case_if. auto.
  apply if_a_not_square. auto.
  intro y. contradict n0. exists y.
  assert (y ^ 2 = y * y).
  simpl. unfold pow_pos. unfold Pos.iter. rewrite Zmult_assoc. rewrite Zmult_1_r. auto.
  congruence.
Qed.
End Eulers_criterion.

Section Eisensteins_lemma.
Variable p : Z.
Hypothesis p_prime : prime p.
Hypothesis p_odd : p mod 2 = 1.

Let p_positive : 
  0 < p.
Proof.
  destruct p_prime. omega.
Qed.
Let p_positive_rev :
  p > 0.
Proof.
  destruct p_prime. omega.
Qed.
Let p_not_0 :
  p <> 0.
Proof.
  assert (0 < p). apply p_positive. omega.
Qed.
Let eq_mod_2 : 
  forall x y : Z, (x + y) mod 2 = 0 -> x mod 2 = y mod 2.
Proof.
  intros x y H. rewrite Zplus_mod in H.
  destruct (even_or_odd x). assert (x mod 2 = 0). apply even_mod. auto.
  rewrite H1 in H. rewrite H1. simpl in H. rewrite Zmod_mod in H. auto.
  assert (x mod 2 = 1). apply odd_mod. auto.
  rewrite H1 in H. rewrite H1. rewrite Zplus_mod_idemp_r in H.
  assert (y = 1 + y - 1). omega. rewrite H2. rewrite Zminus_mod.
  rewrite H. auto.
Qed.
Let div_mod_mod_2_even :
  forall a : Z, a mod 2 = 0 -> (a / p) mod 2 = (a mod p) mod 2.
Proof.
  intros a H.
  rewrite <- Zmult_1_l with (n := (a / p)).
  rewrite <- p_odd. rewrite Zmult_mod_idemp_l.
  apply eq_mod_2. rewrite <- Z_div_mod_eq. auto. auto.
Qed.
Let div_mod_mod_2_odd :
  forall a : Z, a mod 2 = 1 -> (a / p) mod 2 = (a mod p + 1) mod 2.
Proof.
  intros a H.
  rewrite <- Zmult_1_l with (n := (a / p)).
  rewrite <- p_odd. rewrite Zmult_mod_idemp_l.
  apply eq_mod_2. rewrite Zplus_assoc. rewrite <- Z_div_mod_eq.
  rewrite p_odd. rewrite <- Zplus_mod_idemp_l. rewrite H. auto. auto.
Qed.

Variable q : Z.
Hypothesis q_not_0 : q mod p <> 0.
Hypothesis q_postive : q >= 0.

Let r (u : {u : Z | 1 <= u <= p - 1 /\ u mod 2 = 0}) :=
    (q * `u) mod p.
Let r_positive :
  forall (u : {u : Z | 1 <= u <= p - 1 /\ u mod 2 = 0}), 0 <= r u.
Proof.
  intro u. assert (0 <= r u < p). unfold r.
  apply mod_pos_bound with (b := p). apply p_positive. omega.
Qed.
Let r' (u : {u : Z | 1 <= u <= p - 1 /\ u mod 2 = 0}) :=
    ((Zpower (-1) (r u)) * (r u)) mod p.
Let r''_ex (u : {u : Z | 1 <= u <= p - 1 /\ u mod 2 = 0}) :
  1 <= (r' u) <= p - 1 /\ (r' u) mod 2 = 0.
Proof with (exact p_not_0 || exact p_positive || auto).
  split.
  assert (0 <= r' u < p). unfold r'. apply mod_pos_bound...
  destruct H.
  split. assert (r' u <> 0).
  intro H2. unfold r' in H2. apply Zmod_divide in H2...
  apply prime_mult in H2... destruct H2.
  apply prime_divide_pow in H1; [ | apply r_positive | auto].
  apply Zdivide_opp_r_rev with (b := 1) in H1.
  apply Zdivide_1 in H1. destruct p_prime. omega.
  unfold r in H1. apply Zdivide_mod in H1.
  rewrite <- Zmod_div_mod in H1... 2 : reflexivity.
  apply Zmod_divide in H1... apply prime_mult in H1...
  destruct H1. apply Zdivide_mod in H1...
  assert (0 < `u). destruct u. simpl. omega.
  assert (0 <> `u). omega.
  apply Zdivide_bounds in H1... destruct u. simpl in *.
  destruct p_prime. repeat (rewrite abs_eq in H1; [ | omega]).
  omega. omega. omega.
  unfold r'.
  destruct (even_or_odd (r u)).
  rewrite minus_one_pow_even; [ | apply r_positive | auto].
  rewrite mul_1_l. unfold r. rewrite Zmod_mod.
  apply even_mod. auto.
  rewrite minus_one_pow_odd; [ | apply r_positive | auto].
  assert (((p - r u) mod p) mod 2 = 0).
  assert (0 <= p - r u < p).
  assert (0 <= r u < p). unfold r. apply mod_pos_bound. apply p_positive.
  assert (0 <> r u). intro H1. apply Zodd_equiv in H.
  rewrite <- H1 in H. contradiction.
  omega. rewrite Zmod_small with (n := p) by auto. apply odd_mod in H.
  rewrite Zminus_mod. rewrite p_odd. rewrite H. auto.
  rewrite <- H0. f_equal. rewrite Zminus_mod. f_equal.
  unfold r. rewrite Zmod_mod. rewrite Z_mod_same; [ | apply p_positive_rev].
  auto.
Qed.
Let r'' (u : {u : Z | 1 <= u <= p - 1 /\ u mod 2 = 0}) :=
   exist (fun k => 1 <= k <= p - 1 /\ k mod 2 = 0) (r' u) (r''_ex u).
Let r''_inj1 :
  forall u1 u2, r' u1 = r' u2 -> Even (r u1) -> Odd (r u2) -> r u1 = r u2.
Proof.
  intros u1 u2 Heq Hodd Heven.
  exfalso.
  unfold r' in Heq.
  rewrite minus_one_pow_even in Heq; [ | apply r_positive | auto].
  rewrite mul_1_l in Heq.
  rewrite minus_one_pow_odd in Heq; [ | apply r_positive | auto].
  unfold r in Heq.
  rewrite Zmult_mod_idemp_r in Heq.
  rewrite Zmult_comm with (n := -1) in Heq.
  rewrite Zmod_mod in Heq.
  rewrite <- Zmult_assoc in Heq. rewrite <- opp_eq_mul_m1 in Heq.
  apply simpl_mod_p in Heq; [ | auto | auto].
  destruct u1 as [u1' Hu1']. destruct u2 as [u2' Hu2'].
  assert (u1' mod p = u1'). apply Zmod_small. omega.
  assert (u2' mod p = u2'). apply Zmod_small. omega.
  simpl in Heq.
  rewrite Z_mod_nz_opp_full in Heq by omega.
  rewrite H in Heq. rewrite H0 in Heq.
  assert (u1' mod 2 = ((p mod 2) - (u2' mod 2)) mod 2).
  rewrite <- Zminus_mod. f_equal. auto.
  destruct Hu1' as [Hu1' Hu1'']. destruct Hu2' as [Hu2' Hu2''].
  rewrite Hu1'' in H1. rewrite Hu2'' in H1. rewrite p_odd in H1.
  discriminate.
Qed.
Let r''_injective :
  injection r''.
Proof.
  intros u1 u2 H.
  unfold r'' in H.
  apply proj1_inj in H. simpl in H.
  assert (H0: r' u1 = r' u2). auto.
  unfold r' in H0.
  assert (r u1 = r u2).
  destruct (even_or_odd (r u1)).
    rewrite minus_one_pow_even in H0; [ | apply r_positive | auto].
    rewrite mul_1_l in H0.
    destruct (even_or_odd (r u2)).
      rewrite minus_one_pow_even in H0; [ | apply r_positive | auto].
      rewrite mul_1_l in H0.
      unfold r in H0.
      repeat (rewrite Zmod_mod in H0). unfold r. auto.
   (* Odd (r u2) *)
     apply r''_inj1. auto. auto. auto.
  (* Odd (r u1) *)
    rewrite minus_one_pow_odd in H0; [ | apply r_positive | auto].
    destruct (even_or_odd (r u2)).
      symmetry. apply r''_inj1. auto. auto. auto.
   (* Odd (r u1) *)
      rewrite minus_one_pow_odd in H0; [ | apply r_positive | auto].
      apply simpl_mod_p in H0; [ | auto | ].
      unfold r in H0. repeat (rewrite Zmod_mod in H0). unfold r. auto.
      intro H3. apply Zmod_divide in H3. apply Zdivide_opp_r in H3.
      simpl in H3. apply Zdivide_mod in H3. rewrite Zmod_1_l in H3.
      discriminate. destruct p_prime. auto. apply p_not_0.
  unfold r in H1.
  apply simpl_mod_p in H1; [ | auto | auto].
  destruct u1 as [u1' Hu1']. destruct u2 as [u2' Hu2'].
  assert (u1' mod p = u1'). apply Zmod_small. omega.
  assert (u2' mod p = u2'). apply Zmod_small. omega.
  apply proj1_inj. simpl in *. congruence.
Qed.
Let r''_surjective :
  surjection r''.
Proof with (exact p_not_0 || exact p_positive ||
     exact p_positive_rev || auto).
  intro y. destruct y as [y' Hy']. destruct Hy' as [Hy'1 Hy'2].
  cut (exists x, r' x = y'). intro H. destruct H as [x Hx]. exists x.
  unfold r''. apply proj1_inj. auto.
  assert (exists a : Z, (q * a) mod p = y').
  destruct (not_0_inversible_mod_p q p p_prime q_not_0) as [b Hb].
  exists (y' * b). rewrite Zmult_comm. rewrite <- Zmult_assoc.
  rewrite <- Zmult_mod_idemp_r. rewrite Hb. rewrite Zmult_1_r.
  apply Zmod_small. omega.
  destruct H as [a Ha].
  destruct (even_or_odd (a mod p)).
    assert (1 <= a mod p <= p - 1 /\ (a mod p) mod 2 = 0).
    split. assert (0 <= a mod p < p). apply mod_pos_bound...
    assert (a mod p <> 0). intro H1. rewrite <- Zmult_mod_idemp_r in Ha.
    rewrite H1 in Ha. rewrite mul_0_r in Ha. rewrite Zmod_0_l in Ha.
    omega. omega. apply even_mod. auto.
    exists (exist _ (a mod p) H0).
    unfold r'. unfold r. simpl.
    repeat (rewrite Zmult_mod_idemp_r). rewrite Ha.
    rewrite minus_one_pow_even; [ | omega | auto]. rewrite mul_1_l.
    rewrite Zmult_mod_idemp_r. auto. apply even_mod. auto.
  (* Odd (a mod p) *)
    assert (1 <= p - a mod p <= p - 1 /\ (p - a mod p) mod 2 = 0).
    split. assert (0 <= a mod p < p). apply mod_pos_bound...
    assert (a mod p <> 0). intro H1. rewrite H1 in H. rewrite odd_mod in H.
    discriminate. omega. rewrite odd_mod in H.
    rewrite Zminus_mod. rewrite H. rewrite p_odd. auto.
    exists (exist _ (p - a mod p) H0).
    unfold r'. unfold r. simpl.
    repeat (rewrite Zmult_mod_idemp_r).
    repeat (rewrite Zmult_minus_distr_l with (p := q)).
    assert (((q * p - q * (a mod p)) mod p) = p - y').
    rewrite Zminus_mod. rewrite Zmult_mod. rewrite Z_mod_same...
    rewrite mul_0_r. rewrite Zmod_0_l. rewrite Zmult_mod_idemp_r. 
    rewrite Ha. rewrite <- Z_mod_same with (a := p)... rewrite Zminus_mod_idemp_l.
    apply Zmod_small. omega. rewrite <- Zmult_mod_idemp_r. repeat (rewrite H1).
    assert (Odd (p - y')).
    apply odd_mod. rewrite Zminus_mod. rewrite p_odd. rewrite Hy'2. auto.
    rewrite minus_one_pow_odd. assert (-1 * (p - y') = y' + -1 * p). omega.
    rewrite H3. rewrite Z_mod_plus_full. apply Zmod_small. omega. omega. auto.
Qed.

Let card_R :
  cardinality {u : Z | 1 <= u <= p - 1 /\ u mod 2 = 0} (Z.to_nat ((p - 1) / 2)).
Proof.
  assert (forall u : {u : Z | 1 <= u <= p - 1 /\ u mod 2 = 0}, (Z.to_nat ((`u - 1) / 2) < Z.to_nat ((p - 1) / 2))%nat).
  intro u. destruct u as [u' Hu']. destruct Hu' as [Hu'1 Hu'2]. simpl.
  apply Nat2Z.inj_lt.
  repeat (rewrite Z2Nat.id by (apply Z_div_pos; destruct p_prime; omega)).
  apply Zdiv_lt_upper_bound. omega. rewrite Zmult_comm.
  rewrite <- Z_div_exact_full_2. omega. omega. rewrite Zminus_mod.
  rewrite p_odd. auto.
  exists (fun u : {u : Z | 1 <= u <= p - 1 /\ u mod 2 = 0} =>
      (exist _ (Z.to_nat ((`u - 1) / 2)) (H u))).
  apply bijection_inversible.
  assert (forall n : {k : nat | (k < Z.to_nat ((p - 1) / 2))%nat},
    1 <= 2 + 2 * (Z.of_nat `n) <= p - 1 /\ (2 + 2 * (Z.of_nat `n)) mod 2 = 0).
  intro n. destruct n as [n' Hn']. unfold proj1_sig. split.
  assert (0 <= Z.of_nat n'). apply Nat2Z.is_nonneg.
  assert (Z.of_nat (S n') <= Z.of_nat (Z.to_nat ((p - 1) / 2))). apply Nat2Z.inj_le. auto.
  rewrite Z2Nat.id in H1. apply Zmult_le_compat_l with (p := 2) in H1.
  rewrite <- Z_div_exact_full_2 in H1. rewrite Nat2Z.inj_succ in H1.
  omega. omega. rewrite Zminus_mod. rewrite p_odd. auto. omega.
  apply Z_div_pos. omega. destruct p_prime; omega.
  rewrite Zmult_comm. rewrite Z_mod_plus_full. auto.
  exists (fun n : {k : nat | (k < Z.to_nat ((p - 1) / 2))%nat} => 
           exist _ (2 + 2 * (Z.of_nat `n)) (H0 n)).
  unfold proj1_sig. split.
  intro u. destruct u as [u' Hu']. destruct Hu' as [Hu' Hu''].
  apply proj1_inj. unfold proj1_sig.
  rewrite Z2Nat.id. assert (u' - 1 = 2 * ((u' - 1) / 2) + ((u' - 1) mod 2)).
  apply Z_div_mod_eq. omega. assert ((u' - 1) mod 2 = 1).
  rewrite Zminus_mod. rewrite Hu''. auto. omega. apply Z_div_pos. omega.
  omega.
  intro y. destruct y as [y' Hy'].
  apply proj1_inj. unfold proj1_sig.
  assert (2 + 2 * Z.of_nat y' - 1 = 1 + of_nat y' * 2). omega.
  rewrite H1. rewrite Z_div_plus_full. simpl. apply Nat2Z.id. omega.
Qed.

Let R_finite :
  finite {u : Z | 1 <= u <= p - 1 /\ u mod 2 = 0}.
Proof.
  exists (Z.to_nat ((p - 1) / 2)). apply card_R.
Qed.

Let mlt := ZpZmult p.
Let mlt_comm := ZpZmult_comm p.
Let mlt_assoc := ZpZmult_assoc p.
Let one_id := one_idemp p p_prime.

Let P := product Z mlt mlt_comm mlt_assoc 1 _ R_finite (fun x => `x).
Let P_not_0 :
  P mod p <> 0.
Proof.
  unfold P. apply product_property_conservation.
  intros x y Hxnz Hynz. unfold mlt. unfold ZpZmult. rewrite Zmod_mod.
  intro H. apply Zmod_divide in H. apply prime_mult in H.
  destruct H. apply Zdivide_mod in H. contradiction. apply Zdivide_mod in H. contradiction.
  auto. apply p_not_0. rewrite Zmod_1_l. omega. destruct p_prime. omega.
  intro x. destruct x. simpl.  rewrite Zmod_small. omega. omega.
Qed.
Let P1 :
  product Z mlt mlt_comm mlt_assoc 1 _ R_finite r =
    mlt (product Z mlt mlt_comm mlt_assoc 1 _ R_finite (fun x => q)) P.
Proof.
  unfold P.
  rewrite <- product_mul. apply product_ext.
  unfold mlt. unfold ZpZmult. unfold r. auto.
  apply one_id.
Qed.
Let P2 :
  product Z mlt mlt_comm mlt_assoc 1 _ R_finite r' =
    mlt (product Z mlt mlt_comm mlt_assoc 1 _ R_finite (fun u => (-1) ^ (r u)))
        (product Z mlt mlt_comm mlt_assoc 1 _ R_finite r).
Proof.
  rewrite <- product_mul. apply product_ext.
  unfold mlt. unfold ZpZmult. unfold r'. auto.
  apply one_id.
Qed.
Let P3 :
  product Z mlt mlt_comm mlt_assoc 1 _ R_finite r' = P.
Proof.
  transitivity (product Z mlt mlt_comm mlt_assoc 1 _ R_finite
    (compose (proj1_sig (P := (fun u => 1 <= u <= p - 1 /\ u mod 2 = 0))) r'')).
  apply product_ext. unfold compose. unfold r''. simpl. auto.
  unfold P.
  rewrite <- product_bij with (HI := R_finite).
  apply product_ext. auto.
  split. apply r''_injective. apply r''_surjective.
Qed.
Let P4 :
  mlt (product Z mlt mlt_comm mlt_assoc 1 _ R_finite (fun u => (-1) ^ (r u)))
      (product Z mlt mlt_comm mlt_assoc 1 _ R_finite (fun u => (-1) ^ (r u)))
    = 1.
Proof.
  rewrite <- product_mul. apply product_property_conservation.
  intros. rewrite H. rewrite H0. apply one_id. auto.
  unfold mlt. unfold ZpZmult. intro x. rewrite <- Zmult_power. simpl.
  rewrite one_pow. rewrite Zmod_1_l. auto. destruct p_prime; omega.
  apply r_positive. apply r_positive. apply one_id.
Qed.
Let P5 :
  mlt P ((product Z mlt mlt_comm mlt_assoc 1 _ R_finite (fun u => (-1) ^ (r u)))) =
    mlt (product Z mlt mlt_comm mlt_assoc 1 _ R_finite r) 1.
Proof.
  assert (mlt (product Z mlt mlt_comm mlt_assoc 1 _ R_finite r) 1 =
          mlt (product Z mlt mlt_comm mlt_assoc 1 _ R_finite r) 
                   (mlt (product Z mlt mlt_comm mlt_assoc 1 _ R_finite (fun u => (-1) ^ (r u)))
                        (product Z mlt mlt_comm mlt_assoc 1 _ R_finite (fun u => (-1) ^ (r u))))).
  rewrite P4. auto.
  rewrite H. rewrite <- P3. rewrite P2.
  remember (product Z mlt mlt_comm mlt_assoc 1
        {u : Z | 1 <= u <= p - 1 /\ u mod 2 = 0} R_finite
        (fun u : {u : Z | 1 <= u <= p - 1 /\ u mod 2 = 0} => (-1) ^ r u)) as a.
  remember (product Z mlt mlt_comm mlt_assoc 1
     {u : Z | 1 <= u <= p - 1 /\ u mod 2 = 0} R_finite r) as b.
  rewrite mlt_comm. rewrite mlt_assoc. rewrite mlt_comm. auto.
Qed. 
Let P6 :
  mlt P (product Z mlt mlt_comm mlt_assoc 1 _ R_finite (fun u => (-1) ^ (r u))) =
  mlt P (product Z mlt mlt_comm mlt_assoc 1 _ R_finite (fun u => q)).
Proof.
  assert (mlt P ((product Z mlt mlt_comm mlt_assoc 1 _ R_finite (fun u => (-1) ^ (r u)))) =
    mlt (product Z mlt mlt_comm mlt_assoc 1 _ R_finite r) 1).
  apply P5.
  rewrite P1 in H. rewrite <- (mod_1_mod p) in H. rewrite H. apply mlt_comm.
Qed.
Let P7 :
  (product Z mlt mlt_comm mlt_assoc 1 _ R_finite (fun u => (-1) ^ (r u))) mod p =
  (product Z mlt mlt_comm mlt_assoc 1 _ R_finite (fun u => q)) mod p.
Proof.
  apply simpl_mod_p with (a := P). auto. apply P_not_0.
  apply P6.
Qed.
Let P8 :
  (product Z mlt mlt_comm mlt_assoc 1 _ R_finite (fun u => (-1) ^ (r u))) =
  (product Z mlt mlt_comm mlt_assoc 1 _ R_finite (fun u => (-1) ^ ((q * `u) / p))).
Proof.
  apply product_ext. intro i. apply minus_one_pow_mod_2.
  apply r_positive. apply Z_div_pos. apply p_positive_rev.
  destruct i as [i' Hi']. simpl. rewrite <- Zmult_0_l with (n := i').
  apply Zmult_le_compat_r. omega. omega.
  unfold r.
  destruct i as [i' Hi']. destruct Hi' as [Hi' Hi'']. simpl.
  assert (q * i' = p * (q * i' / p) + (q * i') mod p).
  apply Z_div_mod_eq. apply p_positive_rev.
  assert ((q * i' + (q * i') mod p) mod 2 = (p * (q * i' / p) + 2 * ((q * i') mod p)) mod 2).
  f_equal. omega.
  rewrite Zplus_mod in H0. rewrite Zmult_mod in H0.
  rewrite Hi'' in H0. rewrite Zmult_0_r in H0. rewrite Zmod_0_l in H0.
  rewrite Zplus_0_l in H0. rewrite Zmod_mod in H0.
  rewrite Zplus_mod in H0. rewrite Zmult_mod with (n := 2) in H0.
  rewrite p_odd in H0. rewrite Zmult_1_l in H0. rewrite Zmod_mod in H0.
  rewrite Zmult_mod with (n := 2) in H0. rewrite Z_mod_same in H0 by omega.
  rewrite Zmult_0_l in H0. rewrite Zmod_0_l in H0. rewrite Zplus_0_r in H0.
  rewrite Zmod_mod in H0. auto.
Qed.
Let P9 :
  (product Z mlt mlt_comm mlt_assoc 1 _ R_finite (fun u => (-1) ^ ((q * `u) / p))) mod p =
  (m1_pow (product Z Zplus Zplus_comm Zplus_assoc 0 _ R_finite (fun u => (q * `u) / p))) mod p.
Proof.
  transitivity ((product Z mlt mlt_comm mlt_assoc 1
    {u : Z | 1 <= u <= p - 1 /\ u mod 2 = 0} R_finite
    (fun u : {u : Z | 1 <= u <= p - 1 /\ u mod 2 = 0} => m1_pow (q * `u / p))) mod p).
  f_equal.
  apply product_ext. intro i. apply m1_pow_compatible.
  apply Zge_iff_le. apply Z_div_pos. apply p_positive_rev.
  destruct i as [i' Hi']. simpl. rewrite <- Zmult_0_l with (n := i').
  apply Zmult_le_compat_r. omega. omega.
  rewrite product_morph with (morph := fun x => (m1_pow x) mod p)
                             (multS := mlt) (multS_com := mlt_comm)
                             (multS_assoc := mlt_assoc) (eS := 1).
  unfold compose.
  apply product_morph with (morph := fun x => x mod p)
                           (multS := mlt) (multS_com := mlt_comm)
                           (multS_assoc := mlt_assoc) (eS := 1).
  intros. unfold mlt. unfold ZpZmult. rewrite Zmod_mod. rewrite <- Zmult_mod. auto.
  apply Zmod_1_l. destruct p_prime; omega.
  intros. unfold mlt. unfold ZpZmult. rewrite <- Zmult_mod. f_equal. apply m1_pow_morphism.
  unfold m1_pow. simpl. apply Zmod_1_l. destruct p_prime; omega.
Qed.
Let P10 :
  (product Z mlt mlt_comm mlt_assoc 1 _ R_finite (fun u => q)) mod p =
    (q ^ ((p - 1) / 2)) mod p.
Proof.
  assert (cardinality {u : Z | 1 <= u <= p - 1 /\ u mod 2 = 0} (Z.to_nat ((p - 1) / 2))).
  apply card_R.
  apply inv_bijection in H. destruct H as [b Hb].
  rewrite (product_bij _ _ _ _ _ _ _ _ _ (Fints_finite (Z.to_nat ((p - 1) / 2))) b Hb).
  unfold compose.
  transitivity (q ^ (Z.of_nat (Z.to_nat ((p - 1) / 2))) mod p).
  remember (to_nat ((p - 1) / 2)) as n.
  generalize n. simple induction n0.
  rewrite empty_product. simpl. auto.
  intros n1 H. rewrite Nat2Z.inj_succ. rewrite product_n. unfold mlt. unfold ZpZmult.
  rewrite Zmod_mod. fold (ZpZmult p). rewrite <- Zmult_mod_idemp_l. fold mlt. rewrite H.
  rewrite Zmult_mod_idemp_l. f_equal. rewrite pow_succ_r. rewrite Zmult_comm.
  auto. apply Nat2Z.is_nonneg.
  rewrite Z2Nat.id. auto. apply Z_div_pos. omega. destruct p_prime; omega.
Qed.
Let Eisensteins_lemma_mod_p :
  (legendre p q) mod p = (m1_pow (product Z Zplus Zplus_comm Zplus_assoc 0 _ R_finite (fun u => (q * `u) / p))) mod p.
Proof.
  rewrite Eulers_criterion by auto. rewrite <- P10. rewrite <- P7. rewrite P8. apply P9.
Qed.
Let p_not_2 :
  p <> 2.
Proof.
 intro H. rewrite H in p_odd. rewrite Z_mod_same in p_odd by omega. discriminate.
Qed.
Lemma Eisensteins_lemma1 :
  legendre p q = m1_pow (product Z Zplus Zplus_comm Zplus_assoc 0 _ R_finite (fun u => (q * `u) / p)).
Proof.
  assert ((legendre p q + 1) mod p = (m1_pow (product Z Zplus Zplus_comm Zplus_assoc 0 _ R_finite (fun u => (q * `u) / p)) + 1) mod p).
  rewrite Zplus_mod. rewrite Eisensteins_lemma_mod_p. rewrite <- Zplus_mod. auto.
  rewrite Zmod_small in H; [ | (destruct p_prime; unfold legendre; case_if; case_if; omega; omega)].
  rewrite Zmod_small in H; [ | (destruct p_prime;
    destruct (m1_pow_1_or_m1 (product Z add add_comm add_assoc 0
     {u : Z | 1 <= u <= p - 1 /\ u mod 2 = 0} R_finite
     (fun u : {u : Z | 1 <= u <= p - 1 /\ u mod 2 = 0} => q * `u / p))); omega; omega)].
  omega.
Qed.
Let U_finite :
  finite {u : Z | 1 <= u <= (p - 1) / 2}.
Proof.
  exists (Z.to_nat ((p - 1) / 2 - 1 + 1)). apply card_interval.
  apply Zmult_le_reg_r with (p := 2). omega.
  rewrite Zmult_comm with (n := (p - 1) / 2). rewrite <- Z_div_exact_full_2.
  destruct p_prime; omega. omega. rewrite <- Zminus_mod_idemp_l. rewrite p_odd. auto.
Qed.
Hypothesis q_odd : q mod 2 = 1.
Hypothesis q_prime : prime q.
Let E1 :
  (product Z Zplus Zplus_comm Zplus_assoc 0 _ R_finite (fun u => (q * `u) / p)) mod 2 =
  (product Z Zplus Zplus_comm Zplus_assoc 0 _ U_finite (fun u => (q * `u) / p)) mod 2.
Proof.
  rewrite product_split with (P := fun u : {u : Z | 1 <= u <= p - 1 /\ u mod 2 = 0} => `u <= (p - 1) / 2) by (intros; omega).
  rewrite product_split with (P := fun u : {u : Z | 1 <= u <= (p - 1) / 2} => `u mod 2 = 0) by (intros; omega).
  rewrite Zplus_mod.
  rewrite Zplus_mod with (a := product _ _ _ _ _ {x : {u : Z | 1 <= u <= (p - 1) / 2} | `x mod 2 = 0} _ _).
  f_equal. f_equal. f_equal.
  assert (b_ex1 : forall x : {x : {u : Z | 1 <= u <= p - 1 /\ u mod 2 = 0} | `x <= (p - 1) / 2},
    1 <= ``x <= (p - 1) / 2). intro x. destruct x as [x' Hx']. destruct x' as [x'' Hx''].
  simpl in *. omega.
  remember (fun x => exist (fun k => 1 <= k <= (p - 1) / 2) ``x (b_ex1 x)) as b1.
  assert (b_ex2 : forall x, (proj1_sig (b1 x)) mod 2 = 0).
  intro x. rewrite Heqb1. simpl. destruct x as [x' Hx']. destruct x' as [x'' Hx'']. simpl in *. destruct Hx''. auto.
  remember (fun x => exist (fun k => `k mod 2 = 0) (b1 x) (b_ex2 x)) as b2.
  assert (Hb : bijection b2).
  apply bijection_inversible.
  assert (b'_ex1 : forall x : {x : {x : Z | 1 <= x <= (p - 1) / 2} | `x mod 2 = 0},
    1 <= ``x <= p - 1 /\ ``x mod 2 = 0). intro x. destruct x as [x' Hx']. destruct x' as [x'' Hx''].
  simpl in *. split. assert ((p - 1) / 2 < p - 1). apply Z_div_lt. omega. destruct p_prime; omega.
  omega. auto.
  remember (fun x => exist (fun k => 1 <= k <= p - 1 /\ k mod 2 = 0) ``x (b'_ex1 x)) as b'1.
  assert (b'_ex2 : forall x, proj1_sig (b'1 x) <= (p - 1) / 2). intro x. destruct x as [x' Hx']. destruct x' as [x'' Hx''].
  simpl in *. rewrite Heqb'1. simpl. omega.
  remember (fun x => exist (fun k => `k <= (p - 1) / 2) (b'1 x) (b'_ex2 x)) as b'2.
  exists b'2. split.
  intro x. destruct x as [x' Hx']. destruct x' as [x'' Hx''].
  rewrite Heqb2. rewrite Heqb'2. apply proj1_inj. simpl.
  rewrite Heqb'1. apply proj1_inj. simpl. rewrite Heqb1. simpl. auto.
  intro x. destruct x as [x' Hx']. destruct x' as [x'' Hx''].
  rewrite Heqb2. rewrite Heqb'2. apply proj1_inj. simpl.
  rewrite Heqb1. apply proj1_inj. simpl. rewrite Heqb'1. simpl. auto.
  rewrite product_bij with (b := b2) (HJ := (subtype_finite R_finite
     (fun u : {u : Z | 1 <= u <= p - 1 /\ u mod 2 = 0} => `u <= (p - 1) / 2))).
  unfold compose. rewrite Heqb2. simpl. rewrite Heqb1. simpl. auto. auto.
  apply eq_mod_2.
  assert (p - 1 = (p - 1) / 2 + (p - 1) / 2).
  rewrite <- Zmult_1_r. rewrite Zmult_plus_distr_l. rewrite <- Zmult_plus_distr_r.
  rewrite Zmult_comm. apply Z_div_exact_2. omega. rewrite <- Zminus_mod_idemp_l.
  rewrite p_odd. rewrite Zmod_0_l. auto.
  assert (c_ex1 : forall x : {x : {u : Z | 1 <= u <= p - 1 /\ u mod 2 = 0} | ~ `x <= (p - 1) / 2},
    1 <= (p - ``x) <= (p - 1) / 2).
  intro x. destruct x as [x' Hx']. destruct x' as [x'' Hx''].
  simpl in *. omega.
  remember (fun x => exist (fun k => 1 <= k <= (p - 1) / 2) (p - ``x) (c_ex1 x)) as c1.
  assert (c_ex2 : forall x, ~ (proj1_sig (c1 x) mod 2 = 0)).
  intro x. destruct x as [x' Hx']. destruct x' as [x'' Hx'']. simpl in *.
  rewrite Heqc1. simpl. rewrite Zminus_mod. auto. rewrite p_odd.
  destruct Hx'' as [Hx''1 Hx''2]. rewrite Hx''2. intro. discriminate.
  remember (fun x => exist (fun k => ~ `k mod 2 = 0) (c1 x) (c_ex2 x)) as c2.
  assert (Hc : bijection c2). apply bijection_inversible.
  assert (c'_ex1 : forall x : {x : {x : Z | 1 <= x <= (p - 1) / 2} | `x mod 2 <> 0},
    1 <= p - ``x <= p - 1 /\ (p - ``x) mod 2 = 0).
  intro x. destruct x as [x' Hx']. destruct x' as [x'' Hx'']. simpl in *.
  split. omega. rewrite Zminus_mod. rewrite p_odd.
  assert (x'' mod 2 = 1). assert (0 <= x'' mod 2 < 2). apply mod_pos_bound. omega. omega.
  rewrite H0. auto.
  remember (fun x => exist (fun k => 1 <= k <= p - 1 /\ k mod 2 = 0) (p - ``x) (c'_ex1 x)) as c'1.
  assert (c'_ex2 : forall x, ~ proj1_sig (c'1 x) <= (p - 1) / 2).
  intro x. destruct x as [x' Hx']. destruct x' as [x'' Hx'']. simpl in *.
  rewrite Heqc'1. simpl. omega.
  remember (fun x => exist (fun k => ~ `k <= (p - 1) / 2) (c'1 x) (c'_ex2 x)) as c'2.
  exists c'2. split.
  intro x. destruct x as [x' Hx']. destruct x' as [x'' Hx''].
  rewrite Heqc'2. apply proj1_inj. simpl. rewrite Heqc'1. apply proj1_inj. simpl.
  rewrite Heqc2. simpl. rewrite Heqc1. simpl. omega.
  intro x. destruct x as [x' Hx']. destruct x' as [x'' Hx''].
  rewrite Heqc2. apply proj1_inj. simpl. rewrite Heqc1. apply proj1_inj. simpl.
  rewrite Heqc'2. simpl. rewrite Heqc'1. simpl. omega.
  rewrite product_bij with (b := c2) (HJ := (subtype_finite R_finite
      (fun x : {u : Z | 1 <= u <= p - 1 /\ u mod 2 = 0} =>
       ~ `x <= (p - 1) / 2))) by auto.
  rewrite <- product_mul by auto. unfold compose.
  rewrite Heqc2. simpl. rewrite Heqc1. simpl.
  apply product_property_conservation.
  intros x y H1 H2. rewrite Zplus_mod. rewrite H1. rewrite H2. auto. auto.
  intro x. destruct x as [x' Hx']. destruct x' as [x'' Hx'']. simpl in *.
  rewrite Zplus_mod.
  rewrite div_mod_mod_2_even. rewrite div_mod_mod_2_odd.
  rewrite <- Zplus_mod. rewrite Zmult_minus_distr_l.
  rewrite Zminus_mod. rewrite Zmult_mod with (b := p).
  rewrite Z_mod_same. rewrite Zmult_0_r. rewrite Zmod_0_l.
  assert ((0 - (q * x'') mod p) = -((q * x'') mod p)). omega. rewrite H0.
  rewrite minus_mod.
  assert ((q * x'') mod p + (p - (q * x'') mod p + 1) = p + 1). omega. rewrite H1.
  rewrite <- Zplus_mod_idemp_l. rewrite p_odd. auto.
  assert (0 <= (q * x'') mod p < p). apply mod_pos_bound. auto.
  assert ((q * x'') mod p <> 0). intro H2.
  apply Zmod_divide in H2. apply prime_mult in H2. destruct H2.
  apply Zdivide_mod in H2. contradiction.
  apply Zdivide_mod in H2. rewrite Zmod_small in H2. omega. omega. auto. auto.
  omega. auto. rewrite Zmult_mod.
  rewrite q_odd. rewrite Zminus_mod. rewrite p_odd.
  destruct Hx'' as [Hx''1 Hx''2]. rewrite Hx''2. auto.
  rewrite Zmult_mod. destruct Hx'' as [Hx''1 Hx''2]. rewrite Hx''2. rewrite Zmult_0_r. auto.
Qed.
Definition EL := (product Z Zplus Zplus_comm Zplus_assoc 0 _ U_finite (fun u => (q * `u) / p)).
Lemma EL1 : 
  0 <= EL.
Proof.
  unfold EL. apply product_property_conservation. intros. omega. omega.
  intro x. destruct x as [x' Hx']. simpl.
  apply Z_div_pos. omega. rewrite <- Zmult_0_l with (n := x').
  apply Zmult_le_compat_r. omega. omega.
Qed.
Lemma EL2 :
  legendre p q = m1_pow EL.
Proof.
  rewrite Eisensteins_lemma1. unfold EL. unfold m1_pow.
  rewrite E1. auto.
Qed.
Lemma EL3 : 
  cardinality {s : Z * Z | 1 <= fst s <= (p - 1) / 2 /\ 1 <= snd s <= (q - 1) / 2
                                                     /\ p * snd s <= q * fst s}
   (Z.to_nat EL).
Proof.
  unfold EL.
  assert (Z.to_nat
     (product Z Zplus Zplus_comm Zplus_assoc 0 {u : Z | 1 <= u <= (p - 1) / 2}
        U_finite (fun u : {u : Z | 1 <= u <= (p - 1) / 2} => q * `u / p)) =
      product nat plus plus_comm plus_assoc O {u : Z | 1 <= u <= (p - 1) / 2}
        U_finite (fun u : {u : Z | 1 <= u <= (p - 1) / 2} => Z.to_nat (q * `u / p))).
  rewrite <- Nat2Z.id. f_equal.
  transitivity (product Z add add_comm add_assoc 0 {u : Z | 1 <= u <= (p - 1) / 2} U_finite
    (fun u : {u : Z | 1 <= u <= (p - 1) / 2} => Z.of_nat (Z.to_nat (q * `u / p)))).
  apply product_ext. intro i. rewrite Z2Nat.id. auto. destruct i as [i' Hi'].
  simpl. apply Z_div_pos. omega. rewrite <- Zmult_0_r with (n := q).
  apply Zmult_le_compat_l. omega. destruct q_prime; omega.
  symmetry. apply product_morph. intros x y. apply Nat2Z.inj_add. auto.
  rewrite H.
  assert (f_ex : forall s : {s : Z * Z |
    1 <= fst s <= (p - 1) / 2 /\
    1 <= snd s <= (q - 1) / 2 /\ p * snd s <= q * fst s},
   1 <= fst `s <= (p - 1) / 2).
  intro s. destruct s as [s' Hs']. simpl. destruct Hs'. auto.
  apply disjoint_union_cardinality_sum with
   (f := fun s => exist (fun k => 1 <= k <= (p - 1) / 2) (fst `s) (f_ex s)).
  intro k. destruct k as [k' Hk']. simpl.
  assert (b_ex : forall s : {x : {s : Z * Z |
      1 <= fst s <= (p - 1) / 2 /\
      1 <= snd s <= (q - 1) / 2 /\ p * snd s <= q * fst s} |
    exist (fun k : Z => 1 <= k <= (p - 1) / 2) (fst `x) (f_ex x) =
    exist (fun k : Z => 1 <= k <= (p - 1) / 2) k' Hk'},
      1 <= snd ``s <= (q * k') / p).
  intro s. destruct s as [s' Hs']. destruct s' as [s'' Hs'']. simpl in *.
  apply proj1_inj in Hs'. simpl in Hs'. rewrite Hs' in Hs''.
  destruct Hs'' as [Hs''1 Hs''2]. destruct Hs''2 as [Hs''2 Hs''3].
  split. omega. apply Zdiv_le_lower_bound. auto. rewrite Zmult_comm. auto.
  remember (fun s => exist (fun k => 1 <= k <= (q * k' / p)) (snd ``s) (b_ex s)) as b.
  assert (Hb : bijection b).
  apply bijection_inversible.
  assert (b'_ex1 : forall x : {k : Z | 1 <= k <= q * k' / p},
    (1 <= fst (k', `x) <= (p - 1) / 2 /\ (1 <= snd (k', `x) <= (q - 1) / 2
                                      /\ p * snd (k', `x) <= q * fst (k', `x)))).
  intro x. simpl. destruct x as [x' Hx']. simpl.
  split. omega. split. split. omega.
  rewrite over_2 by auto. transitivity (q * k' / p). omega.
  transitivity (q * ((p - 1) / 2) / p).
  apply Z_div_le. auto. apply Zmult_le_compat_l. omega. omega.
  rewrite over_2 by auto. apply Zdiv_le_lower_bound. omega.
  transitivity ((q * (p / 2) * 2) / p).
  rewrite Zmult_comm. rewrite Zmult_comm with (m := 2).
  apply Zdiv_mult_le. rewrite <- Zmult_0_r with (n := q).
  apply Zmult_le_compat_l. apply Z_div_pos. omega. omega. omega. omega. omega.
  transitivity (q * p / p). apply Z_div_le. omega. rewrite <- Zmult_assoc.
  apply Zmult_le_compat_l. rewrite Zmult_comm. apply Z_mult_div_ge. omega. omega.
  rewrite Z_div_mult. omega. omega.
  transitivity (p * ((q * k') / p)). apply Zmult_le_compat_l. omega. omega.
  apply Z_mult_div_ge. omega.
  remember (fun x => exist (fun s =>
    1 <= fst s <= (p - 1) / 2 /\ 1 <= snd s <= (q - 1) / 2 /\ p * snd s <= q * fst s
  ) (k', `x) (b'_ex1 x)) as b'1.
  assert (b'_ex2 : forall x,
    exist (fun k : Z => 1 <= k <= (p - 1) / 2) (fst (proj1_sig (b'1 x))) (f_ex (b'1 x)) =
    exist (fun k : Z => 1 <= k <= (p - 1) / 2) k' Hk').
  intro x. apply proj1_inj. simpl. rewrite Heqb'1. simpl. auto.
  exists (fun x => exist _ (b'1 x) (b'_ex2 x)).
  split.
  intro x. destruct x as [x' Hx']. destruct x' as [x'' Hx''].
  apply proj1_inj. simpl. rewrite Heqb'1. apply proj1_inj. simpl in *.
  rewrite Heqb. simpl. apply proj1_inj in Hx'. simpl in Hx'. rewrite <- Hx'.
  symmetry. apply surjective_pairing.
  intro y. destruct y as [y' Hy']. rewrite Heqb. apply proj1_inj. simpl.
  rewrite Heqb'1. simpl. auto.
  apply card_bijection with (b := b). auto.
  assert (Z.to_nat (q * k' / p) = Z.to_nat (q * k' / p - 1 + 1)). f_equal. omega.
  rewrite H0. apply card_interval_full.
  assert (0 <= q * k' / p). apply Z_div_pos. omega.
  rewrite <- Zmult_0_l with (n := k'). apply Zmult_le_compat_r.
  omega. omega. omega.
Qed.
 
End Eisensteins_lemma.

Section Quadratic_reciprocity.
Variable p : Z.
Variable q : Z.
Hypothesis p_prime : prime p.
Hypothesis q_prime : prime q.
Hypothesis p_odd : p mod 2 = 1.
Hypothesis q_odd : q mod 2 = 1.
Hypothesis p_not_q : p <> q.
Let p_ge_1 :
  p > 1.
Proof.
  destruct p_prime; omega.
Qed.
Let q_ge_1 :
  q > 1.
Proof.
  destruct q_prime; omega.
Qed.
Let p_not_2 :
  p <> 2.
Proof.
  intro H. rewrite H in p_odd. discriminate.
Qed.
Let q_not_2 : 
  q <> 2.
Proof.
  intro H. rewrite H in q_odd. discriminate.
Qed.
Let p2_pos :
  (p - 1) / 2 > 0.
Proof.
  assert (1 <= (p - 1) / 2). apply Zdiv_le_lower_bound. omega. omega. omega.
Qed.
Let q2_pos :
  (q - 1) / 2 > 0.
Proof.
  assert (1 <= (q - 1) / 2). apply Zdiv_le_lower_bound. omega. omega. omega.
Qed.
Let p_mod_q_not_0 :
  p mod q <> 0.
Proof.
  intro H. apply Zmod_divide in H. contradict p_not_q. symmetry. apply prime_div_prime.
  auto. auto. auto. omega.
Qed.
Let q_mod_p_not_0 :
  q mod p <> 0.
Proof.
  intro H. apply Zmod_divide in H. contradict p_not_q. apply prime_div_prime.
  auto. auto. auto. omega.
Qed.
Let a := EL p p_prime p_odd q.
Let b := EL q q_prime q_odd p.
Let QR1 : 
  cardinality {s : {s : Z * Z | 1 <= fst s <= (p - 1) / 2 /\ 1 <= snd s <= (q - 1) / 2} |
                                                     p * snd `s <= q * fst `s}
   (Z.to_nat a).
Proof.
  apply card_and with (Q := fun s => p * snd s <= q * fst s).
  apply card_subtype with (Q := fun s =>
    1 <= fst s <= (p - 1) / 2 /\ 1 <= snd s <= (q - 1) / 2 /\ p * snd s <= q * fst s).
  intro x. tauto.
  unfold a.
  apply EL3. omega. auto. auto.
Qed.
Let QR2 : 
  cardinality {s : {s : Z * Z | 1 <= fst s <= (p - 1) / 2 /\ 1 <= snd s <= (q - 1) / 2} |
                                                     ~ (p * snd `s <= q * fst `s)}
   (Z.to_nat b).
Proof.
  assert (forall s : {s : Z * Z | 1 <= fst s <= (p - 1) / 2 /\ 1 <= snd s <= (q - 1) / 2},
    ~ p * snd `s <= q * fst `s <-> q * fst `s <= p * snd `s).
  intro s. split.
  intro H. omega.
  intro H.
  assert (q * fst `s <> p * snd `s). intro H0.
  assert (p | q * fst `s). exists (snd `s). rewrite Zmult_comm with (m := p). auto.
  apply prime_mult in H1. destruct H1. apply Zdivide_mod in H1.
  apply q_mod_p_not_0 in H1. auto. apply Zdivide_mod in H1. rewrite Zmod_small in H1.
  destruct s as [s' Hs']. simpl in H1.
  omega. destruct s as [s' Hs']. simpl. destruct Hs' as [Hs'1 Hs'2].
  assert ((p - 1) / 2 < p - 1). apply Z_div_lt. omega. omega. omega. auto. omega.
  apply card_subtype with (Q := fun s => q * fst `s <= p * snd `s).
  auto.
  apply card_and with (Q := fun s => q * fst s <= p * snd s).
  apply card_subtype with (Q := fun s =>
    1 <= fst s <= (p - 1) / 2 /\ 1 <= snd s <= (q - 1) / 2 /\ q * fst s <= p * snd s).
  intro x. tauto.
  assert (forall s : {x : Z * Z |
    1 <= fst x <= (p - 1) / 2 /\ 1 <= snd x <= (q - 1) / 2 /\ q * fst x <= p * snd x},
   1 <= fst (snd `s, fst `s) <= (q - 1) / 2 /\ 1 <= snd (snd `s, fst `s) <= (p - 1) / 2 /\
   q * snd (snd `s, fst `s) <= p * fst (snd `s, fst `s)).
  simpl. destruct s. simpl. tauto.
  remember (fun s : {x : Z * Z |
           1 <= fst x <= (p - 1) / 2 /\
           1 <= snd x <= (q - 1) / 2 /\ q * fst x <= p * snd x} =>
  exist (fun s => 
    1 <= snd s <= (p - 1) / 2 /\ 1 <= fst s <= (q - 1) / 2 /\ q * snd s <= p * fst s
  ) (snd `s, fst `s) (proj2_sig s)) as f.
  apply card_bijection with (b := f).
  rewrite Heqf.
  apply sub_bijection with
   (P := fun s => 1 <= snd s <= (p - 1) / 2 /\ 1 <= fst s <= (q - 1) / 2 /\ q * snd s <= p * fst s)
   (b := fun s => (snd s, fst s)).
  apply bijection_inversible. exists (fun s => (snd s, fst s)).
  simpl. split. intro x. symmetry. apply surjective_pairing.
  intro y. symmetry. apply surjective_pairing.
  apply card_subtype with (Q := fun s =>
    1 <= fst s <= (q - 1) / 2 /\ 1 <= snd s <= (p - 1) / 2 /\ q * snd s <= p * fst s).
  tauto.
  unfold b. apply EL3. omega. auto. auto.
Qed.
Let QR3 : 
  cardinality {s : Z * Z | 1 <= fst s <= (p - 1) / 2 /\ 1 <= snd s <= (q - 1) / 2}
  (Z.to_nat a + Z.to_nat b).
Proof.
  apply disjoint_union_cardinality with (P := fun s => p * snd `s <= q * fst `s).
  apply QR1. apply QR2.
Qed.
Let QR4 :
  cardinality {s : Z * Z | 1 <= fst s <= (p - 1) / 2 /\ 1 <= snd s <= (q - 1) / 2}
  (Z.to_nat (((p - 1) / 2) * ((q - 1) / 2))).
Proof.
  assert (forall s : {s : Z * Z | 1 <= fst s <= (p - 1) / 2 /\ 1 <= snd s <= (q - 1) / 2},
    1 <= fst `s + ((p - 1) / 2) * (snd `s - 1) <= ((p - 1) / 2) * ((q - 1) / 2)).
  intro s. destruct s as [s' Hs']. destruct Hs' as [Hs'1 Hs'2].
  simpl. split.
  transitivity (fst s' + ((p - 1) / 2) * (1 - 1)). omega.
  apply Zplus_le_compat_l. apply Zmult_le_compat_l. omega.
  apply Z_div_pos. omega. omega.
  transitivity (fst s' + (p - 1) / 2 * ((q - 1) / 2 - 1)).
  apply Zplus_le_compat_l. apply Zmult_le_compat_l. omega.
  apply Z_div_pos. omega. omega.
  transitivity ((p - 1) / 2 + (p - 1) / 2 * ((q - 1) / 2 - 1)).
  omega. rewrite Zmult_minus_distr_l. omega.
  apply card_bijection with (b := fun s => 
    exist (fun x => 1 <= x <= ((p - 1) / 2) * ((q - 1) / 2))
          (fst `s + ((p - 1) / 2) * (snd `s - 1)) (H s)).
  apply bijection_inversible.
  
  assert (forall x : {x : Z | 1 <= x <= ((p - 1) / 2) * ((q - 1) / 2)},
    1 <= fst ((`x - 1) mod ((p - 1) / 2) + 1, (`x - 1) / ((p - 1) / 2) + 1) <= (p - 1) / 2 /\
    1 <= snd ((`x - 1) mod ((p - 1) / 2) + 1, (`x - 1) / ((p - 1) / 2) + 1) <= (q - 1) / 2).
  intro x. destruct x as [x' Hx']. simpl.
  split. assert (0 <= (x' - 1) mod ((p - 1) / 2) < (p - 1) / 2).
  apply mod_pos_bound. omega. omega.
  assert (0 <= (x' -1) / ((p - 1) / 2)). apply Z_div_pos. omega. omega.
  assert ((x' - 1) / ((p - 1) / 2) < (q - 1) / 2). apply Zdiv_lt_upper_bound.
  omega. rewrite Zmult_comm. omega. omega.
  exists (fun x => exist _
    ((`x - 1) mod ((p - 1) / 2) + 1, (`x - 1) / ((p - 1) / 2) + 1) (H0 x)).
  simpl.
  split.
  intro s. destruct s as [s' Hs']. apply proj1_inj. simpl.
  rewrite Zminus_mod. rewrite Zmult_comm. rewrite Z_mod_plus_full.
  rewrite <- Zminus_mod. rewrite Zmod_small by omega.
  assert (fst s' + (snd s' - 1) * ((p - 1) / 2) - 1 = fst s' - 1 + (snd s' - 1) * ((p - 1) / 2)).
  omega. rewrite H1. rewrite Z_div_plus_full by omega. rewrite Zdiv_small by omega.
  transitivity (fst s', snd s'). f_equal. omega. omega. symmetry. apply surjective_pairing.
  intro x. destruct x as [x' Hx']. apply proj1_inj. simpl.
  assert ((x' - 1) / ((p - 1) / 2) + 1 - 1 = (x' - 1) / ((p - 1) / 2)). omega.
  rewrite H1.
  assert ((x' - 1) mod ((p - 1) / 2) + 1 +
    (p - 1) / 2 * ((x' - 1) / ((p - 1) / 2)) = 
          (p - 1) / 2 * ((x' - 1) / ((p - 1) / 2)) + (x' - 1) mod ((p - 1) / 2) + 1).
  omega. rewrite H2.
  rewrite <- Z_div_mod_eq. omega. omega.
  assert (Z.to_nat ((p - 1) / 2 * ((q - 1) / 2)) = Z.to_nat ((p - 1) / 2 * ((q - 1) / 2) - 1 + 1)).
  f_equal. omega. rewrite H0. apply card_interval_full.
  assert (0 * ((q - 1) / 2) <= (p - 1) / 2 * ((q - 1) / 2)). apply Zmult_le_compat_r.
  omega. omega. omega.
Qed.
Let QR5 :
  (Z.to_nat a + Z.to_nat b)%nat = (Z.to_nat (((p - 1) / 2) * ((q - 1) / 2))).
Proof.
  apply cardinality_unique with
   (T := {s : Z * Z | 1 <= fst s <= (p - 1) / 2 /\ 1 <= snd s <= (q - 1) / 2}).
  auto. auto.
Qed.
Let QR6 : 
  a + b = ((p - 1) / 2) * ((q - 1) / 2).
Proof.
  assert (0 <= a). apply EL1. omega. assert (0 <= b). apply EL1. omega.
  rewrite <- Z2Nat.id. rewrite <- Z2Nat.id with (n := a + b). f_equal.
  rewrite Z2Nat.inj_add. apply QR5. auto. auto.
  generalize H H0. generalize a b. intros. omega.
  rewrite <- Zmult_0_r with (n := (p - 1) / 2).
  apply Zmult_le_compat_l. omega. omega.
Qed.
Theorem Quadratic_reciprocity :
  (legendre p q) * (legendre q p) = (-1) ^ (((p - 1) / 2) * ((q - 1) / 2)).
Proof.
  rewrite EL2 with (p_prime := p_prime) (p_odd := p_odd) by (omega || auto).
  rewrite EL2 with (p_prime := q_prime) (p_odd := q_odd) by (omega || auto).
  rewrite m1_pow_compatible. rewrite <- m1_pow_morphism.
  f_equal. rewrite <- QR6. unfold a. unfold b. auto.
  rewrite <- Zmult_0_r with (n := (p - 1) / 2).
  apply Zmult_ge_compat_l. omega. omega.
Qed.
End Quadratic_reciprocity.
