Module FiniteTypes.

Require Import ClassicalDescription.
Require Import ProofIrrelevance.
Require Import Le. Require Import Lt. Require Import Plus.
Require Import Omega.
Notation "'If' P 'then' x 'else' y" := 
  (if (excluded_middle_informative P) then x else y) (at level 200).
Ltac case_if :=
  let go P := destruct P; try solve [elimtype False; congruence] in
  match goal with 
  | |- context [if ?P then _ else _] => go P
  | K: context [if ?P then _ else _] |- _ => go P
  end.
Ltac ex_mid_destruct :=
  match goal with
    | |- context [excluded_middle_informative ?P] => destruct (excluded_middle_informative P)
    | K : context [excluded_middle_informative ?P] |- _ => destruct (excluded_middle_informative P)
  end.
Lemma If_l : forall (A:Type) (P:Prop) (x y : A), 
  P -> (If P then x else y) = x.
Proof. intros. case_if. auto. Qed.
Lemma If_r : forall (A:Type) (P:Prop) (x y : A), 
  ~ P -> (If P then x else y) = y.
Proof. intros. case_if. auto. Qed.
Set Implicit Arguments.

Definition injection (A B : Type) (f : A -> B) :=
  forall x1 x2 : A, f x1 = f x2 -> x1 = x2.
Theorem injection_iff_neg (A B : Type) (f : A -> B) :
  injection f -> forall x1 x2 : A, f x1 <> f x2 <-> x1 <> x2.
Proof.
  intros Hinjection x1 x2. split.
  intro H. contradict H. f_equal. auto.
  intro H. contradict H. apply Hinjection. auto.
Qed.
Definition surjection (A B : Type) (f : A -> B) :=
  forall y : B, exists x : A, f x = y.
Definition bijection (A B : Type) (f : A -> B) :=
  injection f /\ surjection f.
Definition compose (A B C : Type) (f : B -> C) (g : A -> B) := fun x => f (g x).
Lemma inj_compose (A B C : Type) (f : B -> C) (g : A -> B) :
  injection f -> injection g -> injection (compose f g).
Proof.
  intros Hfinj Hginj x1 x2.
  unfold compose. intro H. apply Hfinj in H. apply Hginj. auto.
Qed.
Lemma surj_compose (A B C : Type) (f : B -> C) (g : A -> B) :
  surjection f -> surjection g -> surjection (compose f g).
Proof.
  intros Hfsurj Hgsurj y.
  unfold compose. destruct (Hfsurj y) as [z H].
  destruct (Hgsurj z) as [x H']. exists x. congruence.
Qed.
Lemma bij_compose (A B C : Type) (f : B -> C) (g : A -> B) :
  bijection f -> bijection g -> bijection (compose f g).
Proof.
  intros Hfbij Hgbij. split. apply inj_compose.
  apply Hfbij. apply Hgbij. apply surj_compose.
  apply Hfbij. apply Hgbij.
Qed.
Definition bijection' (A B : Type) (f : A -> B) :=
  forall y : B, exists! x : A, f x = y.
Hint Unfold injection surjection bijection bijection'.
Lemma bijection_alt (A B : Type) (f : A -> B) :
  bijection f <-> bijection' f.
Proof.
  split.
  repeat autounfold.
  intro Hbijection. destruct Hbijection as [Hinjection Hsurjection].
  intro y. apply unique_existence with (P := fun x => f x = y).
  split. apply Hsurjection. unfold uniqueness.
  intros x y0 H1 H2. apply Hinjection. congruence.
  repeat autounfold.
  intro Hbijection.
  assert (forall y : B, (exists x : A, f x = y) /\
    uniqueness (fun x => f x = y)).
  intro y. apply unique_existence with (P := fun x => f x = y).
  auto. unfold uniqueness in H.
  split.
  intros x1 x2 H1. apply (H (f x2)). auto. auto.
  intro y. apply (H y).
Qed.

Hint Resolve bijection_alt.

Definition inversible (A B : Type) (f : A -> B) :=
  exists g : B -> A,
    (forall x : A, g (f x) = x) /\ (forall y : B, f (g y) = y).
Hint Unfold inversible.
Lemma bijection_inversible (A B : Type) (f : A -> B) :
  bijection f <-> inversible f.
Proof.
  split.
  intro Hbijection. assert (Hbijection' : bijection' f).
  apply bijection_alt. auto.
  repeat (autounfold in *). destruct Hbijection as [Hinjection Hsurjection].
  assert (exists g : B -> A, forall y : B, f (g y) = y).
  apply unique_choice with (R := fun y x => f x = y). auto.
  destruct H as [g H]. exists g.
  split. intro x. apply Hinjection. auto. auto.
  intro Hinversible.
  repeat (autounfold in *). destruct Hinversible as [g Hinversible].
  destruct Hinversible as [Hinverseleft Hinverseright].
  split.
  intros x1 x2 H.
  rewrite <- Hinverseleft with (x := x1). rewrite <- Hinverseleft with (x := x2).
  f_equal. auto.
  intro y. exists (g y). auto.
Qed.
Lemma inv_bijection (A B : Type) :
  (exists f : A -> B, bijection f) -> (exists g : B -> A, bijection g).
Proof.
  intro H. destruct H as [f H].
  apply bijection_inversible in H. unfold inversible in H.
  destruct H as [g Hg]. destruct Hg as [Hginvleft Hginvright].
  exists g. apply bijection_inversible. eauto.
Qed.

Lemma id_bijection (A : Type) :
  bijection (fun x : A => x).
Proof.
  split. auto. eauto.
Qed.

Definition Fints (n : nat) :=
  {p : nat | p < n}.
Definition Fints_last (n : nat) : Fints (S n) :=
  exist (fun k => k < S n) n (lt_n_Sn n).

Definition cardinality (T : Type) (n : nat) :=
  exists f : T -> (Fints n), bijection f.

Lemma Fints_card (n : nat) :
  cardinality (Fints n) n.
Proof.
  exists (fun x => x). apply id_bijection.
Qed.

Definition finite (T : Type) :=
  exists n : nat, (cardinality T n).

Lemma Fints_finite (n : nat) :
  finite (Fints n).
Proof.
  exists n. apply Fints_card.
Qed.

Definition image (A B : Type) (f : A -> B) :=
  {y : B | exists x : A, f x = y}.

Notation "` x" := (proj1_sig x) (at level 0).
Definition Fints_coerce (n : nat) (m : nat) (H : n <= m) (k : Fints n) :=
  exist (fun p => p < m) `k (lt_le_trans `k n m (proj2_sig k) H).

Lemma proj1_inj (A : Type) (P : A -> Prop) :
  forall x y : (sig P), `x = `y <-> x = y.
Proof.
  intros x y. split.
  intro H. destruct x. destruct y.
  unfold "`" in H. destruct H. f_equal. apply proof_irrelevance.
  intro H. f_equal. auto.
Qed.
Lemma proj1_inj_neg (A : Type) (P : A -> Prop) :
  forall x y : (sig P), `x <> `y <-> x <> y.
Proof.
  intros x y. split.
  intro H. contradict H. apply proj1_inj. auto.
  intro H. contradict H. apply proj1_inj. auto.
Qed.

Lemma sub_bijection (T T' : Type) (P : T -> Prop) (b : T' -> T) (Hb : bijection b) :
  bijection (fun x : {x : T' | P (b x)} => exist P (b `x) (proj2_sig x)).
Proof.
  destruct Hb as [Hbinj Hbsurj].
  split.
  intros x1 x2 He. apply proj1_inj in He. simpl in He. apply Hbinj in He.
  apply proj1_inj. auto.
  intro y. destruct y as [y' Hy']. destruct (Hbsurj y').
  assert (P (b x)). congruence.
  exists (exist (fun x => P (b x)) x H0).
  apply proj1_inj. simpl. auto.
Qed.

Lemma bijection_restriction1 (n : nat) (T : Type) (b : (Fints (S n) -> T)) :
  bijection b ->
    forall k : Fints n, b (Fints_coerce (le_n_Sn n) k) <> b (Fints_last n).
Proof.
  intros Hbijection k. destruct Hbijection as [Hinjection _].
  apply injection_iff_neg. auto.
  unfold Fints_coerce. unfold Fints_last. destruct k as [k' Hk'].
  simpl. apply proj1_inj_neg. simpl. contradict Hk'. rewrite Hk'.
  apply lt_irrefl.
Qed.
Lemma bijection_restriction2 (n : nat) (T : Type) (b : (Fints (S n) -> T)) 
  (Hbijection : bijection b) :
  bijection (fun (k : Fints n) =>
    exist (fun p => p <> b (Fints_last n)) (b (Fints_coerce (le_n_Sn n) k))
     (bijection_restriction1 Hbijection k)).
Proof.
  destruct Hbijection as [Hinjection Hsurjection].
  split.
  intros x1 x2 H. apply proj1_inj in H. simpl in H.
  apply Hinjection in H. unfold Fints_coerce in H.
  apply proj1_inj in H. simpl in H. apply proj1_inj. auto.
  intro y. destruct y as [y' Hy']. destruct (Hsurjection y') as [x Hx].
  destruct x as [x' Hx'].
  assert (x' <> n). contradict Hy'. rewrite <- Hx. f_equal.
  destruct Hy'. unfold Fints_last. apply proj1_inj. auto.
  assert (x' < n). clear Hx. apply le_lt_or_eq in Hx'.
  destruct Hx'. apply lt_S_n. auto. injection H0. intro. contradiction.
  exists (exist (fun p => p < n) x' H0).
  apply proj1_inj. simpl. rewrite <- Hx. f_equal.
  unfold Fints_coerce. apply proj1_inj. auto.
Qed.

Definition Fink_b (n : nat) (k : Fints (S n))
  (p : {p : Fints (S n) | p <> k}) := If ``p = n then `k else ``p.
Lemma Fink_b_n (n : nat) (k : Fints (S n)) (p : {p : Fints (S n) | p <> k}) :
  Fink_b p < n.
Proof.
  unfold Fink_b. case_if.
  destruct p as [p' Hp']. simpl in e.
  assert (`k <> `p'). apply proj1_inj_neg. auto.
  rewrite e in H. destruct k as [k' Hk']. simpl in *.
  unfold "<" in Hk'. assert (k' <= n). apply le_S_n. auto.
  apply le_lt_or_eq in H0. destruct H0. auto. contradiction.
  destruct p as [p' Hp']. simpl in *. destruct p' as [p'' Hp'']. simpl in *.
  assert (p'' <= n). apply le_S_n. auto.
  apply le_lt_or_eq in H. destruct H. auto. contradiction.
Qed.

Theorem Fink (n : nat) (k : Fints (S n)) :
  cardinality {p : Fints (S n) | p <> k} n.
Proof.
  unfold cardinality.
  pose (u p := exist (fun k => k < n) (Fink_b (n := n) (k := k) p)
                     (Fink_b_n (n := n) (k := k) p) : Fints n).
  exists u. repeat autounfold. split.
  intros x1 x2 H. apply proj1_inj in H.
  unfold u in H. simpl in H. unfold Fink_b in H.
  apply proj1_inj.
  destruct x1 as [x1' Hx1']. destruct x2 as [x2' Hx2']. simpl in *.
  case_if. case_if. assert (`x1' = `x2'). transitivity n. auto. auto.
  apply proj1_inj. auto.
  apply proj1_inj in H. symmetry in H. contradiction.
  case_if. apply proj1_inj in H. contradiction.
  apply proj1_inj. auto.
  intro y. destruct y as [y' Hy']. unfold u.
  assert (exists x, Fink_b (n := n) (k := k) x = y').
  unfold Fink_b. destruct (excluded_middle_informative (y' = `k)).
  assert (n < S n). auto.
  remember (exist (fun k => k < S n) n H) as n'.
  assert (n' <> k). apply proj1_inj_neg. rewrite <- e.
  rewrite Heqn'. simpl. contradict Hy'. destruct Hy'. apply lt_irrefl.
  exists (exist (fun p => p <> k) n' H0). simpl.
  rewrite Heqn'. simpl. rewrite If_l by auto. auto.
  assert (y' < S n). auto.
  remember (exist (fun k => k < S n) y' H) as y''.
  assert (y' = `y''). rewrite Heqy''. auto. rewrite H0 in n0.
  apply proj1_inj_neg in n0.
  exists (exist (fun p => p <> k) y'' n0). simpl.
  rewrite <- H0. apply If_r. contradict Hy'. destruct Hy'. apply lt_irrefl.
  destruct H as [x H]. exists x. destruct H. f_equal.
  apply proof_irrelevance.
Qed.

Theorem cardinality_inj_n :
  forall n n' : nat, forall f : (Fints n) -> (Fints n'), (injection f) -> n' >= n.
Proof.
  simple induction n. intros. apply le_0_n.
  intros n0 H n' f Hinjection.
  remember (fun (k : Fints n0) => f (
    exist (fun p => p < (S n0)) `k (lt_S `k n0 (proj2_sig k)))) as u.
  assert (forall k : Fints n0, u k <> f (Fints_last n0)).
  intro k. rewrite Hequ. apply injection_iff_neg. auto.
  injection. destruct k as [k' Hk']. simpl. intro H1. destruct H1.
  clear H0. apply lt_irrefl in Hk'. auto.
  remember (f (Fints_last n0)) as p.
  destruct n' as [ | n''].
  destruct p as [p' Hp']. clear Heqp. clear H0. apply lt_n_0 in Hp'. contradiction.
  assert (exists z : {x : Fints (S n'') | x <> p} -> Fints n'', bijection z).
  apply Fink. destruct H1 as [z Hzbijection].
  remember (fun (k : Fints n0) => 
    z (exist (fun x => x <> p) (u k) (H0 k))) as v.
  assert (injection v).
  unfold injection. intros x1 x2 H1.
  rewrite Heqv in H1.
  destruct Hzbijection as [Hzinjection _]. apply Hzinjection in H1.
  inversion H1. rewrite Hequ in H3. apply Hinjection in H3. inversion H3.
  apply proj1_inj. auto.
  apply le_n_S. apply H with (f := v). auto.
Qed.

Theorem cardinality_inj :
  forall (T T' : Type) (n n' : nat) (f : T -> T'),
    (cardinality T n) -> (cardinality T' n') -> injection f -> n' >= n.
Proof.
  intros T T' n n' f HcardT HcardT' Hinjection.
  unfold cardinality in *. destruct HcardT as [fT HfTbij].
  destruct HcardT' as [fT' HfT'bij].
  apply bijection_inversible in HfTbij.
  destruct HfTbij as [gT HgT]. destruct HgT as [HgT1 HgT2].
  remember (fun x => fT' (f (gT x))) as u.
  apply cardinality_inj_n with (f := u).
  unfold injection. intros x1 x2 H.
  rewrite Hequ in H. destruct HfT'bij as [HfT'inj _].
  apply HfT'inj in H. apply Hinjection in H.
  assert (fT (gT x1) = fT (gT x2)). f_equal. auto.
  repeat rewrite HgT2 in H0. auto.
Qed.

Lemma cardinality_unique_u (T : Type) (n n' : nat) :
  (cardinality T n) -> (cardinality T n') -> n' >= n.
Proof.
  intros.
  apply cardinality_inj with (f := (fun (x : T) => x)).
  auto. auto. unfold injection. auto.
Qed.

Theorem cardinality_unique (T : Type) (n n' : nat) :
  (cardinality T n) -> (cardinality T n') -> n = n'.
Proof.
  intros H H'.
  assert (n' >= n). apply cardinality_unique_u with (T := T). auto. auto.
  assert (n >= n'). apply cardinality_unique_u with (T := T). auto. auto.
  apply le_antisym. auto. auto.
Qed.

Theorem card_bijection (T T' : Type) (n : nat) (b : T' -> T) (Hb : bijection b) :
  (cardinality T n) <-> (cardinality T' n).
Proof.
  split.
  intro H. destruct H as [u Hu].
  exists (compose u b). apply bij_compose. auto. auto.
  intro H. destruct H as [u Hu].
  apply bijection_inversible in Hb. destruct Hb as [b' Hb'].
  destruct Hb' as [Hb'bid Hbb'id].
  exists (compose u b'). apply bij_compose. auto. apply bijection_inversible.
  exists b. auto.
Qed.

Theorem card_subtype (T : Type) (P Q : T -> Prop) (n : nat) :
  (forall x : T, P x <-> Q x) -> 
    ((cardinality {x : T | P x} n) <-> (cardinality {x : T | Q x} n)).
Proof.
  intro Heq.
  assert (forall x : {x : T | P x}, Q `x).
  intro x. destruct x as [x' Hx']. simpl. apply Heq. auto.
  assert (bijection (fun x : {x : T | P x} => exist _ `x (H x))).
  split.
  intros x1 x2 He. apply proj1_inj in He. simpl in He.
  apply proj1_inj. auto.
  intro y. destruct y as [y' Hy']. assert (P y'). apply Heq. auto.
  exists (exist _ y' H0). apply proj1_inj. auto.
  symmetry.
  apply card_bijection with (b := (fun x : {x : T | P x} => exist _ `x (H x))). auto.
Qed.  

Theorem card_and (T : Type) (P Q : T -> Prop) (n : nat) :
  (cardinality {x : T | P x /\ Q x} n) <-> (cardinality {x : {x : T | P x} | Q `x} n).
Proof.
  assert (forall x : {x : T | P x /\ Q x}, P `x).
  intro x. destruct x as [x' Hx']. destruct Hx'. auto.
  assert (forall x : {x : T | P x /\ Q x}, Q (proj1_sig (exist _ `x (H x)))).
  intro x. simpl. destruct x as [x' Hx']. destruct Hx'. auto.
  assert (bijection (fun x : {x : T | P x /\ Q x} =>
    exist (fun x => Q `x) (exist _ `x (H x)) (H0 x))).
  split.
  intros x1 x2 He. apply proj1_inj in He. simpl in He.
  apply proj1_inj in He. simpl in He. apply proj1_inj. auto.
  intro y. destruct y as [y' Hy']. destruct y' as [y'' Hy'']. simpl in *.
  exists (exist _ y'' (conj Hy'' Hy')).
  apply proj1_inj. simpl. apply proj1_inj. simpl. auto.
  symmetry.
  apply card_bijection with (b := (fun x : {x : T | P x /\ Q x} =>
        exist (fun x : {x | P x} => Q `x) (exist P `x (H x)) (H0 x))). auto.
Qed.

Lemma cb_ex (n m : nat) (k : Fints (n + m)) (H : ~ (`k < n)) :
  `k - n < m.
Proof.
  destruct k as [k' Hk']. simpl in *.
  omega.
Qed.

Definition choose_bijection (T : Type) (P : T -> Prop) (n m : nat)
  (f : Fints n -> {x : T | P x}) (Hf : bijection f)
  (g : Fints m -> {x : T | ~ P x}) (Hg : bijection g) :=
  (fun k : Fints (n + m) =>
    match (excluded_middle_informative (`k < n)) with
      | left H => proj1_sig (f (exist _ `k H))
      | right H => proj1_sig (g (exist _ (`k - n) (cb_ex m k H)))
    end).
Theorem choose_bij (T : Type) (P : T -> Prop) (n m : nat)
  (f : Fints n -> {x : T | P x}) (Hf : bijection f)
  (g : Fints m -> {x : T | ~ P x}) (Hg : bijection g) :
    bijection (choose_bijection P Hf Hg).
Proof.
  unfold choose_bijection.
  apply bijection_inversible.
  apply bijection_inversible in Hf. destruct Hf as [f' Hf]. destruct Hf as [Hf Hf'].
  apply bijection_inversible in Hg. destruct Hg as [g' Hg]. destruct Hg as [Hg Hg'].
  remember (fun x =>
    match (excluded_middle_informative (P x)) with
      | left H => proj1_sig (f' (exist _ x H))
      | right H => proj1_sig (g' (exist _ x H)) + n
    end) as h'.
  assert (forall x : T, h' x < n + m).
  intro x. rewrite Heqh'.
  ex_mid_destruct.
  destruct (f' _). simpl. omega.
  destruct (g' _). simpl. omega.
  exists (fun x => exist _ (h' x) (H x)).
  split.
  intro x. destruct x as [x' Hx'].
  apply proj1_inj. simpl.
  ex_mid_destruct.
  rewrite Heqh'. remember (f _) as y. destruct y as [y' Hy']. simpl.
  ex_mid_destruct.
  assert (exist (fun x : T => P x) y' Hy' = exist (fun x : T => P x) y' p).
  apply proj1_inj. auto.
  rewrite <- H0. rewrite Heqy. rewrite Hf. auto.
  contradiction.
  rewrite Heqh'. remember (g _ ) as y. destruct y as [y' Hy']. simpl.
  ex_mid_destruct.
  contradiction.
  assert (exist (fun x : T => ~ P x) y' Hy' = exist (fun x : T => ~ P x) y' n1).
  apply proj1_inj. auto.
  rewrite <- H0. rewrite Heqy. rewrite Hg. simpl. omega.
  intro y.
  destruct (excluded_middle_informative (P y)).
  simpl in *.
  assert (h' y = proj1_sig (f' (exist P y p))).
  rewrite Heqh'. ex_mid_destruct.
  f_equal. f_equal. apply proj1_inj. auto. contradiction.
  ex_mid_destruct.
  remember (f' _) as x. destruct x as [x' Hx']. simpl in *.
  generalize l.
  rewrite H0. intro l0.
  assert (exist (fun p0 : nat => p0 < n) x' Hx' = exist (fun p0 : nat => p0 < n) x' l0).
  apply proj1_inj. auto.
  rewrite <- H1. rewrite Heqx. rewrite Hf'. auto.
  destruct (f' _). simpl in H0. omega.
  simpl.
  assert (h' y = proj1_sig (g' (exist _ y n0)) + n).
  rewrite Heqh'. ex_mid_destruct.
  contradiction. f_equal. f_equal. f_equal. apply proj1_inj. auto.
  ex_mid_destruct. omega.
  remember (g' _) as x. destruct x as [x' Hx']. simpl in *.
  assert (exist (fun p : nat => p < m) x' Hx' = exist (fun p : nat => p < m) (h' y - n)
       (cb_ex m (exist (fun p : nat => p < n + m) (h' y) (H y)) n1)).
  apply proj1_inj. simpl. omega.
  rewrite <- H1. rewrite Heqx. rewrite Hg'. auto.
Qed.
   
Theorem disjoint_union_cardinality (T : Type) (P : T -> Prop) :
  forall n m : nat,
    (cardinality {x : T | P x} n) -> (cardinality {x : T | ~ P x} m)
                                  -> (cardinality T (n + m)).
Proof.
  intros n m Hn Hm.
  apply inv_bijection in Hn. apply inv_bijection in Hm.
  destruct Hn as [fn Hfn]. destruct Hm as [fm Hfm].
  apply inv_bijection.
  exists (choose_bijection P Hfn Hfm). apply choose_bij.
Qed.

Theorem subtype_finite_n :
  forall (n : nat) (P : (Fints n) -> Prop), (finite {x : (Fints n) | P x}).
Proof.
  simple induction n.
  intro. exists 0. exists (fun x => `x).
  split. intros x1 x2 H. destruct x1 as [x1' Hx1'].
  destruct x1' as [x1'' Hx1'']. omega.
  intro y. destruct y as [y' Hy']. omega.
  intros n0 H P.
  destruct (H (fun x => P (Fints_coerce (le_n_Sn n0) x))) as [k H'].
  destruct H' as [b Hb]. destruct Hb as [Hbinj Hbsurj].
  destruct (classic (P (Fints_last n0))).
  exists (S k).
  assert (forall x : Fints (S n0), ~ (x = Fints_last n0) -> `x < n0).
  intros x H1. destruct x as [x' Hx']. unfold Fints_last in H1.
  apply proj1_inj_neg in H1. simpl in *. omega.
  assert (forall (x : {x : Fints (S n0) | P x}) (U : ~ (`x = Fints_last n0)),
    P (Fints_coerce (le_n_Sn n0) (exist (fun k => k < n0) ``x (H1 `x U)))).
  unfold Fints_coerce. simpl. destruct x as [x' Hx']. destruct x' as [x'' Hx''].
  simpl. intro U.
  assert (exist (fun p : nat => p < S n0) x'' Hx'' = exist (fun p : nat => p < S n0) x''
     (lt_le_trans x'' n0 (S n0)
        (H1 (exist (fun p : nat => p < S n0) x'' Hx'') U) (le_n_Sn n0))).
  apply proj1_inj. auto. rewrite <- H2. auto.
  exists (fun x => 
    match (excluded_middle_informative (`x = Fints_last n0)) with
      | left _ => Fints_last k
      | right U => Fints_coerce (le_n_Sn k) (b (exist (fun p => P (Fints_coerce (le_n_Sn n0) p)) (exist _ ``x (H1 `x U)) (H2 x U)))
    end).
  split.
  intros x1 x2 He.
  destruct (excluded_middle_informative (`x1 = Fints_last n0)).
  destruct (excluded_middle_informative (`x2 = Fints_last n0)).
  rewrite <- e0 in e. apply proj1_inj. auto.
  remember (b _) as y. destruct y. unfold Fints_last in He. unfold Fints_coerce in He.
  apply proj1_inj in He. simpl in He. omega.
  destruct (excluded_middle_informative (`x2 = Fints_last n0)).
  remember (b _) as y. destruct y. unfold Fints_last in He. unfold Fints_coerce in He.
  apply proj1_inj in He. simpl in He. omega.
  unfold Fints_coerce in He. apply proj1_inj in He. simpl in He.
  apply proj1_inj in He. apply Hbinj in He. apply proj1_inj in He. simpl in He.
  apply proj1_inj in He. simpl in He. apply proj1_inj in He. apply proj1_inj. auto.
  intro y. destruct y as [y' Hy'].
  destruct (excluded_middle_informative (y' = k)).
  exists (exist _ (Fints_last n0) H0). simpl.
  destruct (excluded_middle_informative (Fints_last n0 = Fints_last n0)).
  unfold Fints_last. apply proj1_inj. auto.
  congruence.
  assert (y' < k). omega.
  destruct (Hbsurj (exist _ y' H3)).
  destruct x as [x' Hx'].
  exists (exist _ (Fints_coerce (le_n_Sn n0) x') Hx').
  simpl.
  assert (forall U, (b
         (exist (fun p : Fints n0 => P (Fints_coerce (le_n_Sn n0) p))
            (exist (fun p : nat => p < n0) `x'
               (H1 (Fints_coerce (le_n_Sn n0) x') U))
            (H2 (exist P (Fints_coerce (le_n_Sn n0) x') Hx') U)))
           = exist _ y' H3).
  intro U. rewrite <- H4. f_equal. apply proj1_inj. simpl.
  apply proj1_inj. auto.
  match goal with [|-context[excluded_middle_informative ?P]] => destruct (excluded_middle_informative P) end.
  destruct x' as [x'' Hx'']. unfold Fints_coerce in e. unfold Fints_last in e.
  apply proj1_inj in e. simpl in e. omega.
  apply proj1_inj. unfold Fints_coerce. simpl. rewrite H5. auto.
  exists k.
  assert (forall x : {x : Fints (S n0) | P x}, ``x < n0).
  destruct x as [x' Hx']. destruct x' as [x'' Hx''].
  assert (x'' <> n0). intro. assert (Fints_last n0 = exist _ x'' Hx'').
   unfold Fints_last. apply proj1_inj. auto. rewrite H2 in H0. contradiction.
  simpl. omega.
  assert (forall x : {x : Fints (S n0) | P x}, P (Fints_coerce (le_n_Sn n0) (exist _ ``x (H1 x)))).
  intro x. destruct x as [x' Hx']. unfold Fints_coerce. simpl.
  assert (x' = exist (fun p : nat => p < S n0) `x'
     (lt_le_trans `x' n0 (S n0)
        (H1 (exist (fun x : Fints (S n0) => P x) x' Hx')) (le_n_Sn n0))).
  apply proj1_inj. auto. rewrite <- H2. auto.
  exists (fun x => b (exist (fun p => P (Fints_coerce (le_n_Sn n0) p)) (exist _ ``x (H1 x)) (H2 x))).
  split.
  intros x1 x2 He.
  apply Hbinj in He. apply proj1_inj in He. simpl in He. apply proj1_inj in He.
  simpl in He. apply proj1_inj in He. apply proj1_inj. auto.
  intro y.
  destruct (Hbsurj y) as [x Hx].
  exists (exist _ (Fints_coerce (le_n_Sn n0) `x) (proj2_sig x)).
  simpl. rewrite <- Hx. f_equal. apply proj1_inj. simpl. apply proj1_inj. auto.
Qed.

Theorem subtype_finite (T : Type) (H : finite T) (P : T -> Prop) :
  finite {x : T | P x}.
Proof.
  destruct H as [n H]. destruct H as [b Hb].
  assert (inversible b). apply bijection_inversible. auto.
  destruct H as [b' Hb']. destruct Hb' as [Hidb' Hidb].
  assert (finite {x : Fints n | P (b' x)}). apply subtype_finite_n.
  destruct H as [k H]. destruct H as [c Hc]. destruct Hc as [Hcinj Hcsurj].
  assert (forall x : {x : T | P x}, P (b' (b `x))).
  intro x. destruct x as [x' Hx']. rewrite Hidb'. auto.
  exists k. exists (fun x => c (exist (fun p => P (b' p)) (b `x) (H x))).
  split.
  intros x1 x2 He. apply Hcinj in He. apply proj1_inj in He. simpl in He.
  apply Hb in He. apply proj1_inj. auto.
  intro y. destruct (Hcsurj y) as [x Hx].
  destruct x as [x' Hx'].
  exists (exist _ (b' x') Hx'). rewrite <- Hx. f_equal.
  apply proj1_inj. simpl. auto.
Qed.

End FiniteTypes.