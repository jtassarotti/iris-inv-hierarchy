(** This file proves the basic laws of the HeapLang program logic by applying
the Iris lifting lemmas. *)

From iris.algebra Require Import lib.frac_auth numbers auth.
From iris.proofmode Require Import tactics.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Export gen_heap proph_map gen_inv_heap invariants.
From iris.program_logic Require Export weakestpre total_weakestpre.
From iris.program_logic Require Import ectx_lifting total_ectx_lifting.
From iris.heap_lang Require Export class_instances.
From iris.heap_lang Require Import tactics notation.
From iris.prelude Require Import options.

Class heapG Σ := HeapG {
  heapG_invG : invG Σ;
  heapG_crashG : crashG Σ;
  heapG_gen_heapG :> gen_heapG loc (option val) Σ;
  heapG_inv_heapG :> inv_heapG loc (option val) Σ;
  heapG_proph_mapG :> proph_mapG proph_id (val * val) Σ;
  heapG_credit_inG :> inG Σ (frac_authR natR);
  heapG_credit_name : gname;
}.

Section credit.
Context `{heapG Σ}.

Definition cred_frag (n : nat) : iProp Σ :=
  (∃ q, own (heapG_credit_name) (◯F{q} n)).

Definition cred_auth `{heapG Σ} (ns : nat) : iProp Σ :=
  (own (heapG_credit_name) (●F ns)).

Lemma cred_auth_frag_incr (ns n: nat) :
  cred_auth ns ∗ cred_frag n ==∗
  cred_auth (S ns) ∗ cred_frag (S n).
Proof.
  iIntros "(Hγ&Hγf)".
  iDestruct "Hγf" as (q) "Hγf".
  iMod (own_update_2 with "Hγ Hγf") as "[Hγ Hγf]".
  { apply frac_auth_update, (nat_local_update _ _ (S ns) (S n)); lia. }
  iFrame. iExists _. eauto.
Qed.

Lemma cred_auth_frag_decr (ns n: nat) :
  cred_auth ns ∗ cred_frag (S n) ==∗
  ∃ ns', ⌜ ns = S ns' ⌝ ∗ cred_auth ns' ∗ cred_frag n.
Proof.
  iIntros "(Hγ&Hγf)".
  iDestruct "Hγf" as (q) "Hγf".
  iDestruct (own_valid_2 with "Hγ Hγf") as % ?%frac_auth_included_total%nat_included.
  destruct ns as [| ns']; first lia.
  iMod (own_update_2 with "Hγ Hγf") as "[Hγ Hγf]".
  { apply frac_auth_update, (nat_local_update _ _ ns' n); lia. }
  iExists _. iFrame. iModIntro. iSplit; first eauto. iExists _. eauto.
Qed.

Definition cred_interp ns : iProp Σ :=
  cred_auth ns ∗ cred_frag 0.

Lemma cred_frag_split ns1 ns2 :
  cred_frag (ns1 + ns2) -∗ cred_frag ns1 ∗ cred_frag ns2.
Proof.
  iIntros "H". iDestruct "H" as (q) "H".
  replace q with (q/2 + q/2)%Qp by apply Qp_div_2.
  rewrite frac_auth_frag_op.
  iDestruct "H" as "(H1&H2)".
  iSplitL "H1".
  { iExists _. iFrame. }
  { iExists _. iFrame. }
Qed.

Lemma cred_interp_incr ns :
  cred_interp ns ==∗ cred_interp (S ns) ∗ cred_frag 1.
Proof.
  iIntros "H".
  iMod (cred_auth_frag_incr with "H") as "(?&H)".
  iEval (replace 1 with (1 + 0) by lia) in "H".
  iDestruct (cred_frag_split with "H") as "($&$)".
  eauto.
Qed.

Lemma cred_interp_decr ns n :
  cred_interp ns ∗ cred_frag (S n) ==∗
  ∃ ns', ⌜ ns = S ns' ⌝ ∗ cred_interp ns' ∗ cred_frag n.
Proof.
  iIntros "((H&?)&Hfrag)".
  iMod (cred_auth_frag_decr with "[$H $Hfrag]") as (ns' Heq) "(?&H)". subst.
  iExists ns'. iModIntro. iSplit; eauto.
  iFrame.
Qed.

End credit.

Program Global Instance heapG_irisG `{!heapG Σ} : irisG heap_lang Σ := {
  iris_invG := heapG_invG;
  iris_crashG := heapG_crashG;
  state_interp σ ns κs _ :=
    (cred_interp ns ∗ gen_heap_interp σ.(heap) ∗ proph_map_interp κs σ.(used_proph_id))%I;
  fork_post _ := True%I;
  num_laters_per_step n := n;
}.
Next Obligation.
  iIntros (?? σ ns κs nt) "(Hcred&Hσ&Hproph)".
  iFrame. by iMod (cred_interp_incr with "Hcred") as "($&_)".
Qed.

(** Since we use an [option val] instance of [gen_heap], we need to overwrite
the notations.  That also helps for scopes and coercions. *)
(** FIXME: Refactor these notations using custom entries once Coq bug #13654
has been fixed. *)
Notation "l ↦{ dq } v" := (mapsto (L:=loc) (V:=option val) l dq (Some v%V))
  (at level 20, format "l  ↦{ dq }  v") : bi_scope.
Notation "l ↦□ v" := (mapsto (L:=loc) (V:=option val) l DfracDiscarded (Some v%V))
  (at level 20, format "l  ↦□  v") : bi_scope.
Notation "l ↦{# q } v" := (mapsto (L:=loc) (V:=option val) l (DfracOwn q) (Some v%V))
  (at level 20, format "l  ↦{# q }  v") : bi_scope.
Notation "l ↦ v" := (mapsto (L:=loc) (V:=option val) l (DfracOwn 1) (Some v%V))
  (at level 20, format "l  ↦  v") : bi_scope.

(** Same for [gen_inv_heap], except that these are higher-order notations so to
make setoid rewriting in the predicate [I] work we need actual definitions
here. *)
Section definitions.
  Context `{!heapG Σ}.
  Definition inv_mapsto_own (l : loc) (v : val) (I : val → Prop) : iProp Σ :=
    inv_mapsto_own l (Some v) (from_option I False).
  Definition inv_mapsto (l : loc) (I : val → Prop) : iProp Σ :=
    inv_mapsto l (from_option I False).
End definitions.

Global Instance: Params (@inv_mapsto_own) 4 := {}.
Global Instance: Params (@inv_mapsto) 3 := {}.

Notation inv_heap_inv := (inv_heap_inv loc (option val)).
Notation "l '↦_' I □" := (inv_mapsto l I%stdpp%type)
  (at level 20, I at level 9, format "l  '↦_' I  '□'") : bi_scope.
Notation "l ↦_ I v" := (inv_mapsto_own l v I%stdpp%type)
  (at level 20, I at level 9, format "l  ↦_ I  v") : bi_scope.

Section lifting.
Context `{!heapG Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ Ψ : val → iProp Σ.
Implicit Types efs : list expr.
Implicit Types σ : state.
Implicit Types v : val.
Implicit Types l : loc.

Lemma state_interp_step_incr σ ns κs nt :
  state_interp σ ns κs nt ==∗
  state_interp σ (S ns) κs nt.
Proof.
  iIntros "(Hcred&Hσ&Hproph)".
  iFrame. by iMod (cred_interp_incr with "Hcred") as "($&_)".
Qed.

Lemma state_interp_step_incr' σ ns κs nt :
  state_interp σ ns κs nt ==∗
  state_interp σ (S ns) κs nt ∗ cred_frag 1.
Proof.
  iIntros "(Hcred&Hσ&Hproph)".
  iFrame. by iMod (cred_interp_incr with "Hcred") as "($&$)".
Qed.

Lemma state_interp_step_decr σ ns κs nt n:
  state_interp σ ns κs nt ∗ cred_frag (S n) ==∗
  ∃ ns', ⌜ ns = S ns' ⌝ ∗ state_interp σ ns' κs nt ∗ cred_frag n.
Proof.
  iIntros "((Hcred&Hσ&Hproph)&Hfrag)".
  iFrame. iMod (cred_interp_decr with "[$]") as (ns' Heq) "(?&$)".
  iExists _. iModIntro. iFrame. eauto.
Qed.

Lemma wp_pure_later_cred s E e1 e2 φ Φ :
  PureExec φ 1 e1 e2 → φ → ▷ WP e2 @ s; E {{ v, cred_frag 1 -∗ Φ v }} -∗ WP e1 @ s; E {{ v, Φ v }}.
Proof.
  iIntros (HPure Hφ) "Hwp".
  rewrite /PureExec in HPure. apply HPure in Hφ.
  iApply wp_lift_step.
  {
    eapply (reducible_not_val _ inhabitant), reducible_no_obs_reducible.
    inversion Hφ. eapply pure_step_safe; eauto.
  }
  iIntros (σ1 ns κ κs nt) "(Hcred&Hσ)".
  iMod (cred_interp_incr with "[$]") as "($&Hcred)".
  iApply (fupd_mask_intro); first by set_solver+.
  iIntros "H".
  iSplit.
  {
    destruct s; auto. iPureIntro. eapply reducible_no_obs_reducible.
    inversion Hφ. eapply pure_step_safe; eauto.
  }
  iIntros "!>" (v2 σ2 efs Hstep); inv_head_step.
  inversion Hφ; subst. eapply pure_step_det in Hstep; eauto.
  destruct Hstep as (->&->&?&?). rewrite /=. iFrame.
  subst. inversion H1; subst. rewrite big_sepL_nil.
  iMod "H". iModIntro. iSplitL; last done.
  iApply (wp_wand with "Hwp"). iIntros (?) "Hw".
  iApply "Hw". iFrame.
Qed.

Lemma wp_later_cred_use s E e Φ :
  language.to_val e = None →
  cred_frag 1 -∗
  ▷ WP e @ s; E {{ v, cred_frag 1 -∗ Φ v }} -∗
  WP e @ s; E {{ Φ }}.
Proof.
  iIntros (Hnval) "Hcred Hwp".
  rewrite ?wp_unfold /wp_pre.
  rewrite Hnval.
  iIntros (q σ1 ns κ κs nt) "Hσ HNC".
  iMod (state_interp_step_decr with "[$]") as (ns' ->) "(Hσ&Hcred)".
  iApply (fupd_mask_weaken ∅); first by set_solver+.
  iIntros "H". iModIntro. simpl. iModIntro. iNext. iModIntro. iMod "H" as "_".
  iSpecialize ("Hwp" $! _ _ _ _ _ 0 with "[Hσ] [$]").
  { iFrame. }
  iMod "Hwp". iApply (step_fupdN_wand with "Hwp").
  iNext. iIntros "($&H)".
  iIntros. iMod ("H" with "[//]") as "(Hσ&Hwp&$)".
  iMod (state_interp_step_incr' _ _ _ 0 with "[$]") as "(Hσ&Hcred')".
  iFrame. iModIntro.
  iApply (wp_wand with "Hwp").
  iIntros (?) "H". iApply "H". iFrame.
Qed.

Lemma wp_later_cred_inv N E e `{Atomic _ StronglyAtomic e} Φ P :
  ↑N ⊆ E →
  language.to_val e = None →
  inv N (cred_frag 1 ∗ P) -∗
  (P -∗ WP e @ E ∖ ↑N {{ v, P ∗ Φ v }}) -∗
  WP e @ E {{ Φ }}.
Proof.
  iIntros (? Hnval) "Hcred Hwp".
  iInv "Hcred" as "(>H&HP)".
  iApply (wp_later_cred_use with "[$]"); auto.
  iNext. iSpecialize ("Hwp" with "[$]").
  iApply (wp_mono with "Hwp").
  rewrite ?wp_unfold /wp_pre.
  iIntros (?) "(HP&HΦ) Hcred". iFrame. eauto.
Qed.

(** Recursive functions: we do not use this lemmas as it is easier to use Löb
induction directly, but this demonstrates that we can state the expected
reasoning principle for recursive functions, without any visible ▷. *)
Lemma wp_rec_löb s E f x e Φ Ψ :
  □ ( □ (∀ v, Ψ v -∗ WP (rec: f x := e)%V v @ s; E {{ Φ }}) -∗
     ∀ v, Ψ v -∗ WP (subst' x v (subst' f (rec: f x := e) e)) @ s; E {{ Φ }}) -∗
  ∀ v, Ψ v -∗ WP (rec: f x := e)%V v @ s; E {{ Φ }}.
Proof.
  iIntros "#Hrec". iLöb as "IH". iIntros (v) "HΨ".
  iApply lifting.wp_pure_step_later; first done.
  iNext. iApply ("Hrec" with "[] HΨ"). iIntros "!>" (w) "HΨ".
  iApply ("IH" with "HΨ").
Qed.

(** Fork: Not using Texan triples to avoid some unnecessary [True] *)
Lemma wp_fork s E e Φ :
  ▷ WP e @ s; ⊤ {{ _, True }} -∗ ▷ Φ (LitV LitUnit) -∗ WP Fork e @ s; E {{ Φ }}.
Proof.
  iIntros "He HΦ". iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1 ns κ κs nt) "(Hcred&Hσ) !>"; iSplit; first by eauto with head_step.
  iIntros "!>" (v2 σ2 efs Hstep); inv_head_step.
  iMod (cred_interp_incr with "[$]") as "($&_)". by iFrame.
Qed.

Lemma twp_fork s E e Φ :
  WP e @ s; ⊤ [{ _, True }] -∗ Φ (LitV LitUnit) -∗ WP Fork e @ s; E [{ Φ }].
Proof.
  iIntros "He HΦ". iApply twp_lift_atomic_head_step; [done|].
  iIntros (σ1 ns κs nt) "(Hcred&Hσ) !>"; iSplit; first by eauto with head_step.
  iIntros (κ v2 σ2 efs Hstep); inv_head_step.
  iMod (cred_interp_incr with "[$]") as "($&_)". by iFrame.
Qed.

(** Heap *)

(** We need to adjust the [gen_heap] and [gen_inv_heap] lemmas because of our
value type being [option val]. *)

Lemma mapsto_valid l dq v : l ↦{dq} v -∗ ⌜✓ dq⌝.
Proof. apply mapsto_valid. Qed.
Lemma mapsto_valid_2 l dq1 dq2 v1 v2 :
  l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
Proof.
  iIntros "H1 H2". iDestruct (mapsto_valid_2 with "H1 H2") as %[? [=?]]. done.
Qed.
Lemma mapsto_agree l dq1 dq2 v1 v2 : l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ ⌜v1 = v2⌝.
Proof. iIntros "H1 H2". iDestruct (mapsto_agree with "H1 H2") as %[=?]. done. Qed.

Lemma mapsto_combine l dq1 dq2 v1 v2 :
  l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ l ↦{dq1 ⋅ dq2} v1 ∗ ⌜v1 = v2⌝.
Proof.
  iIntros "Hl1 Hl2". iDestruct (mapsto_combine with "Hl1 Hl2") as "[$ Heq]".
  by iDestruct "Heq" as %[= ->].
Qed.

Lemma mapsto_frac_ne l1 l2 dq1 dq2 v1 v2 :
  ¬ ✓(dq1 ⋅ dq2) → l1 ↦{dq1} v1 -∗ l2 ↦{dq2} v2 -∗ ⌜l1 ≠ l2⌝.
Proof. apply mapsto_frac_ne. Qed.
Lemma mapsto_ne l1 l2 dq2 v1 v2 : l1 ↦ v1 -∗ l2 ↦{dq2} v2 -∗ ⌜l1 ≠ l2⌝.
Proof. apply mapsto_ne. Qed.

Lemma mapsto_persist l dq v : l ↦{dq} v ==∗ l ↦□ v.
Proof. apply mapsto_persist. Qed.

Global Instance inv_mapsto_own_proper l v :
  Proper (pointwise_relation _ iff ==> (≡)) (inv_mapsto_own l v).
Proof.
  intros I1 I2 HI. rewrite /inv_mapsto_own. f_equiv=>-[w|]; last done.
  simpl. apply HI.
Qed.
Global Instance inv_mapsto_proper l :
  Proper (pointwise_relation _ iff ==> (≡)) (inv_mapsto l).
Proof.
  intros I1 I2 HI. rewrite /inv_mapsto. f_equiv=>-[w|]; last done.
  simpl. apply HI.
Qed.

Lemma make_inv_mapsto l v (I : val → Prop) E :
  ↑inv_heapN ⊆ E →
  I v →
  inv_heap_inv -∗ l ↦ v ={E}=∗ l ↦_I v.
Proof. iIntros (??) "#HI Hl". iApply make_inv_mapsto; done. Qed.
Lemma inv_mapsto_own_inv l v I : l ↦_I v -∗ l ↦_I □.
Proof. apply inv_mapsto_own_inv. Qed.

Lemma inv_mapsto_own_acc_strong E :
  ↑inv_heapN ⊆ E →
  inv_heap_inv ={E, E ∖ ↑inv_heapN}=∗ ∀ l v I, l ↦_I v -∗
    (⌜I v⌝ ∗ l ↦ v ∗ (∀ w, ⌜I w ⌝ -∗ l ↦ w ==∗
      inv_mapsto_own l w I ∗ |={E ∖ ↑inv_heapN, E}=> True)).
Proof.
  iIntros (?) "#Hinv".
  iMod (inv_mapsto_own_acc_strong with "Hinv") as "Hacc"; first done.
  iIntros "!>" (l v I) "Hl". iDestruct ("Hacc" with "Hl") as "(% & Hl & Hclose)".
  iFrame "%∗". iIntros (w) "% Hl". iApply "Hclose"; done.
Qed.

Lemma inv_mapsto_own_acc E l v I:
  ↑inv_heapN ⊆ E →
  inv_heap_inv -∗ l ↦_I v ={E, E ∖ ↑inv_heapN}=∗
    (⌜I v⌝ ∗ l ↦ v ∗ (∀ w, ⌜I w ⌝ -∗ l ↦ w ={E ∖ ↑inv_heapN, E}=∗ l ↦_I w)).
Proof.
  iIntros (?) "#Hinv Hl".
  iMod (inv_mapsto_own_acc with "Hinv Hl") as "(% & Hl & Hclose)"; first done.
  iFrame "%∗". iIntros "!>" (w) "% Hl". iApply "Hclose"; done.
Qed.

Lemma inv_mapsto_acc l I E :
  ↑inv_heapN ⊆ E →
  inv_heap_inv -∗ l ↦_I □ ={E, E ∖ ↑inv_heapN}=∗
    ∃ v, ⌜I v⌝ ∗ l ↦ v ∗ (l ↦ v ={E ∖ ↑inv_heapN, E}=∗ ⌜True⌝).
Proof.
  iIntros (?) "#Hinv Hl".
  iMod (inv_mapsto_acc with "Hinv Hl") as ([v|]) "(% & Hl & Hclose)"; [done| |done].
  iIntros "!>". iExists (v). iFrame "%∗".
Qed.

(** The usable rules for [allocN] stated in terms of the [array] proposition
are derived in te file [array]. *)
Lemma heap_array_to_seq_meta l vs (n : nat) :
  length vs = n →
  ([∗ map] l' ↦ _ ∈ heap_array l vs, meta_token l' ⊤) -∗
  [∗ list] i ∈ seq 0 n, meta_token (l +ₗ (i : nat)) ⊤.
Proof.
  iIntros (<-) "Hvs". iInduction vs as [|v vs] "IH" forall (l)=> //=.
  rewrite big_opM_union; last first.
  { apply map_disjoint_spec=> l' v1 v2 /lookup_singleton_Some [-> _].
    intros (j&w&?&Hjl&?&?)%heap_array_lookup.
    rewrite loc_add_assoc -{1}[l']loc_add_0 in Hjl. simplify_eq; lia. }
  rewrite loc_add_0 -fmap_S_seq big_sepL_fmap.
  setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
  setoid_rewrite <-loc_add_assoc.
  rewrite big_opM_singleton; iDestruct "Hvs" as "[$ Hvs]". by iApply "IH".
Qed.

Lemma heap_array_to_seq_mapsto l v (n : nat) :
  ([∗ map] l' ↦ ov ∈ heap_array l (replicate n v), gen_heap.mapsto l' (DfracOwn 1) ov) -∗
  [∗ list] i ∈ seq 0 n, (l +ₗ (i : nat)) ↦ v.
Proof.
  iIntros "Hvs". iInduction n as [|n] "IH" forall (l); simpl.
  { done. }
  rewrite big_opM_union; last first.
  { apply map_disjoint_spec=> l' v1 v2 /lookup_singleton_Some [-> _].
    intros (j&w&?&Hjl&_)%heap_array_lookup.
    rewrite loc_add_assoc -{1}[l']loc_add_0 in Hjl. simplify_eq; lia. }
  rewrite loc_add_0 -fmap_S_seq big_sepL_fmap.
  setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
  setoid_rewrite <-loc_add_assoc.
  rewrite big_opM_singleton; iDestruct "Hvs" as "[$ Hvs]". by iApply "IH".
Qed.

Lemma twp_allocN_seq s E v n :
  (0 < n)%Z →
  [[{ True }]] AllocN (Val $ LitV $ LitInt $ n) (Val v) @ s; E
  [[{ l, RET LitV (LitLoc l); [∗ list] i ∈ seq 0 (Z.to_nat n),
      (l +ₗ (i : nat)) ↦ v ∗ meta_token (l +ₗ (i : nat)) ⊤ }]].
Proof.
  iIntros (Hn Φ) "_ HΦ". iApply twp_lift_atomic_head_step_no_fork; first done.
  iIntros (σ1 ns κs nt) "[Hcred [Hσ Hκs]] !>"; iSplit; first by destruct n; auto with lia head_step.
  iIntros (κ v2 σ2 efs Hstep); inv_head_step.
  iMod (gen_heap_alloc_big _ (heap_array _ (replicate (Z.to_nat n) v)) with "Hσ")
    as "(Hσ & Hl & Hm)".
  { apply heap_array_map_disjoint.
    rewrite replicate_length Z2Nat.id; auto with lia. }
  iMod (cred_interp_incr with "[$]") as "($&_)".
  iModIntro; do 2 (iSplit; first done). iFrame "Hσ Hκs".
  iApply "HΦ".
  iApply big_sepL_sep. iSplitL "Hl".
  - by iApply heap_array_to_seq_mapsto.
  - iApply (heap_array_to_seq_meta with "Hm"). by rewrite replicate_length.
Qed.
Lemma wp_allocN_seq s E v n :
  (0 < n)%Z →
  {{{ True }}} AllocN (Val $ LitV $ LitInt $ n) (Val v) @ s; E
  {{{ l, RET LitV (LitLoc l); [∗ list] i ∈ seq 0 (Z.to_nat n),
      (l +ₗ (i : nat)) ↦ v ∗ meta_token (l +ₗ (i : nat)) ⊤ }}}.
Proof.
  iIntros (Hn Φ) "_ HΦ". iApply (twp_wp_step with "HΦ").
  iApply twp_allocN_seq; [by auto..|]; iIntros (l) "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_alloc s E v :
  [[{ True }]] Alloc (Val v) @ s; E [[{ l, RET LitV (LitLoc l); l ↦ v ∗ meta_token l ⊤ }]].
Proof.
  iIntros (Φ) "_ HΦ". iApply twp_allocN_seq; [auto with lia..|].
  iIntros (l) "/= (? & _)". rewrite loc_add_0. iApply "HΦ"; iFrame.
Qed.
Lemma wp_alloc s E v :
  {{{ True }}} Alloc (Val v) @ s; E {{{ l, RET LitV (LitLoc l); l ↦ v ∗ meta_token l ⊤ }}}.
Proof.
  iIntros (Φ) "_ HΦ". iApply (twp_wp_step with "HΦ").
  iApply twp_alloc; [by auto..|]; iIntros (l) "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_free s E l v :
  [[{ l ↦ v }]] Free (Val $ LitV $ LitLoc l) @ s; E
  [[{ RET LitV LitUnit; True }]].
Proof.
  iIntros (Φ) "Hl HΦ". iApply twp_lift_atomic_head_step_no_fork; first done.
  iIntros (σ1 ns κs nt) "[Hcred [Hσ Hκs]] !>". iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto with head_step.
  iIntros (κ v2 σ2 efs Hstep); inv_head_step.
  iMod (gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iMod (cred_interp_incr with "[$]") as "($&_)".
  iModIntro. iSplit; first done. iSplit; first done. iFrame. by iApply "HΦ".
Qed.
Lemma wp_free s E l v :
  {{{ ▷ l ↦ v }}} Free (Val $ LitV (LitLoc l)) @ s; E
  {{{ RET LitV LitUnit; True }}}.
Proof.
  iIntros (Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_free with "H"); [by auto..|]; iIntros "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_load s E l dq v :
  [[{ l ↦{dq} v }]] Load (Val $ LitV $ LitLoc l) @ s; E [[{ RET v; l ↦{dq} v }]].
Proof.
  iIntros (Φ) "Hl HΦ". iApply twp_lift_atomic_head_step_no_fork; first done.
  iIntros (σ1 ns κs nt) "[Hcred [Hσ Hκs]] !>". iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto with head_step.
  iIntros (κ v2 σ2 efs Hstep); inv_head_step.
  iMod (cred_interp_incr with "[$]") as "($&_)".
  iModIntro; iSplit=> //. iSplit; first done. iFrame. by iApply "HΦ".
Qed.
Lemma wp_load s E l dq v :
  {{{ ▷ l ↦{dq} v }}} Load (Val $ LitV $ LitLoc l) @ s; E {{{ RET v; l ↦{dq} v }}}.
Proof.
  iIntros (Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_load with "H"). iIntros "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_store s E l v' v :
  [[{ l ↦ v' }]] Store (Val $ LitV $ LitLoc l) (Val v) @ s; E
  [[{ RET LitV LitUnit; l ↦ v }]].
Proof.
  iIntros (Φ) "Hl HΦ". iApply twp_lift_atomic_head_step_no_fork; first done.
  iIntros (σ1 ns κs nt) "[Hcred [Hσ Hκs]] !>". iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto with head_step.
  iIntros (κ v2 σ2 efs Hstep); inv_head_step.
  iMod (gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iMod (cred_interp_incr with "[$]") as "($&_)".
  iModIntro. iSplit; first done. iSplit; first done. iFrame. by iApply "HΦ".
Qed.
Lemma wp_store s E l v' v :
  {{{ ▷ l ↦ v' }}} Store (Val $ LitV (LitLoc l)) (Val v) @ s; E
  {{{ RET LitV LitUnit; l ↦ v }}}.
Proof.
  iIntros (Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_store with "H"); [by auto..|]; iIntros "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_cmpxchg_fail s E l dq v' v1 v2 :
  v' ≠ v1 → vals_compare_safe v' v1 →
  [[{ l ↦{dq} v' }]] CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  [[{ RET PairV v' (LitV $ LitBool false); l ↦{dq} v' }]].
Proof.
  iIntros (?? Φ) "Hl HΦ". iApply twp_lift_atomic_head_step_no_fork; first done.
  iIntros (σ1 ns κs nt) "[Hcred [Hσ Hκs]] !>". iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto with head_step.
  iIntros (κ v2' σ2 efs Hstep); inv_head_step.
  rewrite bool_decide_false //.
  iMod (cred_interp_incr with "[$]") as "($&_)".
  iModIntro; iSplit; first done. iSplit; first done. iFrame. by iApply "HΦ".
Qed.
Lemma wp_cmpxchg_fail s E l dq v' v1 v2 :
  v' ≠ v1 → vals_compare_safe v' v1 →
  {{{ ▷ l ↦{dq} v' }}} CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  {{{ RET PairV v' (LitV $ LitBool false); l ↦{dq} v' }}}.
Proof.
  iIntros (?? Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_cmpxchg_fail with "H"); [by auto..|]; iIntros "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_cmpxchg_suc s E l v1 v2 v' :
  v' = v1 → vals_compare_safe v' v1 →
  [[{ l ↦ v' }]] CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  [[{ RET PairV v' (LitV $ LitBool true); l ↦ v2 }]].
Proof.
  iIntros (?? Φ) "Hl HΦ". iApply twp_lift_atomic_head_step_no_fork; first done.
  iIntros (σ1 ns κs nt) "[Hcred [Hσ Hκs]] !>". iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto with head_step.
  iIntros (κ v2' σ2 efs Hstep); inv_head_step.
  rewrite bool_decide_true //.
  iMod (gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iMod (cred_interp_incr with "[$]") as "($&_)".
  iModIntro. iSplit; first done. iSplit; first done. iFrame. by iApply "HΦ".
Qed.
Lemma wp_cmpxchg_suc s E l v1 v2 v' :
  v' = v1 → vals_compare_safe v' v1 →
  {{{ ▷ l ↦ v' }}} CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  {{{ RET PairV v' (LitV $ LitBool true); l ↦ v2 }}}.
Proof.
  iIntros (?? Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_cmpxchg_suc with "H"); [by auto..|]; iIntros "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_faa s E l i1 i2 :
  [[{ l ↦ LitV (LitInt i1) }]] FAA (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i2) @ s; E
  [[{ RET LitV (LitInt i1); l ↦ LitV (LitInt (i1 + i2)) }]].
Proof.
  iIntros (Φ) "Hl HΦ". iApply twp_lift_atomic_head_step_no_fork; first done.
  iIntros (σ1 ns κs nt) "[Hcred [Hσ Hκs]] !>". iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto with head_step.
  iIntros (κ e2 σ2 efs Hstep); inv_head_step.
  iMod (gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iMod (cred_interp_incr with "[$]") as "($&_)".
  iModIntro. do 2 (iSplit; first done). iFrame. by iApply "HΦ".
Qed.
Lemma wp_faa s E l i1 i2 :
  {{{ ▷ l ↦ LitV (LitInt i1) }}} FAA (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i2) @ s; E
  {{{ RET LitV (LitInt i1); l ↦ LitV (LitInt (i1 + i2)) }}}.
Proof.
  iIntros (Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_faa with "H"); [by auto..|]; iIntros "H HΦ". by iApply "HΦ".
Qed.

Lemma wp_new_proph s E :
  {{{ True }}}
    NewProph @ s; E
  {{{ pvs p, RET (LitV (LitProphecy p)); proph p pvs }}}.
Proof.
  iIntros (Φ) "_ HΦ". iApply wp_lift_atomic_head_step_no_fork; first done.
  iIntros (σ1 ns κ κs nt) "[Hcred [Hσ HR]] !>". iSplit; first by eauto with head_step.
  iIntros "!>" (v2 σ2 efs Hstep). inv_head_step.
  rename select proph_id into p.
  iMod (proph_map_new_proph p with "HR") as "[HR Hp]"; first done.
  iMod (cred_interp_incr with "[$]") as "($&_)".
  iModIntro; iSplit; first done. iFrame. by iApply "HΦ".
Qed.

(* In the following, strong atomicity is required due to the fact that [e] must
be able to make a head step for [Resolve e _ _] not to be (head) stuck. *)

Lemma resolve_reducible e σ (p : proph_id) v :
  Atomic StronglyAtomic e → reducible e σ →
  reducible (Resolve e (Val (LitV (LitProphecy p))) (Val v)) σ.
Proof.
  intros A (κ & e' & σ' & efs & H).
  exists (κ ++ [(p, (default v (to_val e'), v))]), e', σ', efs.
  eapply (Ectx_step []); try done.
  assert (∃w, Val w = e') as [w <-].
  { unfold Atomic in A. apply (A σ e' κ σ' efs) in H. unfold is_Some in H.
    destruct H as [w H]. exists w. simpl in H. by apply (of_to_val _ _ H). }
  simpl. constructor. by apply prim_step_to_val_is_head_step.
Qed.

Lemma step_resolve e vp vt σ1 κ e2 σ2 efs :
  Atomic StronglyAtomic e →
  prim_step (Resolve e (Val vp) (Val vt)) σ1 κ e2 σ2 efs →
  head_step (Resolve e (Val vp) (Val vt)) σ1 κ e2 σ2 efs.
Proof.
  intros A [Ks e1' e2' Hfill -> step]. simpl in *.
  induction Ks as [|K Ks _] using rev_ind.
  + simpl in *. subst. inv_head_step. by constructor.
  + rewrite fill_app /= in Hfill. destruct K; inversion Hfill; subst; clear Hfill.
    - rename select ectx_item into Ki.
      assert (fill_item Ki (fill Ks e1') = fill (Ks ++ [Ki]) e1') as Eq1;
        first by rewrite fill_app.
      assert (fill_item Ki (fill Ks e2') = fill (Ks ++ [Ki]) e2') as Eq2;
        first by rewrite fill_app.
      rewrite fill_app /=. rewrite Eq1 in A.
      assert (is_Some (to_val (fill (Ks ++ [Ki]) e2'))) as H.
      { apply (A σ1 _ κ σ2 efs). eapply (Ectx_step (Ks ++ [Ki])); done. }
      destruct H as [v H]. apply to_val_fill_some in H. by destruct H, Ks.
    - rename select (of_val vp = _) into Hvp.
      assert (to_val (fill Ks e1') = Some vp) as Hfillvp by rewrite -Hvp //.
      apply to_val_fill_some in Hfillvp as [-> ->]. inv_head_step.
    - rename select (of_val vt = _) into Hvt.
      assert (to_val (fill Ks e1') = Some vt) as Hfillvt by rewrite -Hvt //.
      apply to_val_fill_some in Hfillvt as [-> ->]. inv_head_step.
Qed.

Lemma wp_resolve s E e Φ (p : proph_id) v (pvs : list (val * val)) :
  Atomic StronglyAtomic e →
  to_val e = None →
  proph p pvs -∗
  WP e @ s; E {{ r, ∀ pvs', ⌜pvs = (r, v)::pvs'⌝ -∗ proph p pvs' -∗ Φ r }} -∗
  WP Resolve e (Val $ LitV $ LitProphecy p) (Val v) @ s; E {{ Φ }}.
Proof.
  (* TODO we should try to use a generic lifting lemma (and avoid [wp_unfold])
     here, since this breaks the WP abstraction. *)
  iIntros (A He) "Hp WPe". rewrite !wp_unfold /wp_pre /= He. simpl in *.
  iIntros (q σ1 ns κ κs nt) "[Hcred [Hσ Hκ]] HNC".
  destruct κ as [|[p' [w' v']] κ' _] using rev_ind.
  - iMod ("WPe" $! q σ1 ns [] κs nt with "[$Hcred $Hσ $Hκ] [$]") as "HWpe".
    iModIntro. iApply (step_fupdN_wand with "HWpe"). iNext.
    iIntros "[Hs WPe]".
    iSplit.
    { iDestruct "Hs" as "%". iPureIntro. destruct s; [ by apply resolve_reducible | done]. }
    iIntros (e2 σ2 efs step). exfalso. apply step_resolve in step; last done.
    inv_head_step. match goal with H: ?κs ++ [_] = [] |- _ => by destruct κs end.
  - rewrite -assoc.
    iMod ("WPe" $! q σ1 ns _ _ nt with "[$Hcred $Hσ $Hκ] [$]") as "HWpe".
    iModIntro. iApply (step_fupdN_wand with "HWpe"). iNext.
    iIntros "[Hs WPe]".
    iSplit.
    { iDestruct "Hs" as %?. iPureIntro. destruct s; [ by apply resolve_reducible | done]. }
    iIntros (e2 σ2 efs step). apply step_resolve in step; last done.
    inv_head_step; simplify_list_eq.
    iMod ("WPe" $! (Val w') σ2 efs with "[%]") as "WPe".
    { by eexists [] _ _. }
    iDestruct "WPe" as "[[$ [$ Hκ]] WPe]".
    iMod (proph_map_resolve_proph p' (w',v') κs with "[$Hκ $Hp]") as (vs' ->) "[$ HPost]".
    iModIntro. rewrite !wp_unfold /wp_pre /=. iDestruct "WPe" as "[HΦ $]".
    iIntros.
    iMod ("HΦ" with "[$]") as "(HΦ&$)". iModIntro. by iApply "HΦ".
Qed.

End lifting.
