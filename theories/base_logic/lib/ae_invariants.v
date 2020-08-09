From stdpp Require Export namespaces.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap.
From iris.base_logic.lib Require Export fancy_updates fupd_level.
From iris.base_logic.lib Require Import wsat.
Set Default Proof Using "Type".
Import uPred.

(** Always Enabled Semantic Invariants *)
Definition ae_inv_def `{!invG Σ} (k : nat) (P : iProp Σ) : iProp Σ :=
  □ ∀ Q E, (match k with
            | O => ▷ P ==∗ ◇ (▷ P ∗ Q)
            | S k' => ▷ P -∗ |k'={E}=> ▷ P ∗ Q
            end) -∗ |k={E}=> Q.
Definition ae_inv_aux : seal (@ae_inv_def). Proof. by eexists. Qed.
Definition ae_inv {Σ i} := ae_inv_aux.(unseal) Σ i.
Definition ae_inv_eq : @ae_inv = @ae_inv_def := ae_inv_aux.(seal_eq).
Instance: Params (@ae_inv) 3 := {}.
Typeclasses Opaque ae_inv.

Local Hint Extern 0 (AE _ ## MaybeEn _) => apply AE_MaybeEn_disj : core.
Local Hint Extern 0 (AlwaysEn ## MaybeEn _) => apply coPset_inl_inr_disj : core.

(** * Ae_Invariants *)
Section ae_inv.
  Context `{!invG Σ}.
  Implicit Types i : positive.
  Implicit Types E : coPset.
  Implicit Types P Q R : iProp Σ.

  (** ** Internal model of ae_invariants *)
  Definition own_ae_inv (k: nat) (P : iProp Σ) : iProp Σ :=
    ∃ i, ⌜i ∈ AE' (S k)⌝ ∧ ownI k i (bi_sch_var_fixed O) (list_to_vec [P]).

  Lemma own_ae_inv_acc_k E k P Q :
    own_ae_inv k P -∗
    (match k with
     | O => ▷ P ==∗ ◇ (▷ P ∗ Q)
     | S k' => ▷ P -∗ |k'={E}=> ▷ P ∗ Q
     end) -∗
    |k={E}=> Q.
  Proof.
    rewrite uPred_fupd_level_eq /uPred_fupd_level_def. iDestruct 1 as (i) "[Hi #HiP]".
    iDestruct "Hi" as % ?%elem_of_subseteq_singleton. iIntros "Hshift".
    rewrite ?(ownE_op (AE _)) // ?ownE_AE_split_current_rest.
    rewrite {1 2}(union_difference_L {[ i ]} (AE' (S k))) // ownE_op; last set_solver.
    iIntros "(Hw & ((Hi&HAE')&HAE) & HE)".
    iDestruct (ownI_open k i with "[$Hw $Hi $HiP]") as "(Hw & HI & HD)".
    iDestruct "HI" as (? Ps_mut) "(Hinterp&Hmut)".
    iEval (rewrite ?bi_schema_interp_unfold /=) in "Hinterp".
    destruct k.
    - iMod ("Hshift" with "[$]") as ">(HP&HQ)".
      iDestruct (ownI_close O i _ (list_to_vec [P]) with "[Hw Hmut HD HP]") as "H".
      { iFrame "# ∗". }
      iFrame. eauto.
    - iDestruct (wsat_le_acc (S k) with "Hw") as "(Hw&Hclo)"; first lia.
      rewrite ownE_op //.
      iMod ("Hshift" with "Hinterp [$Hw $HAE $HE]") as ">(Hw&(HAE&HE)&HP&HQ)".
      iDestruct ("Hclo" with "[$]") as "Hw".
      iDestruct (ownI_close (S k) i _ (list_to_vec [P]) with "[Hw Hmut HD HP]") as "H".
      { iFrame "# ∗". }
      iFrame. eauto.
  Qed.

  Lemma own_ae_inv_acc E k P Q:
    own_ae_inv k P -∗
    (match k with
     | O => ▷ P ==∗ ◇ (▷ P ∗ Q)
     | S k' => ▷ P -∗ |k'={E}=> ▷ P ∗ Q
     end) -∗
    |={E}=> Q.
  Proof.
    iIntros "Hown Hshift". iApply (fupd_level_fupd E _ _ k).
    iApply (own_ae_inv_acc_k E with "Hown Hshift").
  Qed.

  Lemma fresh_ae_inv_name (E : gset positive) k : ∃ i, i ∉ E ∧ i ∈ AE' k.
  Proof.
    exists (coPpick (AE' k ∖gset_to_coPset E)).
    rewrite -elem_of_gset_to_coPset (comm and) -elem_of_difference.
    apply coPpick_elem_of=> Hfin.
    eapply nclose_infinite, (difference_finite_inv _ _), Hfin.
    apply gset_to_coPset_finite.
  Qed.

  Lemma own_ae_inv_alloc_k E k P : ▷ P -∗ |k={E}=> own_ae_inv k P.
  Proof.
    rewrite uPred_fupd_level_eq. iIntros "HP [Hw $]".
    iMod (ownI_alloc (.∈ AE' (S k)) (bi_sch_var_fixed O) k (list_to_vec [P]) (list_to_vec [])
            with "[HP $Hw]") as (i ?) "[$ [? ?]]"; auto using fresh_ae_inv_name.
    { rewrite bi_schema_interp_unfold //=. }
    do 2 iModIntro. iExists i. auto.
  Qed.

  Lemma own_ae_inv_alloc k E P : ▷ P ={E}=∗ own_ae_inv k P.
  Proof. iIntros "HP". iApply (fupd_level_fupd). by iApply own_ae_inv_alloc_k. Qed.

  Lemma own_ae_inv_to_ae_inv k P: own_ae_inv k P -∗ ae_inv k P.
  Proof.
    iIntros "#I". rewrite ae_inv_eq. iIntros (E H).
    iPoseProof (own_ae_inv_acc_k with "I") as "H"; eauto.
  Qed.

  (** ** Public API of ae_invariants *)
  Global Instance ae_inv_contractive N : Contractive (ae_inv N).
  Proof. rewrite ae_inv_eq. solve_contractive. Qed.

  Global Instance ae_inv_ne N : NonExpansive (ae_inv N).
  Proof. apply contractive_ne, _. Qed.

  Global Instance ae_inv_proper N : Proper (equiv ==> equiv) (ae_inv N).
  Proof. apply ne_proper, _. Qed.

  Global Instance ae_inv_persistent N P : Persistent (ae_inv N P).
  Proof. rewrite ae_inv_eq. apply _. Qed.

  Lemma ae_inv_alter N P Q : ae_inv N P -∗ ▷ □ (P -∗ Q ∗ (Q -∗ P)) -∗ ae_inv N Q.
  Proof.
    rewrite ae_inv_eq. iIntros "#HI #HPQ !>" (Q' H). iIntros "Hshift".
    iMod ("HI" $! Q' H with "[Hshift]") as "$"; last done.
    { destruct N.
      - iIntros.
        iDestruct ("HPQ" with "[$]") as "[HQ HQP]".
        iMod ("Hshift" with "[$]") as ">(HQ&$)".
        iModIntro. iModIntro. iNext. by iApply ("HQP").
      - iIntros.
        iDestruct ("HPQ" with "[$]") as "[HQ HQP]".
        iMod ("Hshift" with "[$]") as "(HQ&$)".
        iModIntro. iNext. by iApply ("HQP").
    }
  Qed.

  Lemma ae_inv_iff N P Q : ae_inv N P -∗ ▷ □ (P ↔ Q) -∗ ae_inv N Q.
  Proof.
    iIntros "#HI #HPQ". iApply (ae_inv_alter with "HI").
    iIntros "!> !> HP". iSplitL "HP".
    - by iApply "HPQ".
    - iIntros "HQ". by iApply "HPQ".
  Qed.

  Lemma ae_inv_alloc' k E P : ▷ P -∗ |k={E}=> ae_inv k P.
  Proof.
    iIntros "HP". iApply own_ae_inv_to_ae_inv.
    iApply (own_ae_inv_alloc_k E k with "HP").
  Qed.

  Lemma ae_inv_alloc k E P : ▷ P ={E}=∗ ae_inv k P.
  Proof.
    iIntros "HP". iApply own_ae_inv_to_ae_inv.
    iApply (own_ae_inv_alloc k E with "HP").
  Qed.

  Lemma ae_inv_acc E k P Q :
    ae_inv k P -∗
    (match k with
     | O => ▷ P ==∗ ◇ (▷ P ∗ Q)
     | S k' => ▷ P -∗ |k'={E}=> ▷ P ∗ Q
     end) -∗
    |k={E}=> Q.
  Proof.
    rewrite ae_inv_eq /ae_inv_def. iIntros "#HI"; by iApply "HI".
  Qed.

  Lemma ae_inv_acc_bupd E k P Q :
    ae_inv k P -∗
    (▷ P ==∗ ◇ (▷ P ∗ Q)) -∗
    |k={E}=> Q.
  Proof.
    rewrite ae_inv_eq /ae_inv_def. iIntros "#HI Hshift".
    iApply "HI".
    { destruct k; eauto. iIntros. by iMod ("Hshift" with "[$]") as ">$". }
  Qed.

  Lemma ae_inv_accS E k P Q :
    ae_inv (S k) P -∗
    (▷ P -∗ |k={E}=> ▷ P ∗ Q) -∗
    |(S k)={E}=> Q.
  Proof. by iApply ae_inv_acc. Qed.

  (** ** Proof mode integration *)
  (*
  Global Instance into_ae_inv_ae_inv N P : IntoAe_Inv (ae_inv N P) N := {}.

  Global Instance into_acc_ae_inv_lvl k N P E:
    IntoAcc (X := unit) (ae_inv N P)
            (↑N ⊆ E) True (uPred_fupd_level E (E ∖ ↑N) k) (uPred_fupd_level (E ∖ ↑N) E k)
            (λ _ : (), (▷ P)%I) (λ _ : (), (▷ P)%I) (λ _ : (), None).
  Proof.
    rewrite ae_inv_eq /IntoAcc /accessor bi.exist_unit.
    iIntros (?) "#Hae_inv _". iApply (fupd_level_le _ _ O); first lia.
    iMod ("Hae_inv" $! _ with "[//]") as "($&Hcl)".
    iModIntro. iIntros "H". iSpecialize ("Hcl" with "H").
    iApply (fupd_level_le with "Hcl"); first lia.
  Qed.

  Global Instance into_acc_ae_inv N P E:
    IntoAcc (X := unit) (ae_inv N P)
            (↑N ⊆ E) True (fupd E (E ∖ ↑N)) (fupd (E ∖ ↑N) E)
            (λ _ : (), (▷ P)%I) (λ _ : (), (▷ P)%I) (λ _ : (), None).
  Proof.
    rewrite ae_inv_eq /IntoAcc /accessor bi.exist_unit.
    iIntros (?) "#Hae_inv _". iApply (fupd_level_fupd _ _ _ O).
    iMod ("Hae_inv" $! _ with "[//]") as "($&Hcl)".
    iModIntro. iIntros "H". iSpecialize ("Hcl" with "H").
    iApply (fupd_level_fupd with "Hcl").
  Qed.

  (** ** Derived properties *)
  Lemma ae_inv_acc_strong E N P :
    ↑N ⊆ E → ae_inv N P ={E,E∖↑N}=∗ ▷ P ∗ ∀ E', ▷ P ={E',↑N ∪ E'}=∗ True.
  Proof.
    iIntros (?) "Hae_inv".
    iPoseProof (ae_inv_acc (↑ N) N with "Hae_inv") as "H"; first done.
    rewrite difference_diag_L.
    iPoseProof (fupd_mask_frame_r _ _ (E ∖ ↑ N) with "H") as "H"; first set_solver.
    rewrite left_id_L -union_difference_L //. iMod "H" as "[$ H]"; iModIntro.
    iIntros (E') "HP".
    iPoseProof (fupd_mask_frame_r _ _ E' with "(H HP)") as "H"; first set_solver.
    by rewrite left_id_L.
  Qed.

  Lemma ae_inv_acc_timeless E N P `{!Timeless P} :
    ↑N ⊆ E → ae_inv N P ={E,E∖↑N}=∗ P ∗ (P ={E∖↑N,E}=∗ True).
  Proof.
    iIntros (?) "Hae_inv". iMod (ae_inv_acc with "Hae_inv") as "[>HP Hclose]"; auto.
    iIntros "!> {$HP} HP". iApply "Hclose"; auto.
  Qed.

  Lemma ae_inv_split_l N P Q : ae_inv N (P ∗ Q) -∗ ae_inv N P.
  Proof.
    iIntros "#HI". iApply ae_inv_alter; eauto.
    iIntros "!> !> [$ $] $".
  Qed.
  Lemma ae_inv_split_r N P Q : ae_inv N (P ∗ Q) -∗ ae_inv N Q.
  Proof.
    rewrite (comm _ P Q). eapply ae_inv_split_l.
  Qed.
  Lemma ae_inv_split N P Q : ae_inv N (P ∗ Q) -∗ ae_inv N P ∗ ae_inv N Q.
  Proof.
    iIntros "#H".
    iPoseProof (ae_inv_split_l with "H") as "$".
    iPoseProof (ae_inv_split_r with "H") as "$".
  Qed.
   *)

End ae_inv.
