From iris.algebra Require Export big_op.
From iris.bi Require Export big_op.
From iris.proofmode Require Export tactics.
From iris.proofmode Require Import reduction coq_tactics intro_patterns.
From iris.prelude Require Import options.

Section list.
  Context {PROP : bi}.
  Implicit Types (P Q : PROP).
  Implicit Types (A : Type).

  Lemma big_sepL_mono_with_inv' {A} P Φ Ψ (m: list A) n :
    (∀ k x, m !! k = Some x → P ∗ Φ (k + n) x ⊢ P ∗ Ψ (k + n) x) →
    P ∗ ([∗ list] k ↦ x ∈ m, Φ (k + n) x) ⊢ P ∗ [∗ list] k ↦ x ∈ m, Ψ (k + n) x.
  Proof.
    revert n.
    induction m as [|a m] => n Hwand //=.
    - iIntros "(HP&HΦ&Hl)".
      iDestruct (Hwand 0 a with "[HP HΦ]") as "(HP&HΨ)"; eauto.
      { rewrite Nat.add_0_l. iFrame. }
      rewrite ?Nat.add_0_l.
      iFrame "HΨ".
      setoid_rewrite <-Nat.add_succ_r.
      iApply (IHm with "[$ ]"); eauto.
      intros; eauto.
      specialize (Hwand (S k)).
      rewrite Nat.add_succ_r -Nat.add_succ_l. iApply Hwand; eauto.
  Qed.

  Lemma big_sepL_mono_with_fupd_inv' {A} `{!BiFUpd PROP} E P Φ Ψ (m: list A) n :
    (∀ k x, m !! k = Some x → P ∗ Φ (k + n) x ={E}=∗ P ∗ Ψ (k + n) x) →
    P ∗ ([∗ list] k ↦ x ∈ m, Φ (k + n) x) ={E}=∗ P ∗ [∗ list] k ↦ x ∈ m, Ψ (k + n) x.
  Proof.
    revert n.
    induction m as [|a m] => n Hwand //=.
    - by iIntros "($&_)". 
    - iIntros "(HP&HΦ&Hl)".
      iMod (Hwand 0 a with "[HP HΦ]") as "(HP&HΨ)"; eauto.
      { rewrite Nat.add_0_l. iFrame. }
      rewrite ?Nat.add_0_l.
      iFrame "HΨ".
      setoid_rewrite <-Nat.add_succ_r.
      iApply (IHm with "[$ ]"); eauto.
      intros; eauto.
      specialize (Hwand (S k)).
      rewrite Nat.add_succ_r -Nat.add_succ_l. iApply Hwand; eauto.
  Qed.

  Lemma big_sepL_mono_with_fupd_inv {A} `{!BiFUpd PROP} E P Φ Ψ (m: list A) :
    (∀ k x, m !! k = Some x → P ∗ Φ k x ={E}=∗ P ∗ Ψ k x) →
    P -∗ ([∗ list] k ↦ x ∈ m, Φ k x) ={E}=∗ P ∗ [∗ list] k ↦ x ∈ m, Ψ k x.
  Proof.
    iIntros (?) "HP H".
    iPoseProof (big_sepL_mono_with_fupd_inv' E P Φ Ψ _ O with "[HP H]") as "H";
    setoid_rewrite Nat.add_0_r; eauto; iFrame.
  Qed.

  Lemma big_sepL_mono_with_inv {A} P Φ Ψ (m: list A) :
    (∀ k x, m !! k = Some x → P ∗ Φ k x ⊢ P ∗ Ψ k x) →
    P -∗ ([∗ list] k ↦ x ∈ m, Φ k x) -∗ P ∗ [∗ list] k ↦ x ∈ m, Ψ k x.
  Proof.
    iIntros (?) "HP H".
    iPoseProof (big_sepL_mono_with_inv' P Φ Ψ _ O with "[HP H]") as "H";
    setoid_rewrite Nat.add_0_r; eauto; iFrame.
  Qed.
End list.

Section list2.
  Context {A B : Type}.
  Context {PROP : bi}.
  Implicit Types Φ Ψ : nat → A → B → PROP.

  Lemma big_sepL2_mono_with_fupd_inv E (P: PROP) `{!BiAffine PROP, !BiFUpd PROP} (Φ Ψ: nat → A → B → PROP) l1 l2:
    (∀ k x y, l1 !! k = Some x → l2 !! k = Some y → P ∗ Φ k x y ={E}=∗ P ∗ Ψ k x y) →
    P -∗ ([∗ list] k ↦ x;y ∈ l1;l2, Φ k x y) ={E}=∗ P ∗ [∗ list] k ↦ x;y ∈ l1;l2, Ψ k x y.
  Proof.
    iIntros (Himpl) "HP".
    rewrite ?big_sepL2_alt.
    iIntros "(%&Hwand)".
    iPoseProof (big_sepL_mono_with_fupd_inv E P (λ k ab, Φ k (fst ab) (snd ab))
                                      (λ k ab, Ψ k (fst ab) (snd ab)) with "HP Hwand") as "H".
    { intros k x Hlookup. eapply Himpl; eauto.
      - rewrite -(fst_zip l1 l2); last lia.
        rewrite list_lookup_fmap Hlookup //=.
      - rewrite -(snd_zip l1 l2); last lia.
        rewrite list_lookup_fmap Hlookup //=.
    }
    iMod "H" as "($&$)". eauto.
  Qed.

  Lemma big_sepL2_mono_with_inv (P: PROP) `{!BiAffine PROP} (Φ Ψ: nat → A → B → PROP) l1 l2:
    (∀ k x y, l1 !! k = Some x → l2 !! k = Some y → P ∗ Φ k x y ⊢ P ∗ Ψ k x y) →
    P -∗ ([∗ list] k ↦ x;y ∈ l1;l2, Φ k x y) -∗ P ∗ [∗ list] k ↦ x;y ∈ l1;l2, Ψ k x y.
  Proof.
    iIntros (Himpl) "HP".
    rewrite ?big_sepL2_alt.
    iIntros "(%&Hwand)".
    iPoseProof (big_sepL_mono_with_inv P (λ k ab, Φ k (fst ab) (snd ab))
                                      (λ k ab, Ψ k (fst ab) (snd ab)) with "HP Hwand") as "H".
    { intros k x Hlookup. eapply Himpl; eauto.
      - rewrite -(fst_zip l1 l2); last lia.
        rewrite list_lookup_fmap Hlookup //=.
      - rewrite -(snd_zip l1 l2); last lia.
        rewrite list_lookup_fmap Hlookup //=.
    }
    iDestruct "H" as "($&$)". eauto.
  Qed.
End list2.
