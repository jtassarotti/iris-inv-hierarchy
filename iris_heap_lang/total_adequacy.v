From iris.algebra Require Import lib.frac_auth numbers auth.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Export total_adequacy.
From iris.heap_lang Require Export adequacy.
From iris.heap_lang Require Import proofmode notation.
From iris.prelude Require Import options.

Definition heap_total Σ `{!heapPreG Σ} s e σ φ :
  (∀ `{!heapG Σ}, ⊢ inv_heap_inv -∗ WP e @ s; ⊤ [{ v, ⌜φ v⌝ }]) →
  sn erased_step ([e], σ).
Proof.
  intros Hwp; eapply (twp_total' _ _); iIntros (?) "".
  iMod (gen_heap_init σ.(heap)) as (?) "[Hh _]".
  iMod (inv_heap_init loc (option val)) as (?) ">Hi".
  iMod (proph_map_init [] σ.(used_proph_id)) as (?) "Hp".
  iMod (own_alloc (●F O ⋅ ◯F 0)) as (γ) "[Hγ Hγ']";
    first by apply auth_both_valid_discrete.
  iModIntro.
  set (hG := (HeapG _ _ _ _ _ _ γ)).
  iExists
    (λ σ ns κs _, (cred_interp ns ∗ gen_heap_interp σ.(heap) ∗ proph_map_interp κs σ.(used_proph_id))%I),
    (λ _, True%I), _; iFrame.
  iFrame.
  iSplitL "Hγ'".
  { iExists 1%Qp. iFrame. }
  iApply (Hwp (HeapG _ _ _ _ _ _ _)). done.
Qed.
