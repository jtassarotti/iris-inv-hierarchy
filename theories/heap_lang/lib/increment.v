From iris.heap_lang Require Export lifting notation.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation atomic_heap par.
Set Default Proof Using "Type".

(** Show that implementing fetch-and-add on top of CAS preserves logical
atomicity. *)

(* TODO: Move this to iris-examples once gen_proofmode is merged. *)
Section increment.
  Context `{!heapG Σ} (aheap: atomic_heap Σ).

  Definition incr: val :=
    rec: "incr" "l" :=
       let: "oldv" := aheap.(load) "l" in
       if: aheap.(cas) ("l", "oldv", ("oldv" + #1))
         then "oldv" (* return old value if success *)
         else "incr" "l".

  Lemma incr_spec (l: loc) :
        atomic_wp (incr #l)
                  ⊤ ⊤
                  (λ (v: Z), aheap.(mapsto) l 1 #v)%I
                  (λ v (_:()), aheap.(mapsto) l 1 #(v + 1))%I
                  (λ v _, #v).
  Proof.
    iIntros (Q Φ) "HQ AU". iLöb as "IH". wp_let.
    wp_apply (load_spec with "[HQ]"); first by iAccu.
    (* Prove the atomic shift for load *)
    iAuIntro. iApply (aacc_aupd_abort with "AU"); first done.
    iIntros (x) "H↦".
    iApply (aacc_intro (_, _) with "[H↦]"); [solve_ndisj|done|iSplit].
    { iIntros "$ !> $ !> //". }
    iIntros ([]) "$ !> AU !> HQ".
    (* Now go on *)
    wp_let. wp_op. wp_bind (aheap.(cas) _)%I.
    wp_apply (cas_spec with "[HQ]"); first by iAccu.
    (* Prove the atomic shift for CAS *)
    iAuIntro. iApply (aacc_aupd with "AU"); first done.
    iIntros (x') "H↦".
    iApply (aacc_intro with "[H↦]"); [solve_ndisj|done|iSplit].
    { iIntros "$ !> $ !> //". }
    iIntros ([]) "H↦ !>".
    destruct (decide (#x' = #x)) as [[= ->]|Hx].
    - iRight. iExists (). iFrame. iIntros "HΦ !> HQ".
      wp_if. by iApply "HΦ".
    - iLeft. iFrame. iIntros "AU !> HQ".
      wp_if. iApply ("IH" with "HQ"). done.
  Qed.

End increment.

Section increment_client.
  Context `{!heapG Σ, !spawnG Σ}.

  Definition incr_client : val :=
    λ: "x",
       let: "l" := ref "x" in
       incr primitive_atomic_heap "l" ||| incr primitive_atomic_heap "l".

  Lemma incr_client_safe (x: Z):
    WP incr_client #x {{ _, True }}%I.
  Proof using Type*.
    wp_let. wp_alloc l as "Hl". wp_let.
    iMod (inv_alloc nroot _ (∃x':Z, l ↦ #x')%I with "[Hl]") as "#Hinv"; first eauto.
    (* FIXME: I am only using persistent stuff, so I should be allowed
       to move this to the persisten context even without the additional □. *)
    iAssert (□ WP incr primitive_atomic_heap #l {{ _, True }})%I as "#Aupd".
    { iAlways. wp_apply (incr_spec with "[]"); first by iAccu. clear x.
      iAuIntro. iInv nroot as (x) ">H↦".
      iApply (aacc_intro with "[H↦]"); [solve_ndisj|done|iSplit].
      { by eauto 10. }
      iIntros ([]) "H↦ !>". iSplitL "H↦"; first by eauto 10.
      (* The continuation: From after the atomic triple to the postcondition of the WP *)
      done.
    }
    wp_apply wp_par.
    - iAssumption.
    - iAssumption.
    - iIntros (??) "_ !>". done.
  Qed.

End increment_client.
