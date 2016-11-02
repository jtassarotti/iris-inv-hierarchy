From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.heap_lang.lib.barrier Require Import proof.
From iris.heap_lang Require Import par.
From iris.heap_lang Require Import adequacy proofmode.

Definition worker (n : Z) : val :=
  λ: "b" "y", wait "b" ;; !"y" #n.
Definition client : expr :=
  let: "y" := ref #0 in
  let: "b" := newbarrier #() in
  ("y" <- (λ: "z", "z" + #42) ;; signal "b") ||
    (worker 12 "b" "y" || worker 17 "b" "y").
Global Opaque worker client.

Section client.
  Context `{!heapG Σ, !barrierG Σ, !spawnG Σ} (N : namespace).

  Definition y_inv (q : Qp) (l : loc) : iProp Σ :=
    (∃ f : val, l ↦{q} f ★ □ ∀ n : Z, WP f #n {{ v, v = #(n + 42) }})%I.

  Lemma y_inv_split q l : y_inv q l ⊢ (y_inv (q/2) l ★ y_inv (q/2) l).
  Proof.
    iDestruct 1 as (f) "[[Hl1 Hl2] #Hf]".
    iSplitL "Hl1"; iExists f; by iSplitL; try iAlways.
  Qed.

  Lemma worker_safe q (n : Z) (b y : loc) :
    heap_ctx ★ recv N b (y_inv q y) ⊢ WP worker n #b #y {{ _, True }}.
  Proof.
    iIntros "[#Hh Hrecv]". wp_lam. wp_let.
    wp_apply (wait_spec with "[- $Hrecv]"). iDestruct 1 as (f) "[Hy #Hf]".
    wp_seq. wp_load.
    iApply wp_wand_r. iSplitR; [iApply "Hf"|by iIntros (v) "_"].
  Qed.

  Lemma client_safe : heapN ⊥ N → heap_ctx ⊢ WP client {{ _, True }}.
  Proof.
    iIntros (?) "#Hh"; rewrite /client. wp_alloc y as "Hy". wp_let.
    wp_apply (newbarrier_spec N (y_inv 1 y) with "Hh"); first done.
    iIntros (l) "[Hr Hs]". wp_let.
    iApply (wp_par (λ _, True%I) (λ _, True%I) with "[-$Hh]"). iSplitL "Hy Hs".
    - (* The original thread, the sender. *)
      wp_store. iApply (signal_spec with "[-]"); last by iNext; auto.
      iSplitR "Hy"; first by eauto.
      iExists _; iSplitL; [done|]. iAlways; iIntros (n). wp_let. by wp_op.
    - (* The two spawned threads, the waiters. *)
      iSplitL; [|by iIntros (_ _) "_ !>"].
      iDestruct (recv_weaken with "[] Hr") as "Hr".
      { iIntros "Hy". by iApply (y_inv_split with "Hy"). }
      iMod (recv_split with "Hr") as "[H1 H2]"; first done.
      iApply (wp_par (λ _, True%I) (λ _, True%I) with "[- $Hh]").
      iSplitL "H1"; [|iSplitL "H2"; [|by iIntros (_ _) "_ !>"]];
        iApply worker_safe; by iSplit.
Qed.
End client.

Section ClosedProofs.

Let Σ : gFunctors := #[ heapΣ ; barrierΣ ; spawnΣ ].

Lemma client_adequate σ : adequate client σ (λ _, True).
Proof.
  apply (heap_adequacy Σ)=> ?.
  apply (client_safe (nroot .@ "barrier")); auto with ndisj.
Qed.

End ClosedProofs.

Print Assumptions client_adequate.
