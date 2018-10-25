From iris.heap_lang Require Import proofmode notation.

Open Scope Z_scope.

Definition w : nat := 64.
Definition max_int : Z := 1 ≪ (w-1).
Definition min_int : Z := - max_int.
Definition max_uint : Z := 2 * max_int.

(*
 * Bare machine integers can overflow.
 *)

Section machine_int.

  Context `{heapG Σ}.

  Definition is_machine_int (n : Z) : iProp Σ :=
    ⌜min_int ≤ n < max_int⌝%I.

  Definition machine_int_add : val :=
    λ: "x" "y",
      ("x" + "y" + #max_int) `rem` #max_uint - #max_int.

  (* Machine addition does not overflow when some inequality is met: *)
  Lemma machine_int_add_spec n1 n2 :
    {{{ is_machine_int n1 ∗ is_machine_int n2 ∗ ⌜min_int ≤ n1+n2 < max_int⌝ }}}
    machine_int_add #n1 #n2
    {{{ RET #(n1+n2) ; is_machine_int (n1+n2) }}}.
  Proof.
    iIntros (Φ) "(_ & _ & %) Post". repeat (wp_pure _).
    (* boring arithmetic proof: *)
    assert ((n1 + n2 + max_int) `rem` max_uint - max_int = n1 + n2) as ->. {
      assert ((n1 + n2 + max_int) `rem` max_uint = n1 + n2 + max_int). {
        apply Z.rem_small. unfold min_int, max_uint in *. lia.
      }
      lia.
    }
    by iApply "Post".
  Qed.

End machine_int.
