From stdpp Require Import fin_maps.
From iris_time.heap_lang Require Export notation proofmode.
From iris_time Require Import Reduction Translation.

(* This file contains lemmas and tactics that help reconstruct clean
   terms after the [wp_] tactics have pushed the translation too far
   down into the structure of terms. *)

Section Untranslate.

Context `{Tick}.

(* This lemma cannot be used in a rewriting database; that would
   lead to divergence. It can be manually applied in situations
   where the translation function has disappeared at a leaf #t
   and one must make it re-appear. *)

Lemma untranslate_litv t :
  #t = «#t»%V.
Proof. reflexivity. Qed.

(* This lemma is limited to an expression of the form «e» so as to
   guarantee that it is used only outside the translation brackets,
   never inside them. Indeed, translation brackets must never be
   nested. *)

Lemma untranslate_subst_litv x t e :
  subst x #t «e» = subst x «#t»%V «e».
Proof.
  reflexivity.
Qed.

(* The following lemmas hoist the translation up. *)

Lemma untranslate_pairv v1 v2 :
  («v1», «v2»)%V  = « (v1, v2) »%V.
Proof. reflexivity. Qed.

Lemma untranslate_pair e1 e2 :
  (tick «e1», «e2»)%E  = « (e1, e2) »%E.
Proof. reflexivity. Qed.

Lemma untranslate_injlv v :
  (InjLV «v»)%V = «InjLV v»%V.
Proof. reflexivity. Qed.

Lemma untranslate_injrv v :
  (InjRV «v»)%V = «InjRV v»%V.
Proof. reflexivity. Qed.

Lemma untranslate_injl e :
  (InjL (tick «e»))%E = «InjL e»%E.
Proof. reflexivity. Qed.

Lemma untranslate_injr e :
  (InjR (tick «e»))%E = «InjR e»%E.
Proof. reflexivity. Qed.

Lemma untranslate_lambda f x e :
  RecV f x (translation e) =
  translationV (RecV f x e).
Proof. reflexivity. Qed.

Lemma untranslate_app e1 e2 :
  (tick «e1» «e2»)%E = «e1 e2»%E.
Proof. reflexivity. Qed.

Lemma untranslate_val v :
  Val (translationV v) =
  translation (Val v).
Proof. reflexivity. Qed.

End Untranslate.

(* ------------------------------------------------------------------------------ *)

(* The tactic [untranslate] hoists the translation «...» up. *)

#[export] Hint Rewrite
  @untranslate_pairv
  @untranslate_pair
  @untranslate_injlv
  @untranslate_injrv
  @untranslate_injl
  @untranslate_injr
  @untranslate_lambda
  @untranslate_app
  @untranslate_val
: untranslate.

Ltac untranslate :=
  autorewrite with untranslate.

(* The tactic [push_subst] pushes substitutions down into the translation. *)

#[export] Hint Rewrite
  @untranslate_subst_litv
: push_subst.

#[export] Hint Rewrite
  <- @translation_subst
: push_subst.

Ltac push_subst :=
  repeat progress (autorewrite with push_subst; simpl subst).
