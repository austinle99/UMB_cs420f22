(*
        #####################################################
        ###  PLEASE DO NOT DISTRIBUTE SOLUTIONS PUBLICLY  ###
        #####################################################
*)

Set Default Goal Selector "!".

Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
From Turing Require Import Lang.
From Turing Require Import Util.
Import LangNotations.
Import ListNotations.
Import Lang.Examples.
Open Scope lang_scope.
Open Scope char_scope.

(* ---------------------------------------------------------------------------*)




(**

Show that any word that is in L4 is either empty or starts with "a".

 *)
Theorem ex1:
  forall w, L4 w -> w = [] \/ exists w', w = "a" :: w'.
Proof.
  simpl.
  intros A.
  intros B.
  induction B.
  unfold In, App in H.
  induction x.
  
Admitted.

(**

Show that the following word is accepted by the given language.

 *)
Theorem ex2:
  In ["a"; "b"; "b"; "a"] ("a" >> "b" * >> "a").
Proof.
  simpl.
  unfold Star, In, App.
  exists ["a";"b";"b"], ["a"].
  split.
  - simpl.
    reflexivity.
  - simpl.
    split.
    * simpl.
      exists ["a"], ["b";"b"].
      simpl.
      split.
      + simpl.
        reflexivity.
      + simpl.
        split.
        -- simpl.
           reflexivity.
        -- simpl.
           exists 2.
           apply pow_cons with (w1:= ["b"]) (w2:= ["b"]).
           ** simpl.
              apply pow_cons with (w1:= ["b"]) (w2:= []).
              ++ simpl.
                 apply pow_nil.
              ++ simpl.
                 reflexivity.
              ++ simpl.
                 reflexivity.
           ** simpl.
              reflexivity.
           ** simpl.
              reflexivity.
    * simpl.
      reflexivity.
Qed.

(**

Show that the following word is rejected by the given language.

 *)
Theorem ex3:
  ~ In ["b"; "b"] ("a" >> "b" * >> "a").
Proof.
  simpl.
  unfold In, App, Star, not.
  intros M.
  destruct M.
  destruct H.
  destruct H.
  destruct H0.
  destruct H0.
  destruct H0.
  destruct H0.
  destruct H2.
  destruct H3.
  unfold Char in H1, H2.
  subst.
  inversion H.
Qed.

(**

Show that the following language is empty.

 *)
Theorem ex4:
  "0" * >> {} == {}.
Proof.
  simpl.
  apply app_r_void_rw.
Qed.

(**

Rearrange the following terms. Hint use the distribution and absorption laws.

 *)
Theorem ex5:
  ("0" U Nil) >> ( "1" * ) == ( "0" >> "1" * ) U ( "1" * ).
Proof.
  simpl.
  unfold Equiv.
  intros M.
  split.
  - simpl.
    intros A.
    rewrite <- app_union_distr_l in A.
    rewrite app_l_nil_rw in A.
    apply A.
  - simpl.
    intros A.
    rewrite <- app_union_distr_l.
    rewrite app_l_nil_rw.
    apply A.
Qed.

(**

Show that the following langue only accepts two words.

 *)
Theorem ex6:
  ("0" >> "1" U "1" >> "0") == fun w => (w = ["0"; "1"] \/ w = ["1"; "0"]).
Proof.
  simpl.
  unfold Equiv.
  split.
  - simpl.
    unfold App, Union, In.
    intros A.
    destruct A.
    
Admitted.

Check union_sym_rw.
Check star_union_nil_rw.

Theorem ex7:
  "b" >> ("a" U "b" U Nil) * >> Nil == "b" >> ("b" U "a") *.
Proof.
  simpl.
  split.
  - simpl.
    intros A.
    rewrite app_r_nil_rw in A.
    rewrite union_sym_rw in A.
    rewrite star_union_nil_rw in A.
    rewrite union_sym_rw in A.
    apply A.
  - simpl.
    intros A.
    rewrite app_r_nil_rw.
    rewrite union_sym_rw.
    rewrite star_union_nil_rw.
    rewrite union_sym_rw.
    apply A.
Qed.

Check union_r_void_rw.
Check star_void_rw.

Theorem ex8:
  (("b" >> ("a" U {}) ) U (Nil >> {} >> "c")* ) * == ("b" >> "a") *.
Proof.
  simpl.
  split.
  - simpl.
    intros A.
    rewrite union_r_void_rw in A.
    rewrite app_r_void_rw in A.
    rewrite app_l_void_rw in A.
    rewrite star_void_rw in A.
    rewrite union_sym_rw in A.
    rewrite star_union_nil_rw in A.
    apply A.
  - simpl.
    intros A.
    rewrite union_r_void_rw.
    rewrite app_r_void_rw.
    rewrite app_l_void_rw.
    rewrite star_void_rw.
    rewrite union_sym_rw.
    rewrite star_union_nil_rw.
    apply A.
Qed.



