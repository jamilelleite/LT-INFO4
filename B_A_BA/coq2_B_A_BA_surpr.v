(** * INITIATION A COQ, suite *)

(** Complément à cours02_B_A_BA.v, contenant juste le nécessaire
   pour définir coul_suiv ;
   Définition de la même fonction, en mode preuve interactive
   pour illustrer le développement pas à pas d'une fonction
   au moyen de tactiques.
*)

Inductive coulfeu : Set :=
  | Vert : coulfeu
  | Orange : coulfeu
  | Rouge : coulfeu
.

(** Définition d'origine *)
Definition coul_suiv : coulfeu -> coulfeu :=
  fun c =>
    match c with
    | Vert => Orange
    | Orange => Rouge
    | Rouge => Vert
    end.

(** Définition en mode interactif *)
Definition coul_suiv2 : coulfeu -> coulfeu.
Proof.
  intro c.
  destruct c as [ (*Vert*) | (*Orange*) | (*Rouge*) ].
  Show Proof.
  - exact Orange.
  - exact Rouge.
  - exact Vert.
Defined.

Print coul_suiv2.

(** Définition en utilisant la tactique refine *)
Definition coul_suiv3 : coulfeu -> coulfeu.
Proof.
  intro c. Undo 1.
  refine (fun c => _).
  (** refine (code d'un pgm incomplet)  _ -> joker**)
  destruct c as [ (*Vert*) | (*Orange*) | (*Rouge*) ]. Undo 1.
  refine (match c with
          | Vert => _
          | Orange => _
          | Rouge => _
          end).
  Show Proof. Undo 2.
  refine (fun c =>
            match c with
            | Vert => _
            | Orange => _
            | Rouge => _
            end).
  Undo 1.
  refine (fun c =>
            match c with
            | Vert => _
            | Orange => Rouge
            | Rouge => _
            end).
  Show Proof.
  - refine Orange.
  - refine Vert.
Defined.
Print coul_suiv3.
(** Et pour les théorèmes ? *)

(**
- Une preuve de P -> Q est une fonction qui fabrique une preuve de Q
  à partir de n'importe quelle preuve de P
- une preuve de ∀x, P x est une fonction qui fabrique une preuve de P x
  à partir de n'importe quel x
*)

Lemma coul_suiv_V_O :
  forall c,
    c = Vert \/ c = Orange -> coul_suiv c = Rouge \/ coul_suiv c = Orange.
Proof.
  intros c deux_cas.
  destruct deux_cas as [cv | co].
  - rewrite cv. cbn [coul_suiv]. right. reflexivity.
  - rewrite co. left. cbn [coul_suiv]. reflexivity.
Show Proof. (* un peu saoûlant, mais on voit l'architecture du programme *)
Qed.
