Require Import List.
Import ListNotations.
Set Implicit Arguments.

Section map.
Variable X : Type.
Hypothesis Xeq_dec : forall x x':X, {x = x'} + {x <> x'}.

(* Total and partial maps *)
Definition total_map (Y : Type) := X -> Y.

Definition t_empty {Y} (v : Y) : total_map Y :=
  (fun _ => v).

Definition t_update {Y : Type} (m : total_map Y) (x : X) (v : Y) :=
fun x' => match Xeq_dec x x' with
  | left _ => v
  | right _ => m x'
  end.

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).

Definition partial_map (Y : Type) := total_map (option Y).

Definition add_mapping {Y : Type} (m : partial_map Y)
           (x : X) (v : Y) :=
  (x !-> Some v ; m).

Fixpoint add_mappings {Y : Type} (m : partial_map Y) (xs : list X) (ys : list Y) :=
  match xs, ys with
  | x :: xs', y :: ys' => add_mapping (add_mappings m xs' ys') x y
  | _, _ => m
  end.

Definition empty {Y : Type} : partial_map Y :=
  t_empty None.

End map.
