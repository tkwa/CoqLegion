Require Import List.
Require Import ListSet.
Import ListNotations.
Require Import Nat.
Require Import Bool.
From Legion Require Import Map.

Parameter region : Type.
Parameter location : Type.
Definition physical_region : Type := set location.
Parameter Id_T : Type.

Definition Task_ID := nat.

(* Declarations for ListSet and Map *)


Axiom Id_T_dec :
  forall x y : Id_T, {x = y} + {x <> y}.

Axiom loc_dec :
  forall x y : location, {x = y} + {x <> y}.

Axiom option_loc_dec:
 forall x y : option location, {x = y} + {x <> y}.

Axiom region_eq_neq :
  forall x y : region, {x = y} + {x <> y}.

Definition set_inter_reg := set_inter region_eq_neq.

Axiom physical_region_eq_neq :
  forall r1 r2 : physical_region, {r1 = r2} + {r1 <> r2}.

(* Core Legion Types (page 4) *)
Inductive coherence_mode : Type :=
  | Atomic (r : region) | Simult (r : region)
.

Definition Qs : Type := set coherence_mode.

Inductive priv_T : Type :=
  | Reads (r : region)
  | Writes (r : region)
  | Reduces (id : Id_T) (r : region)
.

Definition Phis := set priv_T.

Inductive constraint : Type :=
| Subregion (r1:region) (r2 : region)
| Disjoint (r1 : region) (r2 : region)
.

Axiom constraint_dec :
  forall x y : constraint, {x = y} + {x <> y}.

Definition Omegas : Type := set constraint.

Inductive T : Type :=
  | TBool | TInt
  | TTuple (tup : list T)
  | TPointer (t : T) (rs : list region)
  | TColoring (r : region)
  | (* ∃rs.t *) TRegionRelation (rs : list region) (t:T) (Ω : Omegas)
    (* TODO change to universal quantification over regions *)
  | (* ∀ *) TTask (rs : list region) (ts : list T) (Φ : list Phis) (Q : list Qs) (tr : T)
.

Inductive expr : Type :=
  | EBool (b : bool)
  | EInt (i : nat)
  | Tuple (es : list expr)
  | ExprIndex (e : expr) (n : nat)
  | Id (id : Id_T)
  | NewPointer (t : T) (r : region)
  | NullPointer (t : T) (r : region)
  | IsNull (e : expr)
  | Upregion (e : expr) (rs : list region)
  | Downregion (e : expr) (rs : list region)
  | Read (e1 : expr)
  | Write (e1 : expr) (e2 : expr)
  | Reduce (id : Id_T) (e1 : expr) (e2 : expr)
  | NewColor (r : region)
  | Color (e1 : expr) (e2 : expr) (e3 : expr)
  | Add (e1 : expr) (e2 : expr)
  | Compare (e1 : expr) (e2 : expr)
  | LetIn (id : Id_T) (t : T) (e1 : expr) (e2 : expr)
  | If (e1 : expr) (e2 : expr) (e3 : expr)
  | Call (id : Id_T) (rs : list region) (es : list expr)
  | Partition (rp : region) (e1 : expr) (rs : list region) (e2 : expr)
  | Pack (e1 : expr) (t : T) (rs : list region)
  | Unpack (e1 : expr) (id : Id_T) (t : T) (rs : list region) (e2 : expr)
.


Inductive value : Type :=
  | VBool (b : bool)
  | VInt (i : nat)
  (* Value tuples in the paper have two entries; changed for consistency with expressions. *)
  | VTuple (vs : list value)
  | VNull
  | VLocation (l : location)
  | VColoring (l : list (location * nat))
  | VRegionRelationInstance (rs : list physical_region) (v : value)
.

Axiom value_dec :
  forall x y : value, {x = y} + {x <> y}.

(* Heap, takes heap location to type *)
Definition Hs := partial_map location T.

(* Store takes global variables to values *)
Definition Ss := partial_map location value.

Inductive CoherenceMode :=
  | SSimult | SAtomic | SExcl
.

(* entry in an execution history *)
Inductive entry : Type :=
  | SRead (l : location) (c : CoherenceMode) (v : value) (a : Task_ID)
  | SWrite (l : location) (c : CoherenceMode) (v : value) (a : Task_ID)
  | SReduce (id : Id_T) (l : location) (c : CoherenceMode) (v : value) (a : Task_ID)
.


Definition get_loc (eps : entry) :=
  match eps with
  | SRead l _ _ _ | SWrite l _ _ _ | SReduce _ l _ _ _ => l
  end.

Definition get_mode (eps : entry) :=
  match eps with
  | SRead _ m _ _ | SWrite _ m _ _ | SReduce _ _ m _ _ => m
  end.

Definition get_val (eps : entry) :=
  match eps with
  | SRead _ _ v _ | SWrite _ _ v _ | SReduce _ _ _ v _ => v
  end.

Definition get_tag (eps : entry) :=
  match eps with
  | SRead _ _ _ t | SWrite _ _ _ t | SReduce _ _ _ _ t => t
  end.

(* E is stored backwards in some rules. TODO: Change throughout to store forwards *)
Definition Es := list entry.

(* a type map *)
Definition Gammas : Type := partial_map Id_T T.

(* map *)
Definition Ms : Type := partial_map region physical_region.

(* map *)
Definition Ls : Type := partial_map Id_T value.

Definition ClobberSet : Type := set location.

(* Helper Functions (Figure 5, page 9)
 ******************
*)

(* Figure 5, page 9 *)
Fixpoint apply_rev (S : Ss) (E : Es) : Ss :=
match E with
  | nil => S
  | SRead l c v t :: E' => apply_rev S E'
  | SWrite l c v t :: E' => add_mapping loc_dec (apply_rev S E') l v
  | SReduce id l _ v _ :: E' =>
      let S' := apply_rev S E' in
      (match S' l with
      | Some sl => add_mapping loc_dec S' l (Call id [] [sl; v])
      | None => S' (* error *)
      end)
  end.
Definition apply (S : Ss) (E : Es) : Ss :=
  apply_rev S (rev E).

(* Valid Interleaving Test, fig 7, page 14 *)

Inductive any_interleave : Es -> list Es -> Prop :=
  | any_interleave_empty l :
      (forall (empty : Es), empty = []) ->
      any_interleave [] l
  | any_interleave_nonempty ep E' Elist Elist':
      is_append_one Elist ep Elist' ->
      any_interleave (ep::E') Elist'
with
  is_append_one : list Es -> entry -> list Es -> Prop :=
  | is_append_one_hd ep Elist Elist' :
    tl Elist = Elist' ->
    is_append_one Elist ep ((ep :: hd [] Elist) :: tl Elist)
  | is_append_one_tl ep Elist Elist' E1:
    is_append_one Elist ep Elist' ->
    is_append_one (E1::Elist) ep (E1::Elist')
.


Inductive coherent : Ss -> set location -> set location -> Es -> Prop :=
  | coherent_empty S L1 L2 :
      coherent S L1 L2 []
  | coherent_read S L1 L2 E ep l c v t :
      (~ (In l L2) \/ S l = Some v) ->
      coherent S L1 L2 E ->
      ep = SRead l c v t ->
      coherent S L1 L2 (ep::E)
  | coherent_write S L1 L2 E ep l c v t :
      coherent (apply S [ep]) L1 (l :: L2) E ->
      ep = SWrite l c v t ->
      In l L1 ->
      coherent S L1 L2 (ep::E)
  | coherent_other S L1 L2 E ep l c v t :
      coherent (apply S [ep]) L1 L2 E ->
      (ep = SWrite l c v t /\ ~ (In l L1)) \/ (exists id, ep = SReduce id l c v t) ->
      coherent S L1 L2 (ep::E)
.

(* Takes a single ex. trace, not a list of execution traces *)
Definition seq_equiv (S:Ss) (L1 : set location) (L2 : set location) (E' : Es) (Eseq : Es)
  : Prop :=
  coherent S L1 L2 Eseq /\
  (forall (l : location), In l L1 -> (apply S E') l = (apply S Eseq) l).


Fixpoint Lexcl_helper (E:Es) (C:ClobberSet) : set location :=
  match E with
  | [] => []
  | h :: E' => let L' := Lexcl_helper E' C in (
    match get_mode h with
    | SExcl => get_loc h :: L'
    | _ => L' end)
  end.

Axiom location_eq_neq:
  forall x y : location, {x = y} + {x <> y}.

Definition Lexcl (E:Es) (C:ClobberSet) : set location :=
  set_diff location_eq_neq (Lexcl_helper E C) C.

Fixpoint Latomic_helper (E:Es) (C:ClobberSet) : set location :=
  match E with
  | [] => []
  | h :: E' => let L' := Latomic_helper E' C in (
    match get_mode h with
    | SAtomic => get_loc h :: L'
    | _ => L' end)
  end.

Definition Latomic (E:Es) (C:ClobberSet) : set location :=
  set_diff location_eq_neq
    (Latomic_helper E C)
    (set_union location_eq_neq C (Lexcl E C)).

(* filters by tag *)
Fixpoint darrow (t : Task_ID) (E : Es) : Es :=
  match E with
  | [] => []
  | h :: E' => if Nat.eqb t (get_tag h) then h::darrow t E'
                  else darrow t E'
  end.

Definition valid_interleave (S : Ss) (C : ClobberSet)
  (E' : Es) (Elist : list Es) : Prop :=
  any_interleave E' Elist /\
  coherent S (Lexcl E' C) (Lexcl E' C) E' /\
  seq_equiv S (Lexcl E' C) (Lexcl E' C) E' (fold_right (@app entry) nil Elist) /\
  forall t, seq_equiv S (Latomic E' C) (empty_set location) (darrow t E')
    (darrow t (fold_right (@app entry) nil Elist))
.

(* ======== *)


(* need to reference M *)
Fixpoint coherence_marking_helper
  (M : Ms) (l : location) (Q : Qs) (has_atomic : bool) : CoherenceMode :=
  match Q with
  | [] => if has_atomic then SAtomic else SExcl
  | Simult r :: Q' =>
    (match M r with
    | Some rho => if set_mem loc_dec l rho then SSimult
                  else coherence_marking_helper M l Q' has_atomic
    | None => coherence_marking_helper M l Q' has_atomic
    end
    )
  | Atomic r :: Q' =>
    (match M r with
    | Some rho => coherence_marking_helper M l Q' (orb has_atomic (set_mem loc_dec l rho))
    | None => coherence_marking_helper M l Q' has_atomic
    end
    )
  end.

Definition coherence_marking (M : Ms) (l : location) (Q : Qs) : CoherenceMode :=
  coherence_marking_helper M l Q false.

(* mark coherence (page 9) *)
Fixpoint mark_coherence (M : Ms) (E : Es) (Q : Qs) (taskid : nat) : Es :=
  let cm l := coherence_marking M l Q in
  match E with
  | [] => []
  | SRead l c v t :: E' => SRead l (cm l) v t :: mark_coherence M E' Q taskid
  | SWrite l c v t :: E' => SWrite l (cm l) v t :: mark_coherence M E' Q taskid
  | SReduce id l c v t :: E' => SReduce id l (cm l) v t :: mark_coherence M E' Q taskid
  end.

(* needed for [nth] *)
Definition default_E : Es := [].
Definition default_expr := EBool false.
Definition default_val := VBool false.
Parameter default_loc : location.
Parameter default_S : Ss.

(* Type rules
   *************************
 *)

(* Privilege and Constraint Closure (Fig. 3, page 7) *)

(* Note: Although privilege and constraint sets are implemented as sets,
    we implement privilege and constraint closure as relations,
    because constructing an explicit set is intractable.
*)

Inductive constraint_closure : Omegas -> constraint -> Prop :=
  | Cc_in Ω c : In c Ω -> constraint_closure Ω c
  | Cc_sub_refl_l Ω ri rj:
      constraint_closure Ω (Subregion ri rj) ->
      constraint_closure Ω (Subregion ri ri)
  | Cc_sub_refl_r Ω ri rj:
      constraint_closure Ω (Subregion ri rj) ->
      constraint_closure Ω (Subregion rj rj)
  | Cc_sub_trans Ω ri rj rk :
      constraint_closure Ω (Subregion ri rj) ->
      constraint_closure Ω (Subregion rj rk) ->
      constraint_closure Ω (Subregion ri rk)
  | Cc_sub_disj Ω ri rj rk :
      constraint_closure Ω (Subregion ri rj) ->
      constraint_closure Ω (Disjoint rj rk) ->
      constraint_closure Ω (Disjoint ri rk)
  | Cc_disj_symm Ω ri rj :
      constraint_closure Ω (Disjoint ri rj) ->
      constraint_closure Ω (Disjoint rj ri)
.

Inductive privilege_closure : Omegas -> Phis -> priv_T -> Prop :=
  | Pc_in Ω Φ P : In P Φ -> privilege_closure Ω Φ P
  | Pc_sub_reads Ω Φ ri rj :
      constraint_closure Ω (Subregion ri rj) ->
      privilege_closure Ω Φ (Reads rj) ->
      privilege_closure Ω Φ (Reads ri)
  | Pc_sub_writes Ω Φ ri rj :
      constraint_closure Ω (Subregion ri rj) ->
      privilege_closure Ω Φ (Writes rj) ->
      privilege_closure Ω Φ (Writes ri)
  | Pc_sub_reduces Ω Φ id ri rj :
      constraint_closure Ω (Subregion ri rj) ->
      privilege_closure Ω Φ (Reduces id rj) ->
      privilege_closure Ω Φ (Reduces id ri)
  | Pc_rw_reduces Ω Φ r id :
      privilege_closure Ω Φ (Reads r) ->
      privilege_closure Ω Φ (Writes r) ->
      privilege_closure Ω Φ (Reduces id r)
.

(* Substitutes regions in types parametrized over regions *)
Definition subst_regions (t : T) (rs' : list region) :=
  match t with
  | TBool | TInt | TTuple _ | TColoring _ => t
  | TPointer t rs => TPointer t rs'
  | TRegionRelation rs t Ω => TRegionRelation rs' t Ω
  | TTask rs ts Φ Q tr => TTask rs' ts Φ Q tr
  end.


(* ⊢ *)
Inductive typed : Gammas -> Phis -> Omegas -> expr -> T -> Prop :=
  (* Figure 4, page 8 *)
  | T_Read Γ Φ Ω e1 t rs :
      typed Γ Φ Ω e1 (TPointer t rs) ->
      (forall (r:region), In r rs -> privilege_closure Ω Φ (Reads r)) ->
      typed Γ Φ Ω (Read e1) t
  | T_Write Γ Φ Ω e1 e2 t rs :
      typed Γ Φ Ω e1 (TPointer t rs) ->
      typed Γ Φ Ω e2 t ->
      (forall (r : region), In r rs -> privilege_closure Ω Φ (Writes r)) ->
      typed Γ Φ Ω (Write e1 e2) (TPointer t rs)
  | T_Reduce Γ Φ Ω id e1 e2 t1 t2 rs :
      Γ id = Some (TTask rs [t1; t2] [] [] t1) ->
      typed Γ Φ Ω e1 (TPointer t1 rs) ->
      typed Γ Φ Ω e2 t2 ->
      (forall (r : region), In r rs -> privilege_closure Ω Φ (Reduces id r)) ->
      typed Γ Φ Ω (Reduce id e1 e2) (TPointer t1 rs)
  | T_New Γ Φ Ω t r :
      typed Γ Φ Ω (NewPointer t r) (TPointer t [r])
  | T_UpRgn Γ Φ Ω e t rs rs' :
      typed Γ Φ Ω e (TPointer t rs') ->
      (forall ri : region, forall rj' : region,
        In ri rs -> In rj' rs' -> constraint_closure Ω (Subregion ri rj')) ->
      typed Γ Φ Ω (Upregion e rs) (TPointer t rs)
  | T_DnRgn Γ Φ Ω e t rs rs' :
      typed Γ Φ Ω e (TPointer t rs') ->
      typed Γ Φ Ω (Downregion e rs) (TPointer t rs)
  | T_NewColor Γ Φ Ω r :
      typed Γ Φ Ω (NewColor r) (TColoring r)
  | T_Color Γ Φ Ω e1 e2 e3 t r :
      typed Γ Φ Ω e1 (TColoring r) ->
      typed Γ Φ Ω e2 (TPointer t [r]) ->
      typed Γ Φ Ω e3 TInt ->
      typed Γ Φ Ω (Color e1 e2 e3) (TColoring r)
  | T_Partition Γ Φ Ω Ω' e1 e2 rp rs t :
      typed Γ Φ Ω e1 (TColoring rp) ->
      Ω' = (let cd := constraint_dec in set_union cd
            (set_union cd Ω (set_map cd (fun r => Subregion r rp) rs))
            (set_diff cd
              (set_map cd (fun rr => Disjoint (fst rr) (snd rr)) (set_prod rs rs))
              (set_map cd (fun rr => Disjoint rr rr) rs))) ->
      typed Γ Φ Ω' e2 t ->
      (* (forall r, (exists id, Γ id = r) -> ~ (In rs r)) -> *)
      (* set_inter rs regions_of(Γ,t) *)
      typed Γ Φ Ω' (Partition rp e1 rs e2) t
  | T_Pack Γ Φ Ω Ω1 e1 rs rs' t1 t2 :
      t1 = (TRegionRelation rs' t2 Ω1) ->
      (* Ω1[rs' / rs] ⊆ Ω* -> *)
      typed Γ Φ Ω e1 (subst_regions t2 rs') ->
      typed Γ Φ Ω (Pack e1 t1 rs) (subst_regions t2 rs')
  | T_Unpack Γ Γ' Φ Ω Ω' Ω1 e1 e2 id rs rs' t1 t2 t3 :
      t1 = (TRegionRelation rs' t2 Ω1) ->
      typed Γ Φ Ω e1 t1 ->
      Γ' = add_mapping Id_T_dec Γ id (subst_regions t2 rs) ->
      Ω' = Ω (* ∪ (add_mappings Ω1 rs) *) ->
      typed Γ' Φ Ω' e2 t3 ->
      (* what is regions_of(Γ, T1, T3)? *)
      typed Γ Φ Ω (Unpack e1 id t1 rs e2) t3
  | T_Call Γ Φ Φ' Ω es id rs rs' Q' tr ts :
      Γ id = Some (TTask rs' ts Φ' Q' tr) ->
      all_typed_subst Γ Φ Ω es ts rs ->
      (* Φ′[r1/r′1,...,rk/r′k]⊆Φ∗ *)
      typed Γ Φ Ω (Call id rs es) (subst_regions tr rs)
with
  all_typed_subst : Gammas -> Phis -> Omegas -> list expr -> list T -> list region -> Prop :=
  | all_typed_subst_empty Γ Φ Ω rs :
      all_typed_subst Γ Φ Ω [] [] rs
  | all_typed_subst_nonempty Γ Φ Ω e1 es t1 ts rs :
      all_typed_subst Γ Φ Ω es ts rs ->
      typed Γ Φ Ω e1 (subst_regions t1 rs)->
      all_typed_subst Γ Φ Ω (e1::es) (t1::ts) rs
.

(* Evaluation rules *)

Definition oset_mem {X Y : Type} dec (m : partial_map X (set Y)) (x : X) (a:Y) :=
  match m x with
  | Some s => set_mem dec a s
  | None => false
  end.

(* ↦ *)
Inductive eval : Ms -> Ls -> Hs -> Ss -> ClobberSet -> expr -> value -> Es -> Prop :=
  (* Trivial evaluation rules from page 23 *)
  | E_Bool (M:Ms) (L:Ls) (H:Hs) (S:Ss) (C:ClobberSet) (b:bool) :
      eval M L H S C (EBool b) (VBool b) []
  | E_Int (M:Ms) (L:Ls) (H:Hs) (S:Ss) (C:ClobberSet) (i:nat) :
      eval M L H S C (EInt i) (VInt i) []
  | E_Tuple (M:Ms) (L:Ls) (H:Hs) (S:Ss) (C:ClobberSet)
      (es : list expr) (vs : list value) (E : Es) (n:nat)
      (z1 : eval M L H S C (Tuple es) (VTuple vs) E) :
      eval M L H S C (ExprIndex (Tuple es) n) (nth n vs default_val) E

  | E_MakeTuple (M:Ms) (L:Ls) (H:Hs) (S:Ss) (C:ClobberSet)
      (es : list expr) (vs : list value) (Elist : list Es) (E' : Es)
      (zvalid : valid_interleave S C E' Elist)
      (zeval : eval_chain M L H S C es vs Elist) :
    eval M L H S C (Tuple es) (VTuple vs) (last Elist default_E)

  | E_Var (M:Ms) (L:Ls) (H:Hs) (S:Ss) (C:ClobberSet) (id : Id_T) (v : value)
      (z1 : L id = Some v) :
    eval M L H S C (Id id) v []

  | E_Let (M:Ms) (L:Ls) (H:Hs) (S:Ss) (C:ClobberSet) (e1 : expr) (v1 : value) (E1 : Es)
      (id : Id_T) (t : T)
      (L' : Ls) (S' : Ss) (e2 : expr) (v2 : value) (E2 : Es) (E' : Es)
      (zvalid : valid_interleave S C E' [E1; E2])
      (* L' = L[v1 / id] *):
    eval M L H S C (LetIn id t e1 e2) v2 E'

  | E_Add (M:Ms) (L:Ls) (H:Hs) (S:Ss) (C:ClobberSet) (e1 : expr) (E1 : Es)
      (S' : Ss) (e2 : expr) (E2 : Es) (E' : Es)
      (v' : value) (i1 : nat) (i2 : nat) (i' : nat)
      (zeval1 : eval M L H S C e1 (VInt i1) E1)
      (zapply : S' = apply S E1)
      (zeval2 : eval M L H S' C e2 (VInt i2) E2)
      (z' : v' = VInt i')
      (zplus : i' = i1 + i2)
      (zvalid : valid_interleave S C E' [E1; E2]) :
    eval M L H S C (Add e1 e2) v' E'

  | E_Compare (M:Ms) (L:Ls) (H:Hs) (S:Ss) (C:ClobberSet) (e1 : expr) (v1 : value) (E1 : Es)
      (S' : Ss) (e2 : expr) (v2 : value) (E2 : Es) (E' : Es)
      (v' : value) (i1 : nat) (i2 : nat) (b : bool)
      (zeval1 : eval M L H S C e1 (VInt i1) E1)
      (zapply : S' = apply S E1)
      (zeval2 : eval M L H S' C e2 (VInt i2) E2)
      (z' : v' = VBool b)
      (zltb : b = ltb i1 i2)
      (zvalid : valid_interleave S C E' [E1; E2]) :
    eval M L H S C (Compare e1 e2) v' E'

  | E_IsNull_F (M:Ms) (L:Ls) (H:Hs) (S:Ss) (C:ClobberSet) (e : expr) (l : location) (E : Es)
      (zeval : eval M L H S C e (VLocation l) E) :
    eval M L H S C (IsNull e) (VBool false) E

  | E_IsNull_T (M:Ms) (L:Ls) (H:Hs) (S:Ss) (C:ClobberSet) (e : expr) (l : location) (E : Es)
      (zeval : eval M L H S C e (VNull) E) :
    eval M L H S C (IsNull e) (VBool true) E

  | E_IfElse_F (M:Ms) (L:Ls) (H:Hs) (S:Ss) (C:ClobberSet) (e1 : expr) (E1 : Es)
      (S' : Ss) (e2 : expr) (e3 : expr) (v3 : value) (E3 : Es)
      (zeval1 : eval M L H S C e1 (VBool false) E1)
      (zapply : S' = apply S E1)
      (zeval3 : eval M L H S' C e3 (v3) E3) :
    eval M L H S C (If e1 e2 e3) v3 (E1 ++ E3)

  | E_IfElse_T (M:Ms) (L:Ls) (H:Hs) (S:Ss) (C:ClobberSet) (e1 : expr) (E1 : Es)
      (S' : Ss) (e2 : expr) (e3 : expr) (v2 : value) (E2 : Es)
      (zeval1 : eval M L H S C e1 (VBool true) E1)
      (zapply : S' = apply S E1)
      (zeval3 : eval M L H S' C e2 (v2) E2) :
    eval M L H S C (If e1 e2 e3) v2 (E1 ++ E2)

  (* Main rules, from page 8 *)
  | E_Read (M:Ms) (L:Ls) (H:Hs) (S:Ss) (C:ClobberSet) (e : expr) (l : location) (E : Es)
      (S' : Ss) (v : value) (v' : value)
      (zeval : eval M L H S C e (VLocation l) E)
      (zapply : S' = apply S E)
      (zv : Some v = if set_mem loc_dec l C then S' l else Some v' (* : H(l) *) ):
    eval M L H S C (Read e) v (E ++ [SRead l SExcl v 0])

  | E_Write (M:Ms) (L:Ls) (H:Hs) (S:Ss) (C:ClobberSet)
      (e1 : expr) (l : location) (E1 : Es) (S' : Ss)
      (e2 : expr) (v : value) (E2 : Es) (E' : Es)
      (zeval1 : eval M L H S C e1 (VLocation l) E1)
      (zapply : S' = apply S E1)
      (zeval2 : eval M L H S C e2 v E2)
      (zvalid : valid_interleave S C E' [E1; E2]) :
    eval M L H S C (Write e1 e2) (VLocation l) (E' ++ [SWrite l SExcl v 0])

  | E_Reduce (M:Ms) (L:Ls) (H:Hs) (S:Ss) (C:ClobberSet)
      (e1 : expr) (l : location) (E1 : Es) (S' : Ss)
      (e2 : expr) (v : value) (E2 : Es) (E' : Es)
      (id : Id_T)
      (zeval1 : eval M L H S C e1 (VLocation l) E1)
      (zapply : S' = apply S E1)
      (zeval2 : eval M L H S C e2 v E2)
      (zvalid : valid_interleave S C E' [E1; E2]) :
    eval M L H S C (Reduce id e1 e2) (VLocation l) (E' ++ [SReduce id l SExcl v 0])

  | E_New (M:Ms) (L:Ls) (H:Hs) (S:Ss) (C:ClobberSet) (l : location) (r : region)
      (t : T)
      (zincl : match (M r) with | Some rho => In l rho | None => False end)
      (* znotls : l not in domain S *)
      (zheap : H l = Some TBool (* should be H l = M[[t]] somehow? *) ):
    eval M L H S C (NewPointer t r) (VLocation l) []

  | E_UpRgn (M:Ms) (L:Ls) (H:Hs) (S:Ss) (C:ClobberSet) (e : expr) (v : value) (E : Es)
      (rs : list region)
      (zeval : eval M L H S C e v E) :
    eval M L H S C (Upregion e rs) v E

  | E_DnRgn (M:Ms) (L:Ls) (H:Hs) (S:Ss) (C:ClobberSet) (e : expr) (v : value) (E : Es)
      (l : location)
      (rs : list region)
      (zeval : eval M L H S C e v E)
      (zv : v = if (existsb (fun ri => oset_mem loc_dec M ri l) rs)
        then (VLocation l) else VNull) :
    eval M L H S C (Downregion e rs) v E

  | E_NewColor (M:Ms) (L:Ls) (H:Hs) (S:Ss) (C:ClobberSet)
      (r : region) (K : list (location * nat))
      (zm : forallb (fun lk => oset_mem loc_dec M r (fst lk)) K = true )
      (zdistinct: forall i j,
        (i >= 1 /\ i <= length K /\ j >= 1 /\ j <= length K /\ i <> j) ->
        fst (nth i K (default_loc, 0)) <> fst (nth j K (default_loc, 0))) :
    eval M L H S C (NewColor r) (VColoring K) []

  | E_Color (M:Ms) (L:Ls) (H:Hs) (S:Ss) (C:ClobberSet)
      (e1 : expr) (K : list (location * nat)) (E1 : Es) (S' : Ss)
      (e2 : expr) (l : location) (E2 : Es)
      (e3 : expr) (v : value) (E3 : Es) (E' : Es) (S'' : Ss)
      (K' : list (location * nat))
      (* (zK' : K' = (l, v) :: li, vi for li, vi in K if l <> li) *)
      (zeval1 : eval M L H S C e1 (VColoring K) E1)
      (zapply : S' = apply S E1)
      (zeval2 : eval M L H S C e2 (VLocation l) E2)
      (zapply' : S'' = apply S E2)
      (zeval3 : eval M L H S C e3 v E3)
      (zvalid : valid_interleave S C E' [E1; E2; E3]) :
    eval M L H S C (Color e1 e2 e3) (VColoring K') E'

  | E_Partition  (M:Ms) (L:Ls) (H:Hs) (S:Ss) (C:ClobberSet) (rp : region)
      (e1 : expr) (K : list (location * nat)) (E1 : Es) (S' : Ss)
      (rs : list region) (rhos : list physical_region) (e2 : expr)
      (v : value) (E2 : Es) (E' : Es)
      (zeval1 : eval M L H S C e1 (VColoring K) E1)
      (zrhos: forall i : nat, i >= 1 /\ i <= length rhos ->
        forall l : location, set_In l (nth i rhos []) <-> set_In (l, i) K)
      (zapply : S' = apply S E1)
      (zeval2 : eval M L H S C e2 v E2)
      (zvalid : valid_interleave S C E' [E1; E2])
    : eval M L H S C (Partition rp e1 rs e2) v E'

  | E_Pack (M:Ms) (L:Ls) (H:Hs) (S:Ss) (C:ClobberSet)
      (e1 : expr) (v : value) (E : Es) (rhos : list physical_region) (rs : list region)
      (t1 : T) (v' : value)
      (zeval1 : eval M L H S C e1 v E)
      (zrhos : map Some rhos = map M rs)
      (zv' : v' = VRegionRelationInstance rhos v)
    : eval M L H S C (Pack e1 t1 rs) v' E

  | E_Unpack  (M:Ms) (L:Ls) (H:Hs) (S:Ss) (C:ClobberSet)
      (e1 : expr) (rhos : list physical_region) (v1 : value) (E1 : Es)
      (M' : Ms) (rs : list region)
      (L' : Ls) (id : Id_T) (S' : Ss)
      (e2 : expr) (t : T)
      (v2 : value) (E2 : Es) (E' : Es)
      (zeval1 : eval M L H S C e1 (VRegionRelationInstance rhos v1) E1)
      (zM' : M' = add_mappings region_eq_neq M rs rhos)
      (zL' : L' = add_mapping Id_T_dec L id v1)
      (zapply : S' = apply S E1)
      (zvalid : valid_interleave S C E' [E1; E2])
    : eval M L H S C (Unpack e1 id t rs e2) v2 E'

  | E_Call (M:Ms) (L:Ls) (H:Hs) (S:Ss) (C:ClobberSet) (rs : list region)
      (aas : list Id_T) (rs' : list region)
      ( es : list expr) (vs : list value) (Elist : list Es) (Slist : list Ss)
      (M' : Ms) (L' : Ls) (S' : Ss) (C' : ClobberSet) (E' : Es) (Q' : Qs) (id : Id_T)
      (enp1 : expr) (vnp1 : value) (E'' : Es) (Enp1 : Es) (Enp1' : Es) (taskid : Task_ID)
      (zeval_chain : eval_chain_call M L H Slist C es vs Elist)
      (zS : S = hd default_S Slist)
      (zvalid : valid_interleave S C E' Elist)
      (zfunction : True) (* TODO fix *)
      (zM' : M' = add_mappings region_eq_neq (@empty region physical_region) rs'
                    (map (fun r => match M r with | Some rho => rho | None => [] end) rs))
      (zL' : L' = add_mappings Id_T_dec (@empty Id_T value) aas vs )
      (zapply : S' = apply S E')
      (zC' : True)   (* TODO: fix *)
      (zeval_np1 : eval M' L' H S' C' enp1 vnp1 Enp1)
      (zEnp1' : Enp1 = mark_coherence M' Enp1 Q' taskid) (* taskid fresh *)
      (zvalid' : valid_interleave S C E'' [E'; Enp1'])
    : eval M L H S C (Call id rs es) vnp1 E''
with
  (* needed for E_MakeTuple *)
  eval_chain : Ms -> Ls -> Hs -> Ss -> ClobberSet ->
    list expr -> list value -> list Es -> Prop :=
  | eval_chain_empty (M:Ms) (L:Ls) (H:Hs) (S:Ss) (C:ClobberSet) :
    eval_chain M L H S C [] [] []
  | eval_chain_nonempty (M:Ms) (L:Ls) (H:Hs) (S0:Ss) (C:ClobberSet)
      (e1 : expr) (v1 : value) (E1 : Es)
      (es : list expr) (vs : list value) (Elist : list Es)
    (z1 : let S1 := apply S0 E1 in eval M L H S1 C e1 v1 E1 /\
      eval_chain M L H S1 C es vs Elist) :
      eval_chain M L H (apply S0 E1) C (e1::es) (v1::vs) (E1::Elist)
with
  eval_chain_call : Ms -> Ls -> Hs -> list Ss -> ClobberSet ->
    list expr -> list value -> list Es -> Prop :=
  | eval_chain_call_empty (M:Ms) (L:Ls) (H:Hs) (S:Ss) (C:ClobberSet) :
    eval_chain_call M L H [] C [] [] []
  | eval_chain_call_nonempty (M:Ms) (L:Ls) (H:Hs) (S1:Ss) (C:ClobberSet)
      (e1 : expr) (v1 : value) (E1 : Es)
      (Slist : list Ss) (es : list expr) (vs : list value) (Elist : list Es)
    (z1 : eval M L H S1 C e1 v1 E1 /\ eval_chain_call M L H Slist C es vs Elist) :
      eval_chain_call M L H (S1::Slist) C (e1::es) (v1::vs) (E1::Elist)
.

Check eval.

(* alternate Fixpoint version of eval_chain
    match es, vs, Elist with
    | [] , [] , [] => True
    | e1::es', v1 :: vs', E1 :: Elist' =>
      let S1 := apply S0 E1 in
      eval M L H S0 C e1 v1 E1 /\ eval_chain M L H S1 C es' vs' Elist'
    | _, _ => False
    end
*)

(* used in theorem 1, 3 *)
(* E :M Φ *)
Definition privileges_cover_ops (E:Es) (M:Ms) (Φ:Phis) : Prop :=
  forall ep, In ep E -> match ep with
  | SRead l _ _ _ =>
      exists r mr, M r = Some mr /\ In l mr /\ In (Reads r) Φ
  | SWrite l _ _ _ =>
      exists r mr, M r = Some mr /\ In l mr /\ In (Writes r) Φ
  | SReduce id l _ _ _ =>
      exists r mr, M r = Some mr /\ In l mr /\ In (Reduces id r) Φ
  end.
