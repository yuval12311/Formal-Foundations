(** * Stlc: The Simply Typed Lambda-Calculus *)

(** The simply typed lambda-calculus (STLC) is a tiny core
    calculus embodying the key concept of _functional abstraction_,
    which shows up in pretty much every real-world programming
    language in some form (functions, procedures, methods, etc.).

    We will follow exactly the same pattern as in the previous chapter
    when formalizing this calculus (syntax, small-step semantics,
    typing rules) and its main properties (progress and preservation).
    The new technical challenges arise from the mechanisms of
    _variable binding_ and _substitution_.  It will take some work to
    deal with these. *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From PLF Require Import Smallstep.

Hint Resolve update_eq : core.

(* ################################################################# *)
(** * Overview *)

(** The STLC is built on some collection of _base types_:
    booleans, numbers, strings, etc.  The exact choice of base types
    doesn't matter much -- the construction of the language and its
    theoretical properties work out the same no matter what we
    choose -- so for the sake of brevity let's take just [Bool] for
    the moment.  At the end of the chapter we'll see how to add more
    base types, and in later chapters we'll enrich the pure STLC with
    other useful constructs like pairs, records, subtyping, and
    mutable state.

    Starting from boolean constants and conditionals, we add three
    things:
        - variables
        - function abstractions
        - application

    This gives us the following collection of abstract syntax
    constructors (written out first in informal BNF notation -- we'll
    formalize it below).

       t ::= x                         (variable)
           | \x:T,t                    (abstraction)
           | t t                       (application)
           | true                      (constant true)
           | false                     (constant false)
           | if t then t else t        (conditional)
*)
(** The [\] symbol in a function abstraction [\x:T,t] is usually
    written as a Greek letter "lambda" (hence the name of the
    calculus).  The variable [x] is called the _parameter_ to the
    function; the term [t] is its _body_.  The annotation [:T]
    specifies the type of arguments that the function can be applied
    to. *)

(** If you've seen lambda-calculus notation elsewhere, you might be
    wondering why abstraction is written here as [\x:T,t] instead of
    the usual "[\x:T.t]". The reason is that some front ends for
    interacting with Coq use periods to separate a file into
    "sentences" to be passed separately to the Coq top level. *)

(** Some examples:

      - [\x:Bool, x]

        The identity function for booleans.

      - [(\x:Bool, x) true]

        The identity function for booleans, applied to the boolean [true].

      - [\x:Bool, if x then false else true]

        The boolean "not" function.

      - [\x:Bool, true]

        The constant function that takes every (boolean) argument to
        [true]. *)

(**
      - [\x:Bool, \y:Bool, x]

        A two-argument function that takes two booleans and returns
        the first one.  (As in Coq, a two-argument function is really
        a one-argument function whose body is also a one-argument
        function.)

      - [(\x:Bool, \y:Bool, x) false true]

        A two-argument function that takes two booleans and returns
        the first one, applied to the booleans [false] and [true].

        As in Coq, application associates to the left -- i.e., this
        expression is parsed as [((\x:Bool, \y:Bool, x) false) true].

      - [\f:Bool->Bool, f (f true)]

        A higher-order function that takes a _function_ [f] (from
        booleans to booleans) as an argument, applies [f] to [true],
        and applies [f] again to the result.

      - [(\f:Bool->Bool, f (f true)) (\x:Bool, false)]

        The same higher-order function, applied to the constantly
        [false] function. *)

(** As the last several examples show, the STLC is a language of
    _higher-order_ functions: we can write down functions that take
    other functions as arguments and/or return other functions as
    results.

    The STLC doesn't provide any primitive syntax for defining _named_
    functions -- all functions are "anonymous."  We'll see in chapter
    [MoreStlc] that it is easy to add named functions to what we've
    got -- indeed, the fundamental naming and binding mechanisms are
    exactly the same.

    The _types_ of the STLC include [Bool], which classifies the
    boolean constants [true] and [false] as well as more complex
    computations that yield booleans, plus _arrow types_ that classify
    functions.

      T ::= Bool
          | T -> T
*)
(**
    For example:

      - [\x:Bool, false] has type [Bool->Bool]

      - [\x:Bool, x] has type [Bool->Bool]

      - [(\x:Bool, x) true] has type [Bool]

      - [\x:Bool, \y:Bool, x] has type [Bool->Bool->Bool]
                              (i.e., [Bool -> (Bool->Bool)])

      - [(\x:Bool, \y:Bool, x) false] has type [Bool->Bool]

      - [(\x:Bool, \y:Bool, x) false true] has type [Bool] *)

(* ################################################################# *)
(** * Syntax *)

(** We next formalize the syntax of the STLC. *)

Module STLC.

(* ================================================================= *)
(** ** Types *)

Inductive ty : Type :=
  | Ty_Bool  : ty
  | Ty_Arrow : ty -> ty -> ty.

(* ================================================================= *)
(** ** Terms *)

Inductive tm : Type :=
  | tm_var   : string -> tm
  | tm_app   : tm -> tm -> tm
  | tm_abs   : string -> ty -> tm -> tm
  | tm_true  : tm
  | tm_false : tm
  | tm_if    : tm -> tm -> tm -> tm.

Declare Custom Entry stlc.
Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc at level 50, right associativity).
Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc at level 90, x at level 99,
                     t custom stlc at level 99,
                     y custom stlc at level 99,
                     left associativity).
Coercion tm_var : string >-> tm.

Notation "'Bool'" := Ty_Bool (in custom stlc at level 0).
Notation "'if' x 'then' y 'else' z" :=
  (tm_if x y z) (in custom stlc at level 89,
                    x custom stlc at level 99,
                    y custom stlc at level 99,
                    z custom stlc at level 99,
                    left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := tm_true (in custom stlc at level 0).
Notation "'false'"  := false (at level 1).
Notation "'false'"  := tm_false (in custom stlc at level 0).

(** Now we need some notation magic to set up the concrete syntax, as
    we did in the [Imp] chapter... *)

Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.

(** Note that an abstraction [\x:T,t] (formally, [tm_abs x T t]) is
    always annotated with the type [T] of its parameter, in contrast
    to Coq (and other functional languages like ML, Haskell, etc.),
    which use type inference to fill in missing annotations.  We're
    not considering type inference here. *)

(** Examples... *)

Notation idB :=
  <{\x:Bool, x}>.

Notation idBB :=
  <{\x:Bool->Bool, x}>.

Notation idBBBB :=
  <{\x:((Bool->Bool)->(Bool->Bool)), x}>.

Notation k := <{\x:Bool, \y:Bool, x}>.

Notation notB := <{\x:Bool, if x then false else true}>.

(** (We write these as [Notation]s rather than [Definition]s to make
    things easier for [auto].) *)

(* ################################################################# *)
(** * Operational Semantics *)

(** To define the small-step semantics of STLC terms, we begin,
    as always, by defining the set of values.  Next, we define the
    critical notions of _free variables_ and _substitution_, which are
    used in the reduction rule for application expressions.  And
    finally we give the small-step relation itself. *)

(* ================================================================= *)
(** ** Values *)

(** To define the values of the STLC, we have a few cases to consider.

    First, for the boolean part of the language, the situation is
    clear: [true] and [false] are the only values.  An [if] expression
    is never a value. *)

(** Second, an application is not a value: it represents a function
    being invoked on some argument, which clearly still has work left
    to do. *)

(** Third, for abstractions, we have a choice:

      - We can say that [\x:T, t] is a value only when [t] is a
        value -- i.e., only if the function's body has been
        reduced (as much as it can be without knowing what argument it
        is going to be applied to).

      - Or we can say that [\x:T, t] is always a value, no matter
        whether [t] is one or not -- in other words, we can say that
        reduction stops at abstractions.

    Our usual way of evaluating expressions in Gallina makes the first
    choice -- for example,

         Compute (fun x:bool => 3 + 4)

    yields:

         fun x:bool => 7

    Most real-world functional programming languages make the second
    choice -- reduction of a function's body only begins when the
    function is actually applied to an argument.  We also make the
    second choice here. *)

Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>
  | v_true :
      value <{true}>
  | v_false :
      value <{false}>.

Hint Constructors value : core.

(** Finally, we must consider what constitutes a _complete_ program.

    Intuitively, a "complete program" must not refer to any undefined
    variables.  We'll see shortly how to define the _free_ variables
    in a STLC term.  A complete program is _closed_ -- that is, it
    contains no free variables.

    (Conversely, a term with free variables is often called an _open
    term_.) *)

(** Having made the choice not to reduce under abstractions, we don't
    need to worry about whether variables are values, since we'll
    always be reducing programs "from the outside in," and that means
    the [step] relation will always be working with closed terms.  *)

(* ================================================================= *)
(** ** Substitution *)

(** Now we come to the heart of the STLC: the operation of
    substituting one term for a variable in another term.  This
    operation is used below to define the operational semantics of
    function application, where we will need to substitute the
    argument term for the function parameter in the function's body.
    For example, we reduce

       (\x:Bool, if x then true else x) false

    to

       if false then true else false

    by substituting [false] for the parameter [x] in the body of the
    function.

    In general, we need to be able to substitute some given term [s]
    for occurrences of some variable [x] in another term [t].  In
    informal discussions, this is usually written [ [x:=s]t ] and
    pronounced "substitute [s] for [x] in [t]." *)

(** Here are some examples:

      - [[x:=true] (if x then x else false)]
           yields [if true then true else false]

      - [[x:=true] x] yields [true]

      - [[x:=true] (if x then x else y)] yields [if true then true else y]

      - [[x:=true] y] yields [y]

      - [[x:=true] false] yields [false] (vacuous substitution)

      - [[x:=true] (\y:Bool, if y then x else false)]
           yields [\y:Bool, if y then true else false]

      - [[x:=true] (\y:Bool, x)] yields [\y:Bool, true]

      - [[x:=true] (\y:Bool, y)] yields [\y:Bool, y]

      - [[x:=true] (\x:Bool, x)] yields [\x:Bool, x]

    The last example is very important: substituting [x] with [true] in
    [\x:Bool, x] does _not_ yield [\x:Bool, true]!  The reason for
    this is that the [x] in the body of [\x:Bool, x] is _bound_ by the
    abstraction: it is a new, local name that just happens to be
    spelled the same as some global name [x]. *)

(** Here is the definition, informally...

       [x:=s]x               = s
       [x:=s]y               = y                     if x <> y
       [x:=s](\x:T, t)       = \x:T, t
       [x:=s](\y:T, t)       = \y:T, [x:=s]t         if x <> y
       [x:=s](t1 t2)         = ([x:=s]t1) ([x:=s]t2)
       [x:=s]true            = true
       [x:=s]false           = false
       [x:=s](if t1 then t2 else t3) =
              if [x:=s]t1 then [x:=s]t2 else [x:=s]t3
*)

(** ... and formally: *)

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if String.eqb x y then s else t
  | <{\y:T, t1}> =>
      if String.eqb x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
      <{([x:=s] t1) ([x:=s] t2)}>
  | <{true}> =>
      <{true}>
  | <{false}> =>
      <{false}>
  | <{if t1 then t2 else t3}> =>
      <{if ([x:=s] t1) then ([x:=s] t2) else ([x:=s] t3)}>
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).

(** Note on notations: You might be wondering why we need parentheses
    around the substitution notation in the above definition, and why
    do we need to redefine the substitution notation in the [stlc]
    custom grammar. The reason is that reserved notations in
    definitions have to be defined in the general Coq grammar (and not
    a custom one like [stlc]). This restriction only applies to the
    [subst] definition, that is before the [where ...] part. From now
    on, using the substitution notation in the [stlc] custom grammar
    doesn't need any curly braces. *)

(** For example... *)
Check <{[x:=true] x}>.

(** _Technical note_: Substitution becomes trickier to define if we
    consider the case where [s], the term being substituted for a
    variable in some other term, may itself contain free variables.

    Fortunately, since we are only interested here in defining the
    [step] relation on _closed_ terms (i.e., terms like [\x:Bool, x]
    that include binders for all of the variables they mention), we
    can sidestep this extra complexity, but it must be dealt with when
    formalizing richer languages. *)

(** For example, using the definition of substitution above to
    substitute the _open_ term

      s = \x:Bool, r

    (where [r] is a _free_ reference to some global resource) for
    the free variable [z] in the term

      t = \r:Bool, z

    where [r] is a bound variable, we would get

      \r:Bool, \x:Bool, r
[]
    where the free reference to [r] in [s] has been "captured" by
    the binder at the beginning of [t]. 

    Why would this be bad?  Because it violates the principle that the
    names of bound variables do not matter.  For example, if we rename
    the bound variable in [t], e.g., let

      t' = \w:Bool, z

    then [[z:=s]t'] is

      \w:Bool, \x:Bool, r

    which does not behave the same as the original substitution into t:

      [z:=s]t = \r:Bool, \x:Bool, r

    That is, renaming a bound variable in [t] changes how [t] behaves
    under substitution. *)

(** See, for example, [Aydemir 2008] (in Bib.v) for further discussion
    of this issue. *)

(** **** Exercise: 3 stars, standard (substi_correct)

    The definition that we gave above uses Coq's [Fixpoint] facility
    to define substitution as a _function_.  Suppose, instead, we
    wanted to define substitution as an inductive _relation_ [substi].
    We've begun the definition by providing the [Inductive] header and
    one of the constructors; your job is to fill in the rest of the
    constructors and prove that the relation you've defined coincides
    with the function given above. *)

Inductive substi (s : tm) (x : string) : tm -> tm -> Prop :=
  | s_var1 :
      substi s x (tm_var x) s
  | s_var2 :
      forall y,
      x <> y ->
      substi s x (tm_var y) (tm_var y)
  | s_abst1 :
      forall t1 T,
      substi s x (<{\x:T, t1}>) (<{\x:T, t1}>)
  | s_abst2 :
      forall y t1 t2 T,
      x <> y ->
      substi s x t1 t2 ->
      substi s x (<{\y:T, t1}>) (<{\y:T, t2}>)
  | s_app :
      forall t1 t2 t3 t4,
      substi s x t1 t2 ->
      substi s x t3 t4 ->
      substi s x (<{t1 t3}>) (<{t2 t4}>)
  | s_true :
      substi s x <{true}> <{true}>
  | s_false :
      substi s x <{false}> <{false}>
  | s_if :
      forall t1 t2 t3 t4 t5 t6,
      substi s x t1 t2 ->
      substi s x t3 t4 ->
      substi s x t5 t6 ->
      substi s x (<{if t1 then t3 else t5}>) (<{if t2 then t4 else t6}>).

Hint Constructors substi : core.

Theorem substi_correct : forall s x t t',
  <{ [x:=s]t }> = t' <-> substi s x t t'.
Proof.
  split; intros. generalize dependent t'.
  -induction t; intros; subst; auto.
    + destruct ((x0 =? s0)%string) eqn:E.
      * apply eqb_eq in E. subst. simpl. rewrite eqb_refl. apply s_var1.
      * subst. simpl. rewrite E. apply eqb_neq in E. apply s_var2. apply E.
    +  simpl. apply s_app.
      * apply IHt1. reflexivity.
      * apply IHt2. reflexivity.
    + destruct ((x0 =? s0)%string) eqn:E.
      * apply eqb_eq in E. subst. simpl. rewrite eqb_refl. apply s_abst1.
      * subst. simpl. rewrite E. apply eqb_neq in E. apply s_abst2. apply E. apply IHt. reflexivity.
    + simpl. apply s_if. apply IHt1; reflexivity. apply IHt2; reflexivity. apply IHt3; reflexivity.
  - induction H; auto.
    + simpl. rewrite eqb_refl. reflexivity.
    + simpl. apply eqb_neq in H. rewrite H. reflexivity.
    + simpl. rewrite eqb_refl. reflexivity.
    + simpl. apply eqb_neq in H. rewrite H. rewrite IHsubsti. reflexivity.
    + subst. reflexivity.
    + subst. reflexivity.
 Qed.

(** [] *)

(* ================================================================= *)
(** ** Reduction *)

(** The small-step reduction relation for STLC now follows the
    same pattern as the ones we have seen before.  Intuitively, to
    reduce a function application, we first reduce its left-hand
    side (the function) until it becomes an abstraction; then we
    reduce its right-hand side (the argument) until it is also a
    value; and finally we substitute the argument for the bound
    variable in the body of the abstraction.  This last rule, written
    informally as

      (\x:T,t12) v2 --> [x:=v2]t12

    is traditionally called _beta-reduction_. *)

(** 
                               value v2
                     ---------------------------                     (ST_AppAbs)
                     (\x:T2,t1) v2 --> [x:=v2]t1

                              t1 --> t1'
                           ----------------                           (ST_App1)
                           t1 t2 --> t1' t2

                              value v1
                              t2 --> t2'
                           ----------------                           (ST_App2)
                           v1 t2 --> v1 t2'
*)
(** ... plus the usual rules for conditionals:

                    --------------------------------               (ST_IfTrue)
                    (if true then t1 else t2) --> t1

                    ---------------------------------              (ST_IfFalse)
                    (if false then t1 else t2) --> t2

                             t1 --> t1'
      --------------------------------------------------------     (ST_If)
      (if t1 then t2 else t3) --> (if t1' then t2 else t3)
*)

(** Formally: *)

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T2 t1 v2,
         value v2 ->
         <{(\x:T2, t1) v2}> --> <{ [x:=v2]t1 }>
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 t2}> --> <{v1  t2'}>
  | ST_IfTrue : forall t1 t2,
      <{if true then t1 else t2}> --> t1
  | ST_IfFalse : forall t1 t2,
      <{if false then t1 else t2}> --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      <{if t1 then t2 else t3}> --> <{if t1' then t2 else t3}>

where "t '-->' t'" := (step t t').

Hint Constructors step : core.

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

(* ================================================================= *)
(** ** Examples *)

(** Example:

      (\x:Bool->Bool, x) (\x:Bool, x) -->* \x:Bool, x

    i.e.,

      idBB idB -->* idB
*)

Lemma step_example1 :
  <{idBB idB}> -->* idB.
Proof.
  eapply multi_step.
    apply ST_AppAbs.
    apply v_abs.
  simpl.
  apply multi_refl.  Qed.

(** Example:

      (\x:Bool->Bool, x) ((\x:Bool->Bool, x) (\x:Bool, x))
            -->* \x:Bool, x

    i.e.,

      (idBB (idBB idB)) -->* idB.
*)

Lemma step_example2 :
  <{idBB (idBB idB)}> -->* idB.
Proof.
  eapply multi_step.
    apply ST_App2. auto.
    apply ST_AppAbs. auto.
  eapply multi_step.
    apply ST_AppAbs. simpl. auto.
  simpl. apply multi_refl.  Qed.

(** Example:

      (\x:Bool->Bool, x)
         (\x:Bool, if x then false else true)
         true
            -->* false

    i.e.,

       (idBB notB) true -->* false.
*)

Lemma step_example3 :
  <{idBB notB true}> -->* <{false}>.
Proof.
  eapply multi_step.
    apply ST_App1. apply ST_AppAbs. auto. simpl.
  eapply multi_step.
    apply ST_AppAbs. auto. simpl.
  eapply multi_step.
    apply ST_IfTrue. apply multi_refl.  Qed.

(** Example:

      (\x:Bool -> Bool, x)
         ((\x:Bool, if x then false else true) true)
            -->* false

    i.e.,

      idBB (notB true) -->* false.

    (Note that this term doesn't actually typecheck; even so, we can
    ask how it reduces.)
*)

Lemma step_example4 :
  <{idBB (notB true)}> -->* <{false}>.
Proof.
  eapply multi_step.
    apply ST_App2. auto.
    apply ST_AppAbs. auto. simpl.
  eapply multi_step.
    apply ST_App2. auto.
    apply ST_IfTrue.
  eapply multi_step.
    apply ST_AppAbs. auto. simpl.
  apply multi_refl.  Qed.

(** We can use the [normalize] tactic defined in the [Smallstep] chapter
    to simplify these proofs. *)

Lemma step_example1' :
  <{idBB idB}> -->* idB.
Proof. normalize.  Qed.

Lemma step_example2' :
  <{idBB (idBB idB)}> -->* idB.
Proof. normalize. Qed.

Lemma step_example3' :
  <{idBB notB true}> -->* <{false}>.
Proof. normalize.  Qed.

Lemma step_example4' :
  <{idBB (notB true)}> -->* <{false}>.
Proof. normalize.  Qed.

(** **** Exercise: 2 stars, standard, optional (step_example5)

    Try to do this one both with and without [normalize]. *)

Lemma step_example5 :
       <{idBBBB idBB idB}>
  -->* idB.
Proof.
  (* FILL IN HERE *) Admitted.

Lemma step_example5_with_normalize :
       <{idBBBB idBB idB}>
  -->* idB.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Typing *)

(** Next we consider the typing relation of the STLC. *)

(* ================================================================= *)
(** ** Contexts *)

(** _Question_: What is the type of the term "[x y]"?

    _Answer_: It depends on the types of [x] and [y]!

    I.e., in order to assign a type to a term, we need to know
    what assumptions we should make about the types of its free
    variables.

    This leads us to a three-place _typing judgment_, informally
    written [Gamma |- t \in T], where [Gamma] is a
    "typing context" -- a mapping from variables to their types. *)

(** Following the usual notation for partial maps, we write [(X |->
    T, Gamma)] for "update the partial function [Gamma] so that it
    maps [x] to [T]." *)

Definition context := partial_map ty.

(* ================================================================= *)
(** ** Typing Relation *)

(** 
                              Gamma x = T1
                            -----------------                            (T_Var)
                            Gamma |- x \in T1

                        x |-> T2 ; Gamma |- t1 \in T1
                        -----------------------------                    (T_Abs)
                         Gamma |- \x:T2,t1 \in T2->T1

                        Gamma |- t1 \in T2->T1
                          Gamma |- t2 \in T2
                         ----------------------                          (T_App)
                         Gamma |- t1 t2 \in T1

                         ---------------------                          (T_True)
                         Gamma |- true \in Bool

                         ---------------------                         (T_False)
                         Gamma |- false \in Bool

       Gamma |- t1 \in Bool    Gamma |- t2 \in T1    Gamma |- t3 \in T1
       ----------------------------------------------------------------   (T_If)
                  Gamma |- if t1 then t2 else t3 \in T1

    We can read the three-place relation [Gamma |- t \in T] as:
    "under the assumptions in Gamma, the term [t] has the type [T]." *)

Reserved Notation "Gamma '|-' t '\in' T"
            (at level 101,
             t custom stlc, T custom stlc at level 0).

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T1,
      Gamma x = Some T1 ->
      Gamma |- x \in T1
  | T_Abs : forall Gamma x T1 T2 t1,
      x |-> T2 ; Gamma |- t1 \in T1 ->
      Gamma |- \x:T2, t1 \in (T2 -> T1)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |- t1 \in (T2 -> T1) ->
      Gamma |- t2 \in T2 ->
      Gamma |- t1 t2 \in T1
  | T_True : forall Gamma,
       Gamma |- true \in Bool
  | T_False : forall Gamma,
       Gamma |- false \in Bool
  | T_If : forall t1 t2 t3 T1 Gamma,
       Gamma |- t1 \in Bool ->
       Gamma |- t2 \in T1 ->
       Gamma |- t3 \in T1 ->
       Gamma |- if t1 then t2 else t3 \in T1

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type : core.

(* ================================================================= *)
(** ** Examples *)

Example typing_example_1 :
  empty |- \x:Bool, x \in (Bool -> Bool).
Proof. eauto. Qed.

(** Note that, since we added the [has_type] constructors to the hints
    database, [auto] can actually solve this one immediately. *)

Example typing_example_1' :
  empty |- \x:Bool, x \in (Bool -> Bool).
Proof. auto.  Qed.

(** More examples:

       empty |- \x:A, \y:A->A, y (y x)
             \in A -> (A->A) -> A.
*)

Example typing_example_2 :
  empty |-
    \x:Bool,
       \y:Bool->Bool,
          (y (y x)) \in
    (Bool -> (Bool -> Bool) -> Bool).
Proof. eauto 20. Qed.

(** **** Exercise: 2 stars, standard, optional (typing_example_2_full)

    Prove the same result without using [auto], [eauto], or
    [eapply] (or [...]). *)

Example typing_example_2_full :
  empty |-
    \x:Bool,
       \y:Bool->Bool,
          (y (y x)) \in
    (Bool -> (Bool -> Bool) -> Bool).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (typing_example_3)

    Formally prove the following typing derivation holds:

    
       empty |- \x:Bool->Bool->Bool, \y:Bool->Bool, \z:Bool,
                   y (x z z)
             \in T.
*)

Example typing_example_3 :
  exists T,
    empty |-
      \x:Bool->Bool->Bool,
         \y:Bool->Bool,
            \z:Bool,
               (y (x z z)) \in
      T.
Proof.
    exists <{(Bool->Bool->Bool)->(Bool->Bool)->Bool->Bool}>.
    apply T_Abs. apply T_Abs. apply T_Abs. eapply T_App.
    -apply T_Var. reflexivity.
    -eapply T_App.
      +eapply T_App. 
        *apply T_Var. reflexivity.
        *apply T_Var. reflexivity.
      +apply T_Var. reflexivity.
Qed.
  
(** [] *)

(** We can also show that some terms are _not_ typable.  For example,
    let's check that there is no typing derivation assigning a type
    to the term [\x:Bool, \y:Bool, x y] -- i.e.,

    ~ exists T,
        empty |- \x:Bool, \y:Bool, x y \in T.
*)

Example typing_nonexample_1 :
  ~ exists T,
      empty |-
        \x:Bool,
            \y:Bool,
               (x y) \in
        T.
Proof.
  intros Hc. destruct Hc as [T Hc].
  (* The [clear] tactic is useful here for tidying away bits of
     the context that we're not going to need again. *)
  inversion Hc; subst; clear Hc.
  inversion H4; subst; clear H4.
  inversion H5; subst; clear H5 H4.
  inversion H2; subst; clear H2.
  discriminate H1.
Qed.

(** **** Exercise: 3 stars, standard (typing_nonexample_3)

    Another nonexample:

    ~ (exists S T,
          empty |- \x:S, x x \in T).
*)

Example typing_nonexample_3 :
  ~ (exists S T,
        empty |-
          \x:S, x x \in T).
Proof.
  intros Hc. destruct Hc.
  inversion H; subst; clear H.
  inversion H0; subst; clear H0.
  inversion H5; subst; clear H5.
  inversion H2; subst; clear H2.
  inversion H4; subst; clear H4.
  inversion H1; subst; clear H1.
  
  inversion H2; subst; clear H2.
  induction T2.
  -discriminate.
  -inversion H0; subst. apply IHT2_1 in H1. apply H1.
Qed.
(** [] *)

End STLC.

(* ################################################################# *)
(** * Extending STLC with an option type *)
Module OptionSTLC.
(** We wish to add options to STLC.

    Informal concrete syntax:

       t ::= x                         (variable)
           | \x:T,t                    (abstraction)
           | t t                       (application)
           | true                      (constant true)
           | false                     (constant false)
           | if t then t else t        (conditional)
           | none                      (failure)
           | some t                    (success)
           | case t of              (success)
               | none   => t
               | some x => t

(The [|] in the [case] construct is part of the syntax.)
*)
(** As an example, [case f z of | none => y | some x => x]
    will compute [f] applied to [z], and either keep going with
    [y] if it failed, or simply return the result upon success.
    In particular, note that ['none'] and ['some'] in this
    constructor is just suggestive syntax - these are not the
    constructors themselves. Moreover, the variable after the
    ['some'] part is capturing, similar to the variable after
    the ['\'] part of the lambda.
*)
(** Types are also extended:

      T ::= Bool
          | T -> T
          | option T
*)
(** Calling the term in the previous example [t], we typing
    [f : T -> option S, z : T, y : S |- s] should be valid.
    Note that the branches of [case] must give back terms
    of the same type, just like [if].
*)

(** We next formalize the syntax of the STLC. *)

(* ================================================================= *)
(** ** Types *)

Inductive ty : Type :=
  | Ty_Bool  : ty
  | Ty_Arrow : ty -> ty -> ty
  | Ty_Option : ty -> ty.

(* ================================================================= *)
(** ** Terms *)

Inductive tm : Type :=
  (* STLC with bool *)
  | tm_var   : string -> tm
  | tm_app   : tm -> tm -> tm
  | tm_abs   : string -> ty -> tm -> tm
  | tm_true  : tm
  | tm_false : tm
  | tm_if    : tm -> tm -> tm -> tm
  (* option *)
  | tm_none  : tm
  | tm_some  : tm -> tm
  | tm_case  : tm -> tm -> string -> tm -> tm.

Declare Custom Entry stlc_op.
Notation "<{ e }>" := e (e custom stlc_op at level 99).
Notation "( x )" := x (in custom stlc_op, x at level 99).
Notation "x" := x (in custom stlc_op at level 0, x constr at level 0).
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc_op at level 50, right associativity).
Notation "x y" := (tm_app x y) (in custom stlc_op at level 1, left associativity).
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc_op at level 90, x at level 99,
                     t custom stlc_op at level 99,
                     y custom stlc_op at level 99,
                     left associativity).
Coercion tm_var : string >-> tm.

Notation "{ x }" := x (in custom stlc_op at level 1, x constr).

Notation "'Bool'" := Ty_Bool (in custom stlc_op at level 0).
Notation "'if' x 'then' y 'else' z" :=
  (tm_if x y z) (in custom stlc_op at level 89,
                    x custom stlc_op at level 99,
                    y custom stlc_op at level 99,
                    z custom stlc_op at level 99,
                    left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := tm_true (in custom stlc_op at level 0).
Notation "'false'"  := false (at level 1).
Notation "'false'"  := tm_false (in custom stlc_op at level 0).

Notation "'option' T" :=
  (Ty_Option T) (in custom stlc_op at level 4).
Notation "'case' t0 'of' '|' 'none' '=>' t1 '|' 'some' x '=>' t2" :=
  (tm_case t0 t1 x t2) (in custom stlc_op at level 89,
                               t0 custom stlc_op at level 99,
                               t1 custom stlc_op at level 99,
                               x  custom stlc_op at level 99,
                               t2 custom stlc_op at level 99,
                               left associativity).
Notation "'none'" := tm_none (in custom stlc_op at level 0).
Notation "'some' t" := (tm_some t) (in custom stlc_op at level 0,
                                       t custom stlc_op at level 0).

(** Now we need some notation magic to set up the concrete syntax, as
    we did in the [Imp] chapter... *)

Definition f : string := "f".
Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Hint Unfold f : core.
Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.

(* ----------------------------------------------------------------- *)
(** *** Substitution *)

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc_op at level 20, x constr).

(** **** Exercise: 3 stars, standard (OptionSTLC.subst)

    Extend substitution for the new terms.

    You may find it necessary to escape from the STLC notational scope
    back to Coq in this exercise, such as in the following example. *)
Example escape_stlc := <{\x:Bool, {if true then <{x}> else <{x x}>}}>.
Compute escape_stlc. (* <{\x:Bool, x}> *)

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  (* STLC with bool *)
  | tm_var y =>
      if String.eqb x y then s else t
  | <{\y:T, t1}> =>
      if String.eqb x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
      <{([x:=s] t1) ([x:=s] t2)}>
  | <{true}> =>
      <{true}>
  | <{false}> =>
      <{false}>
  | <{if t1 then t2 else t3}> =>
      <{if ([x:=s] t1) then ([x:=s] t2) else ([x:=s] t3)}>

  (* Complete the option case. *)

  (* option *)
  (* FILL IN HERE *)
  | <{none}> =>
      <{none}>
  | <{some y}> =>
      <{some ([x:=s] y)}>
  | <{case f of | none => t1 | some y => t2}> =>
      <{case ([x:=s] f) of | none => ([x:=s] t1) | some y => {if String.eqb x y then t2 else <{([x:=s] t2)}> }}>
    (* ... and delete this line when you finish the exercise *)
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc_op).

Example subst1 : <{[x := false] (case x of | none => false | some y => x)}> = <{(case false of | none => false | some y => false)}>.
Proof. reflexivity. Qed.

Example subst2 : <{[x := false] (case x of | none => x | some x => x)}> = <{(case false of | none => false | some x => x)}>.
Proof. reflexivity. Qed.

Example subst3 : <{[x := some y] (some (\y: Bool, x (\x: Bool, y)))}> = <{[x := false] (some (\y: Bool, (some y) (\x: Bool, y)))}>.
Proof. reflexivity. Qed.

(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Reduction *)

(** Next we define the values of our language. *)

Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>
  | v_true :
      value <{true}>
  | v_false :
      value <{false}>
  (* The additional values  *)
  | v_none :
      value <{none}>
  | v_some : forall v,
      value v ->
      value <{some v}>.

Hint Constructors value : core.

Reserved Notation "t '-->' t'" (at level 40).

(** **** Exercise: 3 stars, standard (OptionSTLC.step)

    Extend reduction for the new terms. *)
Inductive step : tm -> tm -> Prop :=
  (* STLC with bool *)
  | ST_AppAbs : forall x T2 t1 v2,
         value v2 ->
         <{(\x:T2, t1) v2}> --> <{ [x:=v2]t1 }>
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 t2}> --> <{v1  t2'}>
  | ST_IfTrue : forall t1 t2,
      <{if true then t1 else t2}> --> t1
  | ST_IfFalse : forall t1 t2,
      <{if false then t1 else t2}> --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      <{if t1 then t2 else t3}> --> <{if t1' then t2 else t3}>

  (* Complete the option case. *)
  | ST_Option : forall  t1 t1',
      t1 --> t1' ->
      <{some t1}> --> <{some t1'}>
  | ST_CaseNone : forall x t2 t3,
      <{case none of | none => t2 | some x => t3}> --> t2
  | ST_CaseSome : forall x y t2 t3,
      <{case (some y) of | none => t2 | some x => t3}> --> <{ [x:=y]t3 }>
  | ST_Case : forall t1 t1' t2  t3,
      t1 --> t1' ->
      <{case t1 of | none => t2 | some x => t3}> --> <{case t1' of | none => t2 | some x => t3}>

  (* option *)
  (* FILL IN HERE *)

  where "t '-->' t'" := (step t t').

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Hint Constructors step : core.

(** If your definitions are correct, you can use the [normalize] 
tactic defined in the [Smallstep] chapter to prove the following. *)

Example step1 : <{(\x: option Bool, case x of | none => false | some x => x) (some true)}> -->* <{true}>.
Proof. 
 eapply multi_step.
  -eapply ST_AppAbs. apply v_some. apply v_true.
  -eapply multi_step.
    + simpl. eapply ST_CaseSome.
    + eapply multi_refl. 
Qed.

Example step2 : <{(\x: option Bool, case x of | none => false | some x => x) (some false)}> -->* <{false}>.
Proof. 
 eapply multi_step.
  -eapply ST_AppAbs. apply v_some. apply v_false.
  -eapply multi_step.
    + simpl. eapply ST_CaseSome.
    + eapply multi_refl.
Qed.

Example step3 : <{(\x: option Bool, case x of | none => false | some x => x) none}> -->* <{false}>.
Proof. 
eapply multi_step.
  -eapply ST_AppAbs. apply v_none.
  -eapply multi_step.
    + simpl. eapply ST_CaseNone.
    + eapply multi_refl.
Qed.

(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Typing *)

Definition context := partial_map ty.

Reserved Notation "Gamma '|-' t '\in' T" (at level 101, t custom stlc_op, T custom stlc_op at level 0).

(** **** Exercise: 3 stars, standard (OptionSTLC.has_type) *)
Inductive has_type : context -> tm -> ty -> Prop :=
  (* STLC with bool *)
  | T_Var : forall Gamma x T1,
      Gamma x = Some T1 ->
      Gamma |- x \in T1
  | T_Abs : forall Gamma x T1 T2 t1,
      x |-> T2 ; Gamma |- t1 \in T1 ->
      Gamma |- \x:T2, t1 \in (T2 -> T1)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |- t1 \in (T2 -> T1) ->
      Gamma |- t2 \in T2 ->
      Gamma |- t1 t2 \in T1
  | T_True : forall Gamma,
       Gamma |- true \in Bool
  | T_False : forall Gamma,
       Gamma |- false \in Bool
  | T_If : forall t1 t2 t3 T1 Gamma,
       Gamma |- t1 \in Bool ->
       Gamma |- t2 \in T1 ->
       Gamma |- t3 \in T1 ->
       Gamma |- if t1 then t2 else t3 \in T1

  (* Complete the option case. *)
  | T_OptionSome : forall t1 T1 Gamma,
      Gamma |- t1 \in T1 ->
      Gamma |- some t1 \in option T1
  | T_OptionNone : forall T1 Gamma,
      Gamma |- none \in option T1

  | T_Case : forall x t1 t2 t3 T1 T2 Gamma,
      Gamma |- t1 \in (option T1) ->
      Gamma |- t2 \in T2 ->
      x |-> T1; Gamma |- t3 \in T2 ->
      Gamma |- case t1 of | none => t2 | some x => t3 \in T2
      
  (* option *)
  (* FILL IN HERE *)

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type : core.

Example type1 : empty |- (\x: option Bool, case x of | none => false | some x => x) (some true) \in Bool.
Proof. 
  eapply T_App.
    - eapply T_Abs.
      + eapply T_Case.
        * apply T_Var. reflexivity.
        * apply T_False.
        * apply T_Var. reflexivity.
    - apply T_OptionSome. apply T_True.
Qed.

Example type2 : empty |- (\x: option Bool, case x of | none => false | some x => x) (some false) \in Bool.
Proof. 
  eapply T_App.
    - eapply T_Abs.
      + eapply T_Case.
        * apply T_Var. reflexivity.
        * apply T_False.
        * apply T_Var. reflexivity.
    - apply T_OptionSome. apply T_False.
Qed.

Example type3 : empty |- (\x: option Bool, case x of | none => false | some x => x) none \in Bool.
Proof.  
  eapply T_App.
    - eapply T_Abs.
      + eapply T_Case.
        * apply T_Var. reflexivity.
        * apply T_False.
        * apply T_Var. reflexivity.
    - apply T_OptionNone.
Qed.
(** [] *)

End OptionSTLC.


(* ################################################################# *)
(** * Modeling CBN in STLC with a unit type *)

(* In class we discussed the differences between Call-by-Value (CBV) and
Call-by-Name (CBN). In this exercise we add a unit element (and Unit type) to
STLC, and use it in order to simulate CBN evaluation inside out CBV-based
operational semantics. *)

Module CBN_Unit.

(* We start by adding [Unit] type and [unit] term to the core language 
defined above. *)

Inductive ty : Type :=
  | Ty_Bool  : ty
  | Ty_Arrow : ty -> ty -> ty
  | Ty_Unit : ty.

Inductive tm : Type :=
  | tm_var   : string -> tm
  | tm_app   : tm -> tm -> tm
  | tm_abs   : string -> ty -> tm -> tm
  | tm_true  : tm
  | tm_false : tm
  | tm_if    : tm -> tm -> tm -> tm
  | tm_unit : tm.

Declare Custom Entry stlc_un.
Notation "<{ e }>" := e (e custom stlc_un at level 99).
Notation "( x )" := x (in custom stlc_un, x at level 99).
Notation "x" := x (in custom stlc_un at level 0, x constr at level 0).
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc_un at level 50, right associativity).
Notation "x y" := (tm_app x y) (in custom stlc_un at level 1, left associativity).
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc_un at level 90, x at level 99,
                     t custom stlc_un at level 99,
                     y custom stlc_un at level 99,
                     left associativity).
Coercion tm_var : string >-> tm.

Notation "{ x }" := x (in custom stlc_un at level 1, x constr).

Notation "'Bool'" := Ty_Bool (in custom stlc_un at level 0).
Notation "'if' x 'then' y 'else' z" :=
  (tm_if x y z) (in custom stlc_un at level 89,
                    x custom stlc_un at level 99,
                    y custom stlc_un at level 99,
                    z custom stlc_un at level 99,
                    left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := tm_true (in custom stlc_un at level 0).
Notation "'false'"  := false (at level 1).
Notation "'false'"  := tm_false (in custom stlc_un at level 0).

Notation "'Unit'" :=
  (Ty_Unit) (in custom stlc_un at level 0).
Notation "'unit'" := tm_unit (in custom stlc_un at level 0).

(** Now we need some notation magic to set up the concrete syntax, as
    we did in the [Imp] chapter... *)

Definition f : string := "f".
Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Hint Unfold f : core.
Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.

(* Next we repeat the substitution operation, and extend it with a trivial case for [unit]. *)

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc_un at level 20, x constr).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if String.eqb x y then s else t
  | <{\y:T, t1}> =>
      if String.eqb x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
      <{([x:=s] t1) ([x:=s] t2)}>
  | <{true}> =>
      <{true}>
  | <{false}> =>
      <{false}>
  | <{if t1 then t2 else t3}> =>
      <{if ([x:=s] t1) then ([x:=s] t2) else ([x:=s] t3)}>
  | <{unit}> => <{unit}>
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc_un).

(* Next we define the values of our language, and the small-step 
operational semantics. Note that we keep the semantics to be CBV 
(we actually don't change anything there, [unit] cannot step). *)

Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>
  | v_true :
      value <{true}>
  | v_false :
      value <{false}>
  (* unit is a value *)
  | v_unit : value <{unit}>.

Hint Constructors value : core.

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T2 t1 v2,
         value v2 ->
         <{(\x:T2, t1) v2}> --> <{ [x:=v2]t1 }>
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 t2}> --> <{v1  t2'}>
  | ST_IfTrue : forall t1 t2,
      <{if true then t1 else t2}> --> t1
  | ST_IfFalse : forall t1 t2,
      <{if false then t1 else t2}> --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      <{if t1 then t2 else t3}> --> <{if t1' then t2 else t3}>

  where "t '-->' t'" := (step t t').

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Hint Constructors step : core.

(* And here are some examples of functions, like we had before: *)

Notation idB :=
  <{\x:Bool, x}>.

Notation idBB :=
  <{\x:Bool->Bool, x}>.

Notation idBBBB :=
  <{\x:((Bool->Bool)->(Bool->Bool)), x}>.

Notation k := <{\x:Bool, \y:Bool, x}>.

Notation notB := <{\x:Bool, if x then false else true}>.

(* Now, consider the following example for emulating CBN.
Suppose we want to execute [k (notB true) (notB false)] in CBN.
We can instead run in CBV the program:

[k' (\z: Unit (notB true)) (\z: Unit (notB false))]

where

[k' := \x:Unit -> Bool, \y:Unit -> Bool, x unit]

How will the execution proceed?

Since t1=(\z: Unit (notB true)) and t2=(\z: Unit (notB false))
are both abstractions, they are values, so the first two steps
perform the substitutions in k', leading to:

[(\z: Unit (notB true)) unit]

Then, the next step will lead us to

[notB true]

which evaluates to [false].

Importantly, we never evaluated [notB false]! *)

(* Your goal is to generalize this idea and define a function that 
translates a term [t] into another term [t'] such that the CBV 
evaluation of [t'] simulates the CBN evaluation of [t]. *)

(** You may find it necessary to escape from the STLC notational scope
    back to Coq in this exercise, such as in the following example. *)
Example escape_stlc := <{\x:Bool, {if true then <{x}> else <{x x}>}}>.
Compute escape_stlc. (* <{\x:Bool, x}> *)

(** **** Exercise: 5 stars, standard (CBN_Unit.make_cbn) *)
Fixpoint make_cbn (t : tm) : tm :=
  match t with
  | tm_var y =>
      <{y unit}>
  | <{\y:T, t1}> =>
      <{\y:Unit->T, {make_cbn t1}}>
  | <{t1 t2}> =>
      tm_app (make_cbn t1) <{\x:Unit, ({make_cbn t2})}>
  | <{true}> =>
      <{true}>
  | <{false}> =>
      <{false}>
  | <{if t1 then t2 else t3}> =>
      <{if {make_cbn t1} then {make_cbn t2} else {make_cbn t3}}>
  | <{unit}> => <{unit}>
 
  end.
(** [] *)

(* Here are some tests that should pass. You may use the [normalize] tactic 
defined in the [Smallstep] chapter to simplify these proofs. 
The tactic also prints the steps it performed, so you can see what happens. *)

(** **** Exercise: 1 star, standard (CBN_Unit.cbn1) *)
Lemma cbn1 :
       (make_cbn <{ notB (notB true) }>)
  -->* <{ true }>.
Proof.
simpl. normalize. Qed.

  (* FILL IN HERE *) 
(** [] *)

(** **** Exercise: 1 star, standard (CBN_Unit.cbn2) *)
Lemma cbn2 :
       (make_cbn <{ (idBB notB) (notB true)}>)
  -->* <{ true }>.
Proof.
simpl. normalize. Qed.
(** [] *)

(** **** Exercise: 1 star, standard (CBN_Unit.cbn3) *)
Lemma cbn3 : forall t, 
       (make_cbn <{ k (notB true) t }>)
  -->* <{ false }>.
Proof.
(* If your definition is correct, 
you never need to destruct/induct on t. *)
intros t. simpl. normalize. Qed.
(** [] *)

End CBN_Unit.

(* 2023-01-05 13:10 *)
