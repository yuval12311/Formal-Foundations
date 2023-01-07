(** * MoreFP: Advanced Functional Programming *)

(** We will introduce (using example):

    1) Type classes

    2) Monads

    We use Coq as a functional programming language.
*)



(** Slides are based on:

    - Chapter from volume 4 of Software Foundations (QuickChick) by 
      Leonidas Lampropoulos and Benjamin C. Pierce.
    - Slides by Nadia Polikarpova (Programming Languages in Haskell)
*)

From Coq Require Import Bool.Bool.
From Coq Require Import Strings.String.
From Coq Require Import Arith.Arith.
From Coq Require Import List. 
Import ListNotations.
Local Open Scope string.
From Coq Require Import Recdef.

Section Monads.

(* ################################################################# *)
(** * Typeclasses *)

(** Suppose we need string converters for lots of data structures.

    We can build a small library of primitives

       showBool : bool -> string
       showNat : nat -> string

    and combinators for structured types:

     showList : {A : Type}
                (A -> string) -> (list A) -> string
     showPair : {A B : Type}
                (A -> string) -> (B -> string) -> A * B -> string

    Then we can build string converters for more
    complex structured types by assembling them from these pieces:

     showListOfPairsOfNats = showList (showPair showNat showNat)
*)

(** This works, but it's clunky.
      - Requires making up names for all these string converters,
        when it seems they could be generated automatically.
      - Moreover, even the _definitions_ of converters like
        [showListOfPairsOfNats] seem pretty mechanical, given their
        types.

    Solution: _Typeclasses_.
      - Based on Haskell
      - This is not "classes" as in object-oriented programming.
 *)

(* ================================================================= *)
(** ** Classes and Instances *)

(** To automate converting various kinds of data into strings, we
    begin by defining a typeclass called [Show]. *)

Class Show (A : Type) :=
  {
    show : A -> string
  }.

(** A class definition defines an interface for some type.

   We say that types [A] that implement the [Show] interface have
   a method named show that will convert them to a string.

   So we can use the generic method [show] on any type [A] that is
   an instance of the [Show] class. 

   In general, you can have multiple things in the interface.
*)

(** The [Show] typeclass can be thought of as "classifying" types
    whose values can be converted to strings -- that is, types [A]
    such that we can define a function [show] of type [A -> string].

    We can declare that [bool] is such a type by giving an [Instance]
    declaration that witnesses this function: *)

Instance showBool : Show bool :=
  {
    show := fun b:bool => if b then "אמת" else "שקר"
  }.

Compute show true.
(* ==> "אמת" : string

    Other types can similarly be equipped with [Show] instances --
    including, of course, new types that we define. *)

Inductive primary := Red | Green | Blue.

Instance showPrimary : Show primary :=
  {
    show :=
      fun c:primary =>
        match c with
        | Red => "Red"
        | Green => "Green"
        | Blue => "Blue"
        end
  }.

Compute show Green.
(* ==> "Green" : string *)

(** Importantly, we still have the ability to show booleans. *)

Compute show true.
(* ==> "אמת" : string

    The [show] function is sometimes said to be _overloaded_, since it
    can be applied to arguments of many types, with potentially
    radically different behavior depending on the type of its
    argument.
    This is _not_ parametric polymorphism. *)

(* ================================================================= *)
(** **   [show] for nat *)
Compute show 3.
(* This doesn't work because we haven't said how to show a nat. *)

(** Let's define nat as an instance of Show. *)

(** We first need
   some helper functions to convert nats to strings. *)

Definition num2string (d : nat) : string := 
  match d with 
    | 0 => "0"  | 1 => "1"  | 2 => "2"  | 3 => "3"
    | 4 => "4"  | 5 => "5"  | 6 => "6"  | 7 => "7"
    | 8 => "8"  | 9 => "9"  | 10 => "A" | 11 => "B"
    | 12 => "C" | 13 => "D" | 14 => "E" | 15 => "F"
    | _ => "ERROR"
  end.

(** Now, [string_of_nat] is defined as follows. *)

Fail Fixpoint string_of_nat_aux (n : nat) (acc : string) : string :=
  let acc' := num2string (n mod 16) ++ acc in
    match n / 16 with
      | 0 => acc'
      | n' => string_of_nat_aux n' acc'
    end.

(* Cannot guess decreasing argument of fix. *)

(** To convince Coq that [string_of_nat_aux] terminates
   we give it fuel.  *)

Fixpoint string_of_nat_aux 
  (fuel n : nat) (acc : string) : string :=
  match fuel with
    | 0 => "ERROR"
    | S fuel' =>
        let acc' := num2string (n mod 16) ++ acc in
          match n / 16 with
            | 0 => acc'
            | n' => string_of_nat_aux fuel' n' acc'
          end
  end.

(** It's sufficient to use [S n] as the fuel here since
   we know we won't need to divide [n] by [16] more than
   [S n] times.  We could of course use something like
   [log_16 n], but there's no need to bother here. *)

Definition string_of_nat (n : nat) : string :=
  string_of_nat_aux (S n) n "".

(** Coq also has a mechanism to allow a definition without fuel. *)

Function digits_no_fuel (n : nat) (acc : string) 
  {measure (fun x : nat => x) n} :=
  let acc' := num2string (n mod 16) ++ acc in
  match n with
    | 0 => acc'
    | _ => match n / 16 with
           | 0 => acc'
           | n' => digits_no_fuel n' acc'
         end
  end.
Proof.
  intros. rewrite <- teq0.
  apply Nat.div_lt.
  - apply Nat.lt_0_succ.
  - apply Nat.leb_le. reflexivity.
Defined.

Definition string_of_nat_no_fuel (n : nat) : string :=
  digits_no_fuel n "".

(** Now we can define our [nat] instance for the Show class. *)

Instance showNat : Show nat :=
  {
    show := string_of_nat
  }.

Compute show 0.
(* ==> "0" : string *)

Compute show 100.
(* ==> "64" : string *)

Compute show (S (S 0)).
(* ==> "2" : string *)

Compute show (7 + 4 + 18).
(* ==> "1D" : string *)

(** Parameterized instances allow us to show data structures.

    The following is a generic instance in that if we can have two types
    [A] and [B] that are instances of the [Show] class, then we can
    build a generic [Show] for the product type [A*B].
*)

Instance showPair (A B : Type)
  (showA : Show A) (showB : Show B) : Show (A*B) := 
{
  show := (fun p =>    "<" 
                    ++ (show (fst p)) 
                    ++ ","
                    ++ (show (snd p)) 
                    ++ ">")
}.

(** Since we can have pairs of any types, we parameterize
    our [Show] instance by two types.  We need to
    constrain both of these types to be instances of [Show]. *)

Compute show (3,4).
(* ==> "<3,4>" : string *)

Compute show (true,40).
(* ==> "<אמת,28>" : string *)

(**  [showA] and [showB] are _evidence_ that [A] and [B] are 
    instances of [Show]. *)

(** Note that we never use the terms [showA] and [showB], 
   so the following is also ok: *)

Instance showPair' (A B : Type) 
  (_ : Show A) (_ : Show B) : Show (A*B) := 
{
  show := (fun p =>    "<" 
                    ++ (show (fst p)) 
                    ++ ","
                    ++ (show (snd p)) 
                    ++ ">")
}.

(** ...and here is [Show] for lists: *)

Fixpoint showListAux {A : Type} 
  (s : A -> string) (l : list A) : string :=
  match l with
    | nil => ""
    | cons h nil => s h
    | cons h t => (s h) ++ ", " ++ (showListAux s t)
  end.

Instance showList (A : Type) (_ : Show A) : Show (list A) :=
  {
    show l := "[" ++ (showListAux show l) ++ "]"
  }.

Compute (show [1;2;9]).
(* ==> "[[1, 2, 9]]" : string *)

Compute (show [true;true]).
(* ==> "[[אמת, אמת]]" : string *)

(* ================================================================= *)
(** **   Equality Testers *)

(** Of course, [Show] is not the only interesting typeclass.  There
    are many other situations where it is useful to be able to
    choose (and construct) specific functions depending on the type of
    an argument that is supplied to a generic function like [show]. *)

(** Here is another basic example of typeclasses: a class [Eq]
    describing types with a (boolean) test for equality. *)

Class Eq (A : Type) :=
  {
    eqb: A -> A -> bool;
  }.

Notation "x =? y" := (eqb x y) (at level 70).

(** And here are some basic instances: *)

Instance eqBool : Eq bool :=
  {
    eqb := fun (b c : bool) =>
       match b with
         | true  => c
         | false => negb c
       end
  }.

Instance eqNat : Eq nat :=
  {
    eqb := Nat.eqb
  }.

Example eqBool_ex : (true =? negb false) = true.
Proof. reflexivity. Qed.

Example eqNat_ex : (7 =? 100 - 94) = false.
Proof. reflexivity. Qed.

(** **** Exercise: 3 stars, standard (boolArrowBool)

    There are some function types, like [bool->bool], for which
    checking equality makes perfect sense.  Write an [Eq] instance for
    this type. Include some test cases (e.g., simple logical equivalences) 
    as Examples proved using [reflexivity].  *)

Instance eqBoolBool : Eq (bool->bool) :=
  {
    eqb := fun f g => 
        (f true =? g true) && (f false =? g false)
  }.

Example eqBoolBool_ex1 : eqb negb (fun x => negb (negb (negb x))) = true.
Proof. reflexivity. Qed.
Example eqBoolBool_ex2 : eqb negb (fun x => negb (negb x)) = false.
Proof. reflexivity. Qed.
Example eqBoolBool_ex3 : eqb negb negb = true.
Proof. reflexivity. Qed.
(** [] *)

(** Here is an [Eq] instance for pairs... *)

Instance eqPair (A B : Type) (_ : Eq A) (_ : Eq B) : Eq (A * B) :=
  {
    eqb p1 p2 :=
      let (p1a,p1b) := p1 in
      let (p2a,p2b) := p2 in
      andb (p1a =? p2a) (p1b =? p2b)
  }.

(** **** Exercise: 3 stars, standard (eqEx)

    Write an [Eq] instance for lists and [Show] and [Eq] instances for
    the [option] type constructor. In particular, the examples should
    all hold. *)

(* FILL IN HERE *)

Fixpoint eqlist {A : Type} (e:Eq A) (l1 l2 : list A): bool :=
  match l1, l2 with
    | h1 :: t1, h2 :: t2 => (h1 =? h2) && eqlist e t1 t2 
    | [], [] => true
    | _, _ => false
    end.

Instance eqList {A : Type} (e : Eq A) : Eq (list A) :=
{eqb := eqlist e
}.
Example eqList_ex1 : eqb [1;2;9] [1;2;9] = true.
Proof. reflexivity. Qed.

Example eqList_ex2 : eqb [1;2;9] [1] = false.
Proof. reflexivity. Qed.

Example eqList_ex3 : eqb [(true,true);(false,true)] [(true,true);(false,true)] = true.
Proof. reflexivity. Qed.

Example eqList_ex4 : eqb [] [(true,true);(false,true)] = false.
Proof. reflexivity. Qed.

(* GRADE_THEOREM 0.25: eqList_ex1 *)
(* GRADE_THEOREM 0.25: eqList_ex2 *)
(* GRADE_THEOREM 0.25: eqList_ex3 *)
(* GRADE_THEOREM 0.25: eqList_ex4 *)
 Compute Show.

Instance showOpt (A : Type) (_ : Show A) : Show (option A) :=
{
  show xs := match xs with
      | None => "[||]"
      | Some x => "[|" ++ show x ++ "|]"
end
}.

Example showOpt_ex1 : show (Some 5) = "[|5|]".
Proof. reflexivity. Qed.

Example showOpt_ex2 : show (None) = "[||]".
Proof. reflexivity. Qed.

Instance eqOpt (A : Type) (_ : Eq A) : Eq (option A):=
{eqb xs ys :=
    match xs, ys with
    | Some x, Some y => x =? y
    | None, None => true
    | _, _ => false
    end
}.

Example eqOpt_ex1 : eqb (Some false) (Some true) = false.
Proof. reflexivity. Qed.
Example eqOpt_ex2 : eqb (Some [(true,true);(false,true)]) (Some [(true,true);(false,true)]) = true.
Proof. reflexivity. Qed.

Example eqOpt_ex3 : eqb (Some false) None = false.
Proof. reflexivity. Qed.

Example eqOpt_ex4 : eqb None None = true.
Proof. reflexivity. Qed.

(* GRADE_THEOREM 0.25: eqOpt_ex1 *)
(* GRADE_THEOREM 0.25: eqOpt_ex2 *)
(* GRADE_THEOREM 0.25: eqOpt_ex3 *)
(* GRADE_THEOREM 0.25: eqOpt_ex4 *)

(** [] *)

(** **** Exercise: 3 stars, standard (boolArrowA)

    Generalize your solution to the [boolArrowBool] exercise to build
    an equality instance for any type of the form [bool->A], where [A]
    itself is an [Eq] type.  Demonstrate that it works for [bool->bool->nat]. *)

Instance eqBoolA (A : Type) : Eq A -> Eq (bool -> A) := {
  eqb f g := (f true =? g true) && (f false =? g false)
}.

Compute (eqb (fun (b1 b2 : bool) => if b1 then 42 else 9)
             (fun (b1 b2 : bool) => if b2 then 42 else 9)).

Example eqBoolA_ex1 : eqb negb (fun x => negb (negb (negb x))) = true.
Proof. reflexivity. Qed.
Example eqBoolA_ex2 : (eqb (fun (b1 b2 : bool) => if b1 then 42 else 9)
                              (fun (b1 b2 : bool) => if b2 then 42 else 9)) = false.
Proof. reflexivity. Qed.
Example eqBoolA_ex3 : (eqb (fun (b1 b2 : bool) => if b1 && b2 then 42 else 9)
                              (fun (b1 b2 : bool) => if negb (b2 && b1) then 9 else 42)) = true.
Proof. reflexivity. Qed.

(** [] *)

(* ================================================================= *)
(** **   Typeclasses Hierarchies *)

(** We often want to organize typeclasses into hierarchies.  For
    example, we might want a typeclass [Ord] for "ordered types" that
    support both equality and a less-or-equal comparison operator. *)

(** A possible (but bad) way to do this is to define a new class with
    two associated functions: *)

Class OrdBad (A : Type) :=
  {
    eqbad : A -> A -> bool;
    lebad : A -> A -> bool
  }.

(** The reason this is bad is because we now need to use a new
    equality operator ([eqbad]) if we want to test for equality on
    ordered values. *)

(** A much better way is to parameterize the definition of [Ord] on an
    [Eq] class constraint: *)

Class Ord (A : Type) {H : Eq A} : Type :=
  {
    le : A -> A -> bool
  }.

Notation "x <=? y" := (le x y) (at level 70).

(** When we define instances of [Ord], we just have to implement the
    [le] operation. *)

Instance ordNat : Ord nat :=
  {
    le := Nat.leb 
  }.

(** Functions expecting to be instantiated with an instance of [Ord]
    now have two class constraints, one witnessing that they have an
    associated [eqb] operation, and one for [le]. *)

Definition max {A: Type} {_ : Eq A} {_: Ord A} (x y : A) : A :=
  if x <=? y then y else x.

(** The parameters [_:Eq A] and [_:Ord A] are _class constraints_, 
    which state that the function [max] is expected to be applied only to
    types [A] that belong to the [Eq] and [Ord] classes.
*)

Compute (max 4 5).
(* ==> 5 : nat *)


(** There is mechanism for implicit generalization that is helpful here: *)

Definition max' {A: Type} `{Ord A} (x y : A) : A :=
  if x <=? y then y else x.

(** **** Exercise: 3 stars, standard (ordMisc)

    Define [Ord] instances for pairs.
    Include some examples. *)

Instance ordPair  (X Y: Type) `(Ord X) `(Ord Y) : Ord (X *Y) := {

  le p1 p2 := let (x1, y1) := p1 in
             let (x2, y2) := p2 in
                if x1 =? x2 then y1 <=? y2 
                else if x1 <=? x2 then true else false
}.


Example ex1: (5, 3) <=? (6, 3) = true.
Proof. reflexivity. Qed.
Example ex2: (5, 3) <=? (5, 3) = true.
Proof. reflexivity. Qed.
Example ex3: (5, 3) <=? (5, 4) = true.
Proof. reflexivity. Qed.
Example ex4: (5, 3) <=? (4, 3) = false.
Proof. reflexivity. Qed.
(* FILL IN HERE *)
(* Do not modify the following line: *)
Definition manual_grade_for_ordMisc : option (nat*string) := None.
(** [] *)

(** **** Exercise: 3 stars, standard (ordList)

    For a little more practice, define an [Ord] instance for lists.
    Include some examples. *) 
Fixpoint ordlist {X: Type} (e1:Eq X) (e2:Ord X) (l1 l2 : list X) : bool :=
 match l1, l2 with
             | h1::t1, h2::t2 => if h1 =? h2 then (ordlist e1 e2 t1 t2) 
                else if h1 <=? h2 then true else false
             | [], _ => true
             | _, _ => false
            end.

Instance ordList  (X : Type) (e1:Eq X) (e2:Ord X) : Ord (list X) := {

  le := ordlist e1 e2
}.


Example exl1: [5; 3] <=? [6; 3] = true.
Proof. reflexivity. Qed.
Example exl2: [5; 3 ; 4] <=? [5; 3] = false.
Proof. reflexivity. Qed.

(* FILL IN HERE *)
(* Do not modify the following line: *)
Definition manual_grade_for_ordList : option (nat*string) := None.


(** [] *)

(* ================================================================= *)
(** ** The Functor Class *)

Class Functor (F : Type -> Type) := {
  fmap : forall {A B : Type}, (A -> B) -> F A -> F B;
}.

(** Here, it's not a type that is a functor, but rather a 
    type constructor (i.e., a function from types to types).
*)

Fixpoint mapList {A B : Type} (f : A -> B) (xs : list A) :=
  match xs with
    | [] => []
    | x :: xs => (f x) :: (mapList f xs)
  end.

Instance functorList : Functor list := {
  fmap A B := mapList
}.

Compute (fmap S [1;2;9]).
(* ==> [[2; 3; 10]] : list nat *)

(* ================================================================= *)
(** ** Trees *)

Inductive tree (X : Type) : Type :=
  | Leaf
  | Node (x : X) (l : tree X) (r : tree X).

Arguments Leaf {X}.
Arguments Node {X}.

Fixpoint mapTree {A B : Type} (f : A -> B) (t : tree A) :=
  match t with
    | Leaf => Leaf
    | Node x l r  => Node (f x) (mapTree f l) (mapTree f r)
  end.

Instance functorTree : Functor tree := {
  fmap A B := mapTree
}.

Compute (fmap S (Node 5  (Node 7 Leaf Leaf) 
                (Node 12 (Node 7 Leaf Leaf) Leaf))).
(* ==> Node 6 (Node 8 Leaf Leaf) (Node 13 (Node 8 Leaf Leaf) Leaf) : tree nat *)

Definition showall {F : Type -> Type} {_ : Functor F}
                   {A : Type} {_ : Show A} 
                   (x : F A) : F string :=
  fmap show x.

Compute (showall (Node true (Node false Leaf Leaf) 
                 (Node false Leaf Leaf))).

(** **** Exercise: 1 star, standard (functorOpt)

    Define Option as an instance of Functor. *) 

Instance functorOption : Functor option := {
  fmap A B f xs := match xs with
      | None => None
      | Some x => Some (f x)
  end
}.

Example functorOpt_ex1 : fmap S None = None.
Proof. reflexivity. Qed.

Example functorOpt_ex2 : fmap S (Some 1) = Some 2.
Proof. reflexivity. Qed.

(** [] *)

(** A functor instance has to to satisfy two constraints: 

- fmap_id: 

forall (A : Type), fmap (@id A) = id

- fmap_comp : 

forall (A B C : Type) (f : B -> C) (g : A -> B),
      fmap (fun x => f (g x)) = fun x => (fmap f (fmap g x))
*)

(** **** Exercise: 2 stars, standard (fmap_tree)

    Prove the required properties for the tree instance. *) 

Lemma fmap_id_tree : forall (A : Type) (t : tree A), 
  @fmap tree _ _ _ (@id A) t = id t.
Proof.
  intros. induction t.
    -reflexivity.
    -simpl. simpl in IHt1, IHt2. rewrite IHt1. rewrite IHt2. reflexivity.
Qed.

Lemma fmap_comp_tree : forall (A B C : Type) 
  (f : B -> C) (g : A -> B) (t : tree A),
  @fmap tree _ _ _ (fun x => f (g x)) t = 
  (fun x => (fmap f (fmap g x))) t.
Proof.
  intros. induction t.
    - reflexivity.
    - simpl. simpl in IHt1, IHt2. rewrite IHt1. rewrite IHt2. reflexivity.
Qed.

(** [] *)

(** Cool fact: only one possible fmap per type! *)

(** Thus, fmap can be derived automatically. Haskell does it for you. *)

(* ================================================================= *)
(** ** Monads (from "Categories for the Working Mathematician" by Sounders Mac Lane) *)

(** "All told, a monad in [X] is just a monoid in the category of endofunctors of X, 
  with product [×] replaced by composition of endofunctors 
  and unit set by the identity endofunctor." *)

(* ================================================================= *)
(** ** Monads (via programming examples) *)

(** One important typeclass (which is heavily used) is 
    the [Monad] typeclass, especially in conjunction with Haskell's
    "[do] notation" for monadic actions.

    Monads are an extremely powerful tool for organizing and
    streamlining code in a wide range of situations where computations
    can be thought of as yielding a result along with some kind of
    "effect."  

   Monads are very useful for modeling things that are not just
   pure functions, that may have some kind of external effect on 
   the world such as reading input or producing output. They're
   essential for modeling statefulness a in pure, stateless,
   functional language like Coq.

    Examples of possible effects include:
       - input / output
       - state mutation
       - failure
       - nondeterminism
       - randomness  *)

(* ================================================================= *)
(** ** Monad for error signaling *)

(** As a first example, consider a simplified expression type
   and let's implement an evaluator for it. *)

Inductive exp := 
| Num : nat -> exp
| Plus : exp -> exp -> exp
| Div : exp -> exp -> exp.

(** First, a [show] function: *)

Fixpoint showExpAux (e : exp) : string :=
  match e with 
    | Num n => show n
    | Plus e1 e2 => 
        "(" ++ (showExpAux e1) ++ "+" ++ (showExpAux e2) ++ ")"
    | Div e1 e2 => 
        "(" ++ (showExpAux e1) ++ "/" ++ (showExpAux e2) ++ ")"
  end.

Instance showExp : Show exp := {
  show := showExpAux
}.

Compute (show (Div (Num 6) (Num 0))).
(* ==> "(6/0)" : string *)

(** Here is a first attempt for an evaluator. *)

Fixpoint eval0 (e:exp) : nat := 
  match e with 
    | Num n => n
    | Plus e1 e2 => eval0 e1 + eval0 e2 
    | Div e1 e2 => eval0 e1 / eval0 e2
  end.


Compute (eval0 (Div (Num 6) (Num 2))).
(* ==> 3 : nat *)

Compute (eval0 (Div (Num 6) (Num 0))).
(* ==> 0 : nat *)

(** Here we assumed that dividing by [0] returns [0].
    
    We can do better.*)

(** Our next version of [eval] will return a value only if
   it does not divide by [0]. 

   Otherwise, it will return an _error message_, reporting an expression 
   evaluating to [0] that we divided by. *)

(** For that matter, we define a [Result] type constructor: *)

Inductive Result (X : Type) : Type :=
  | Error (err : string)
  | Value (x : X).

Arguments Error {X}.
Arguments Value {X}.

(** The evaluation returning [Result nat] is implemented as follows: *)

Fixpoint eval1 (e:exp) : Result nat := 
  match e with 
   | Num n => Value n
   | Plus e1 e2 => 
        match eval1 e1 with
          | Error err1 => Error err1
          | Value n1 => 
              match eval1 e2 with
                | Error err2 => Error err2 
                | Value n2  => Value (n1 + n2)
              end
        end
   | Div e1 e2 => 
        match eval1 e1 with
          | Error err1 => Error err1
          | Value n1 => 
              match eval1 e2 with
                | Error err2 => Error err2 
                | Value n2  => match n2 with 
                                 | 0 => Error ("DBZ: " ++ show e2)
                                 | _ => Value (n1 / n2)
                               end
              end
        end
 end.

(** This works: *) 

Compute (eval1 (Div (Num 6) (Num 2))).
(* ==>  Value 3 : Result nat *)

Compute (eval1 (Div (Num 6) (Num 0))).
(* ==>  Error "DBZ: 0" : Result nat *)

Compute (eval1 (Div (Num 6) (Plus (Num 0) (Num (0))))).
(* ==>  Error "DBZ: (0+0)" : Result nat *)

Compute (eval1 (Plus (Div (Num 6) (Num 0)) 
                     (Div (Num 6) (Plus (Num 0) (Num (0)))))).
(* ==>  Error "DBZ: 0" : Result nat *)

Compute (eval1 (Div (Div (Num 6) (Plus (Num 0) (Num (0)))) (Num 0))).
(* ==>  Error "DBZ: (0+0)" : Result nat *)

(** The bad news: the code is super duper gross! *)

(** A lot of the computation logic is duplicated. 
    (Imagine more operations / larger arity.) *)


(** We have these cascading blocks:

match eval e with
  | Error err1 => Error err1
  | Value n1 => match eval e2 with
                  | Error err2 => Error err2 
                  | Value n2  => ...
                 end
*)

(** But these blocks have a common pattern:

- First do [eval e] and get result [res]
- If [res] is an [Error], just return that error
- If [res] is a [Value v] then do further processing on [v] *)

(** Let's bottle the common structure in a function! *)

(** Such a function is usually called [bind] and denoted by [>>=] *)

Definition bind_result {A B : Type} (r : Result A) 
  (process : A -> Result B) : Result B :=
  match r with
  | Error err => Error err
  | Value v => process v
  end.

Notation "r >>= process" := (bind_result r process)
                     (at level 60, right associativity).

(** [>>=] takes two inputs:

  - [r] of type [Result A]: result of the first evaluation
  - [process] of type [A -> Result B]: in case the first evaluation produced a value, 
    what to do next with that value
*)

(** The magic bottle lets us clean up our evaluator: *)

Fixpoint eval2 (e:exp) : Result nat := 
  match e with 
    | Num n => Value n
    | Plus e1 e2 => eval2 e1 >>= fun n1 =>
                    eval2 e2 >>= fun n2 =>
                    Value (n1 + n2)
    | Div e1 e2  => eval2 e1 >>= fun n1 =>
                    eval2 e2 >>= fun n2 =>
                    match n2 with 
                      | 0 => Error ("DBZ: " ++ show e2)
                      | _ => Value (n1 / n2)
                    end
end.

(** The gross pattern matching is all hidden inside >>= *)

(* ================================================================= *)
(** ** The Monad Typeclass *)

(** Like [show] or [eqb], the [>>=] operator 
    turns out to be useful across many types (not just [Result]). *)

(** Let's create a typeclass for it! *)

Class Monad (M : Type -> Type) := 
{
  bind : forall {A B : Type}, M A -> (A -> M B) -> M B ;
  ret : forall {A : Type}, A -> M A
}.

(** Note:

- It's not a type that is a monad, but rather a type constructor 
  (i.e., a function from types to types), like [Result]. 

- Monads have two operations: bind and return. 

- Return tells you how to wrap a value in the monad. 
*)

(** For [Result], we already saw [bind]:

Definition bind_result {A B : Type} (r :Result A) 
  (process : A -> Result B) : Result B :=
  match r with
  | Error err => Error err
  | Value v => process v
  end.
*)


(** What about [ret] ? *)

(**

Definition ret {A : Type} (a : A) : Result A := ???
*)

Instance monResult : Monad Result := 
{
  bind := fun {A B : Type} (x : Result A) (f : A -> Result B) =>
            match x with 
              | Error err => Error err
              | Value y => f y
            end ;
  ret := fun {A : Type} (x : A) => Value x
}.

(** In fact, [>>=] is so useful there is special syntax for it. *)

(** It’s called the "do notation". *)

Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2)) 
               (right associativity, at level 84, c1 at next level).

Notation "c1 ;; c2" := (bind c1 (fun _ => c2)) 
               (at level 100, right associativity).



(**
Instead of writing

   e1 >>= fun v1 =>
   e2 >>= fun v2 =>
   e3 >>= fun v3 =>
   e

we can write

   v1 <- e1 ;;
   v2 <- e2 ;;
   v3 <- e3 ;;
   e
*)

(** We can further simplify our evaluator to: *)

Fixpoint eval (e:exp) : Result nat := 
  match e with 
    | Num n => ret n
    | Plus e1 e2 => n1 <- eval e1 ;;
                    n2 <- eval e2 ;;
                    ret (n1 + n2)
    | Div e1 e2  => n1 <- eval e1 ;;
                    n2 <- eval e2 ;;
                    match n2 with 
                      | 0 => Error ("DBZ: " ++ show e2)
                      | _ => ret (n1 + n2)
                    end
end.

(** This looks like imperative programming :) *)

(** We can also catch errors, and return [0]: *)

Definition eval_to_zero (e : exp) := 
  let r := (eval e) in
    match r with 
      | Error s => ret 0
      | _ => r
    end.


Compute (eval_to_zero (Div (Num 6) (Plus (Num 0) (Num (0))))).
(* ==>  Value 0 : Result nat *)

(* ================================================================= *)
(** ** Monad for Mutable State *)

(** We used a monad for error signaling. *)

(** The next example considers mutable state, 
    which _seems_ very different. *)



(** Consider implementing expressions with a counter: *)

Inductive exp_c := 
| Num_c : nat -> exp_c
| Plus_c : exp_c -> exp_c -> exp_c
| Inc.

(** Behavior we want: 

- [eval] is given the initial counter value
- every time we evaluate [Inc] (within the call to [eval]), 
  the value of the counter increases
*)


(** For example: *)

(**

eval Inc 0                       -->  0

eval (Plus Inc Inc) 0            -->  1

eval (Plus Inc (Plus Inc Inc)) 0 -->  3
*)

(* ================================================================= *)
(** ** How should we implement [eval]? *)


Definition Cnt := nat.

(**

Fixpoint eval (e:exp_c) (cnt:Cnt) : ?? := 
  match e with 
    | Num_c n => ??
    | Plus_c e1 e2 => ??
    | Inc => ??
  end.
*)

(* ================================================================= *)
(** ** Evaluating Expressions with Counter *)

(** We need to increment the counter every time we do eval [Inc]. *)

(** So [eval] needs to return the new counter. *)

Fixpoint eval_c0 (e:exp_c) (cnt:Cnt) : Cnt * nat := 
  match e with 
    | Num_c n => (cnt, n)
    | Plus_c e1 e2 => 
          let (cnt1, v1) := eval_c0 e1 cnt  in
          let (cnt2, v2) := eval_c0 e2 cnt1 in
          (cnt2, v1 + v2)
    | Inc => (S cnt, cnt)
  end.

Definition topEval_c0 e := snd (eval_c0 e 0).

(** The good news: we get the right result: *)

Compute (topEval_c0 (Plus_c Inc Inc)).
(* ==>  Value 1 : Result nat *)

Compute (topEval_c0 (Plus_c Inc (Plus_c Inc Inc))).
(* ==>  Value 3 : Result nat *)



(** The bad news: the code is super duper gross: 

- The Plus case has to “thread” the counter through the recursive calls.

- Easy to make a mistake, e.g. pass [cnt] instead of [cnt1] into the second [eval]!

- The logic of addition is obscured by all the counter-passing

- So unfair, since [Plus] doesn't even care about the counter!
*)

(** Is it too much to ask that [eval] looks like this?

Fixpoint eval (e:exp) (cnt:Cnt) : Cnt * nat := 
  match e with 
    | Num n => ret n
    | Plus e1 e2 => n1 <- eval e1 ;;
                    n2 <- eval e2 ;;
                    ret (n1 + n2)
    ...
  end.
*)



(**
- Cases that don't care about the counter ([Num], [Plus]), don't even have to mention it!
- The counter is somehow threaded through automatically behind the scenes
- Looks just like in the error handing evaluator.
*)

(* ================================================================= *)
(** ** Lets Spot a Pattern *)

(**

    | Plus_c e1 e2 => let (cnt1, v1) := eval e1 cnt  in 
                      let (cnt2, v2) := eval e2 cnt1 in
                        (cnt2, v1 + v2)

This block has a standard common pattern:

- Perform first step [eval e1] using initial counter [cnt]
- Get a result [(cnt1, v1)]
- Do further processing on [v1] using the new counter [cnt1]

*)

(**

   let (cnt', v) := step cnt 
   in process v cnt' 
*)

(**

   let (cnt', v) := step cnt 
   in process v cnt' 

Can we bottle this common pattern as a [>>=] ?

>>= step process cnt = let (cnt', v) = step cnt
                         in process v cnt'
*)

(** But what is the type of this [>>=] ? 
*)

Definition bind_counter {A B : Type} 
 (step : Cnt -> Cnt * A) (process : A -> Cnt -> Cnt * B)
 (cnt : Cnt) : Cnt * B :=
 let (cnt', v) := step cnt
 in process v cnt'.

(**

bind_counter : (Cnt -> Cnt * A) 
               -> (A -> Cnt -> Cnt * B) 
               -> Cnt 
               -> Cnt * B
*)

(**
Wait, but this type signature looks nothing like the Monad’s bind!

Class Monad (M : Type -> Type) := 
{
  bind : forall {A B : Type}, M A -> (A -> M B) -> M B ;
  ret  : forall {A : Type}, A -> M A
}.

... or does it??? *)

(** Our type constructor [M]: *)

Definition Counting (X : Type) : Type := Cnt -> Cnt * X.

(**

bind_counter : (Cnt -> Cnt * A) 
               -> (A -> Cnt -> Cnt * B) 
               -> Cnt 
               -> Cnt * B

bind_counter : Counting A 
               -> (A -> Counting B) 
               -> Counting B
*)

(**
Indeed: *)

Check (@bind_counter nat nat) : 
               Counting nat 
               -> (nat -> Counting nat) 
               -> Counting nat.

(* ================================================================= *)
(** **   Cleaned-up Evaluator for Expressions with Counter *)

Instance monCounting : Monad Counting := 
{
  ret := fun {A:Type} (x:A) => fun cnt => (cnt, x) ; 
  bind := fun {A B:Type} (x: Counting A) (f:A -> Counting B) =>
            fun cnt => let (cnt1,v1) := (x cnt) in (f v1) cnt1
}.

Fixpoint eval_c (e:exp_c) : Counting nat := 
  match e with 
    | Num_c n      => ret n
    | Plus_c e1 e2 => n1 <- eval_c e1 ;;
                      n2 <- eval_c e2 ;;
                      ret (n1 + n2)
    | Inc       => fun cnt => (S cnt, cnt)
end.

(** Hooray! We rid the poor [Num] and [Plus] from the pesky counters!
The Inc case deals with counters
*)

Definition topEval_c e := snd (eval_c e 0).

(** We get the right results: *)

Compute (topEval_c (Plus_c Inc Inc)).
(* ==>  1 : nat *)

Compute (topEval_c (Plus_c Inc (Plus_c Inc Inc))).
(* ==>  3 : nat *)

(** It is possible to go a step forward and hide the representation
of Counting: *)

Definition get : Counting Cnt := fun cnt => (cnt,cnt).
(* Computation whose return value is the current counter value *)

Definition put (newCnt : Cnt) : Counting unit := fun cnt => (newCnt,tt).
(* Computation that updates the counter value to [newCnt] *)

Fixpoint eval'_c (e:exp_c) : Counting nat := 
  match e with 
    | Num_c n => ret n
    | Plus_c e1 e2 => n1 <- eval'_c e1 ;;
                      n2 <- eval'_c e2 ;;
                      ret (n1 + n2)
    | Inc => cnt <- get ;;
                _ <- put (cnt + 1) ;;
                ret (cnt)
  end. 

(* ================================================================= *)
(** **   The State Monad  *)

(**

Threading state (like a counter) is a common task!
*)

(**

Haskell standard library provides the "State monad" for it.

Let's see how it works in another example 
*)

(** We consider expressions equipped with an imperative
    update: *)

Definition var := string.
Definition state := var -> nat.

Definition update_state (s : state) (x : var) (n : nat) : state :=
  fun x' => if String.eqb x x' then n else s x'.

Notation "'_' '!->' n" := (fun _ => n)
  (at level 100, right associativity).

Notation "x '!->' n ';' s" := (update_state s x n)
                              (at level 100, n at next level, right associativity).

Inductive exp_v : Type := 
| Var_v : var -> exp_v
| Plus_v : exp_v -> exp_v -> exp_v
| Times_v : exp_v -> exp_v -> exp_v
| Store_v : var -> exp_v -> exp_v
| Seq_v : exp_v -> exp_v -> exp_v
| If0_v : exp_v -> exp_v -> exp_v -> exp_v.

(** An evaluator can be written that passes the state
    through everywhere, but it's tedious and error-prone: *)

Fixpoint eval_v0 (e : exp_v) (s : state) : (state * nat) := 
  match e with 
    | Var_v x => (s, s x)
    | Plus_v e1 e2 => 
      let (s1, n1) := eval_v0 e1 s in
      let (s2, n2) := eval_v0 e2 s1 in 
      (s2, n1+n2)
    | Times_v e1 e2 =>
      let (s1, n1) := eval_v0 e1 s in
      let (s2, n2) := eval_v0 e2 s1 in 
      (s2, n1*n2)
    | Store_v x e => 
      let (s1, n1) := eval_v0 e s in 
      (x !-> n1 ; s, n1)
    | Seq_v e1 e2 => 
      let (s1, n1) := eval_v0 e1 s in
      eval_v0 e2 s1
    | If0_v e1 e2 e3 => 
      let (s1, n1) := eval_v0 e1 s in 
      match n1 with 
        | 0 => eval_v0 e2 s1
        | _ => eval_v0 e3 s1
      end
  end.

Compute snd (eval_v0 
         (Var_v "y") 
         ("x" !-> 5 ; "y" !-> 7 ; _ !-> 0)).
(* ==>  7 : nat *)

Compute snd (eval_v0 
         (Seq_v (Store_v "x" (Plus_v (Var_v "x") (Var_v "y"))) 
                (Var_v "x"))
         ("x" !-> 5 ; "y" !-> 7 ; _ !-> 0)).
(* ==>  12 : nat *)

(** Let's use the state monad: *)

Definition StateComp (S : Type) (A : Type) := S -> (S * A).

Instance monState (S : Type) : Monad (StateComp S) := {
  ret := fun {A:Type} (x:A) => fun (s : S) => (s,x) ; 
  bind := fun {A B:Type} (c : StateComp S A) (f: A -> StateComp S B) => 
            fun (s : S) => 
              let (s',v) := c s in 
              f v s'
}.

(** BTW, we can now define:

Definition Counting (A : Type) := StateComp Cnt A.

and the [eval] above will just work out of the box!
*)

(** Helpers: *) 

Definition read (x:var) : StateComp state nat := 
  fun s => (s, s x).
(* Computation whose return value is the current value of [x] *)

Definition write (x:var) (n:nat) : StateComp state nat := 
  fun s => (x !-> n ; s, n).
(* Computation that updates [x] value to [n] and returns [n] *)

(** The evaluator looks much cleaner with the state monad,
    using the functions [read] and [write] to capture interaction
    with the state. *)

Fixpoint eval_v (e : exp_v) : StateComp state nat := 
  match e with 
    | Var_v x => read x
    | Plus_v e1 e2 => 
      n1 <- eval_v e1 ;; 
      n2 <- eval_v e2 ;; 
      ret (n1 + n2)
    | Times_v e1 e2 =>
      n1 <- eval_v e1 ;; 
      n2 <- eval_v e2 ;; 
      ret (n1 * n2)
    | Store_v x e => 
      n <- eval_v e ;; 
      write x n 
    | Seq_v e1 e2 => 
      _ <- eval_v e1 ;; 
      eval_v e2
    | If0_v e1 e2 e3 => 
      n <- eval_v e1 ;;
      match n with 
        | 0 => eval_v e2
        | _ => eval_v e3 
      end
  end.

(* ================================================================= *)
(** **   Using a Monad for Non-deterministic Evaluation *)

(** Our final example is an evaluator that supports non-determinism. *)

Inductive exp_nd : Type := 
| Choose_nd : list nat -> exp_nd
| Plus_nd : exp_nd -> exp_nd -> exp_nd
| Times_nd : exp_nd -> exp_nd -> exp_nd.

(** Behavior we want: 

eval (Choose [1;3])                        -->  [1;3]

eval (Plus (Choose [1;3]) (Choose [0;1;2]) -->  [1;3;2;4;3;5]
*)

(** We need some helpers to define the evaluation *)

(** For addition: *)

Definition add_num_list n l:=
map (fun x => n + x) l.

Compute add_num_list 1 [1;2].
(* ==>  [[2; 3]] : list nat *)

Definition add_list_list l1 l2:=
map (fun x => add_num_list x l1) l2.

Compute add_list_list [0;4] [1;2].
(* ==>  [[[1; 5]; [2; 6]]] : list (list nat) *)

Definition flatten {A:Type} (xs:list (list A)) := 
  fold_right (@app A) nil xs.

Compute (flatten (add_list_list [0;4] [1;2])).
(* ==>  [[1; 5; 2; 6]] : list nat *)

(** For multiplication: *)

Definition mul_num_list n l:=
map (fun x => n * x) l.

Compute mul_num_list 1 [1;2].
(* ==>  [[1; 2]] : list nat *)

Definition mul_list_list l1 l2:=
map (fun x => mul_num_list x l1) l2.

Compute mul_list_list [0;4] [1;2].
(* ==>  [[[0; 4]; [0; 8]]] : list nat *)

Compute (flatten (mul_list_list [0;4] [1;2])).
(* ==>  [[0; 4; 0; 8]] : list nat *)

(** It is simple to generalize our helpers: *)

Definition apply_num_list (f : nat -> nat -> nat) n l:=
map (fun x => f n x) l.

Compute (apply_num_list plus 1 [1;2]).
(* ==>  [[2; 3]] : list nat *)

Compute (apply_num_list mult 1 [1;2]).
(* ==>  [[1; 2]] : list nat *)

Definition apply_list_list f l1 l2:=
map (fun x => apply_num_list f x l1) l2.

Compute apply_list_list plus [0;4] [1;2].
(* ==>  [[[1; 5]; [2; 6]]] : list (list nat) *)

Compute apply_list_list mult [0;4] [1;2].
(* ==>  [[[0; 4]; [0; 8]]] : list (list nat) *)

(** The (ugly) evaluation function for non-determinstic values : *)

Fixpoint eval_nd0 (e:exp_nd) : list nat := 
  match e with 
    | Choose_nd ns => ns
    | Plus_nd e1 e2 => 
      flatten (apply_list_list plus (eval_nd0 e1) (eval_nd0 e2))
    | Times_nd e1 e2 => 
      flatten (apply_list_list mult (eval_nd0 e1) (eval_nd0 e2))
  end.

Compute eval_nd0 (Plus_nd (Choose_nd [1;3]) 
                          (Choose_nd [0;1;2])).
(* ==>  [[1; 3; 2; 4; 3; 5]] : list nat *)

(** We can do better with the "list monad"! *)

Instance monList : Monad list := {
  bind := fun {A B:Type} (c:list A) (f: A -> list B) => 
            flatten (map f c) ;
  ret := fun {A:Type} (x:A) => (x::nil)
}.

Fixpoint eval_nd (e:exp_nd) : list nat := 
  match e with 
    | Choose_nd ns => ns
    | Plus_nd e1 e2 => 
      n1 <- eval_nd e1 ;;
      n2 <- eval_nd e2 ;;
      ret (n1 + n2)
    | Times_nd e1 e2 => 
      n1 <- eval_nd e1 ;;
      n2 <- eval_nd e2 ;;
      ret (n1 * n2)
  end.

Compute eval_nd (Plus_nd (Choose_nd [1;3]) 
                         (Choose_nd [0;1;2])).
(* ==>  [[1; 3; 2; 4; 3; 5]] : list nat *)

(* ================================================================= *)
(** ** Monads in General *)

(**
   If we think of monads as a pattern for encoding effects, such
   as exceptions or state or non-determinism, then we can think 
   of [M A] as describing side-effecting computations that produce
   a value of type A.  

   The [ret] operation takes a pure (effect-free) value of type A
   and injects it into the space of side-effecting computations.

   The [bind] operation sequences two side-effecting computations,
   allowing the latter to depend upon the value of the first one.

*)

(** 

So it is not that pure languages lack imperative features,
but rather the other languages that lack the
ability to have a statically distinguishable pure
subset...

*)

(* ================================================================= *)
(** ** Algebraic Properties *)

(**

Class Monad (M : Type -> Type) := 
{
  bind : forall {A B : Type}, M A -> (A -> M B) -> M B ;
  ret : forall {A : Type}, A -> M A
}.
*)

(** Monads must obey these laws: 
- [ret x >>= f] is equivalent to [f x]
Doing the trivial effect then doing a computation [f] is the same as
just doing the computation [f]
(return is left identity of bind)

- [m >>= return] is equivalent to [m]
Doing only a trivial effect is the same as not doing any effect
(return is right identity of bind)

- [(m >>= f) >>= g] is equivalent to [m >>= (fun x => f x >>= g)]
Doing [f] then doing [g] as two separate computations is the same as
doing a single computation which is [f] followed by [g]
(bind is associative)

*)

(**
Why? The laws make sequencing of effects work the way you expect.
*)

(* ================================================================= *)
(** ** Example: The Counting Monad *)

Lemma m_left_id_Counting : 
  forall {A B : Type} (x:A) (f : A -> Counting B) (cnt : nat), 
  bind (ret x) f cnt = f x cnt.
Proof.
intros A B x f cnt.
unfold bind. reflexivity.
Qed.

Lemma m_right_id_Counting : 
  forall {A:Type} (c : Counting A) (cnt : nat),
  bind c ret cnt = c cnt.
Proof.
intros A c cnt.
simpl.
destruct (c cnt).
reflexivity.
Qed.

Lemma m_assoc_Counting : 
  forall {A B C :Type} (c:Counting A) 
  (f : A -> Counting B) (g : B -> Counting C) (cnt : nat),
    bind (bind c f) g cnt = bind c (fun x => bind (f x) g) cnt.
Proof.
intros A B C c f g cnt.
simpl.
destruct (c cnt).
reflexivity.
Qed.

(* ================================================================= *)
(** ** Example: The List Monad *)

(** **** Exercise: 3 stars, standard (list_monad_properties)

    State and prove the required properties for the list monad instance. *) 

Lemma m_left_id_list : 
  forall {A B : Type} (x:A) (f : A -> list B), 
    bind (ret x) f = f x.
Proof.
  intros. simpl. apply app_nil_r.
Qed.

Lemma m_right_id_list : 
  forall {A:Type} (l : list A), bind l ret = l.
Proof.
  intros. induction l as [|h t IH].
  -reflexivity.
  -simpl. simpl in IH. rewrite IH. reflexivity.
Qed.

(* FILL IN HERE *)

Lemma map_app : forall {A B : Type} (l1 l2 : list A) (f : A -> B),
  map f (l1 ++ l2) = app (map f l1) (map f l2).
Proof. intros A B l1. induction l1 as [|h1 t1 IH].
    -reflexivity.
    -intros. simpl. rewrite IH. reflexivity.
Qed.

Lemma flatten_app : forall {A: Type} (l1 l2 : list (list A)), 
  flatten (l1 ++ l2) = app (flatten l1) (flatten l2).
Proof. intros A  l1. induction l1 as [|h1 t1 IH].
    - reflexivity.
    -intros. simpl. rewrite IH. rewrite app_assoc. reflexivity.
Qed.

Lemma m_assoc_list : 
  forall {A B C :Type} (l:list A) 
    (f : A -> list B) (g : B -> list C),
    bind (bind l f) g = bind l (fun x => bind (f x) g).
Proof.
  intros. induction l as [|h t IH].
  -reflexivity.
  -simpl. simpl in IH. rewrite <- IH. rewrite map_app. rewrite flatten_app. reflexivity.
Qed.

(** [] *)

(* ================================================================= *)
(** ** Monads are Amazing *)

(** This code stays the same:

Fixpoint eval (e:exp) : Interpreter nat := 
  match e with 
    | Plus e1 e2 => 
      n1 <- eval e1 ;;
      n2 <- eval e2 ;;
      ret (n1 + n2)
    | Times e1 e2 => 
      n1 <- eval e1 ;;
      n2 <- eval e2 ;;
      ret (n1 * n2)
   ...
  end.
*)

(**
We change the type [Interpreter] to implement different effects:

- [Interpreter A = Result A]  if we want to handle errors
- [Interpreter A = State nat A] if we want to have a counter
- [Interpreter A = State (total_map nat) A] if we want to have assignments
- [Interpreter A = Result (State (total_map nat) A)] if we want both errors and assignments
- [Interpreter A = List A] if we want to return multiple results
*)

(**
Monads let us decouple two things:

- Application logic: the sequence of actions (implemented in [eval])
- Effects: how actions are sequenced (implemented in [>>=])
*)

(* ================================================================= *)
(** ** Monads are Influential *)

(** Monads have had a revolutionary influence in PL.

    Especially in Haskell (a pure functional language), but also well beyond.

    Some recent examples:

- Error handling in go

https://speakerdeck.com/rebeccaskinner/monadic-error-handling-in-go

https://www.innoq.com/en/blog/golang-errors-monads/

- Asynchrony in JavaScript

https://gist.github.com/MaiaVictor/bc0c02b6d1fbc7e3dbae838fb1376c80

https://medium.com/@dtipson/building-a-better-promise-3dd366f80c16

- Big data pipelines

https://www.microsoft.com/en-us/research/project/dryadlinq/

https://www.tensorflow.org/
*)

(* ================================================================= *)
(** ** Additional Example: The Writer Monad *)

Fixpoint eval_log0 (e:exp) : string * nat := 
  match e with 
   | Num n => ("num(" ++ show n ++ ");",n)
   | Plus e1 e2 => 
        match eval_log0 e1 with
          (s1,n1) => 
              match eval_log0 e2 with
                | (s2,n2)  => 
                   (s1 ++  s2 ++
                   "plus(" ++ show n1 ++ "," ++ show n2 ++ ");",
                   n1 + n2)
              end
        end
   | Div e1 e2 => 
        match eval_log0 e1 with
          (s1,n1) => 
              match eval_log0 e2 with
                | (s2,n2)  => 
                   (s1 ++  s2 ++
                   "div(" ++ show n1 ++ "," ++ show n2 ++ ");",
                   n1 + n2)
              end
        end
 end.

Compute (eval_log0 (Div (Num 6) (Num 2))).
(* ==> ("num(6);num(2);div(6,2);", 3) : string * nat *)

Compute (eval_log0 (Div (Num 6) (Plus (Num 0) (Num 7)))).
(* ==> ("num(6);num(0);num(7);plus(0,7);div(6,7);", 0) : string * nat *)

(** Using a "Log Monad" *)

Definition LogString (X : Type) : Type := string * X.

Instance monLogString : Monad LogString := 
{
  bind := fun {A B : Type} (x : LogString A) (f : A -> LogString B) =>
              let (s ,a) := x in 
              let (s',b) := f a in
              (s ++ s',b) ;
  ret := fun {A:Type} (x:A) => ("",x)
}.

Definition tell {X : Type} (x : X) := (x, tt).

Fixpoint eval_log (e:exp) : LogString nat := 
  match e with 
    | Num n      => 
        _  <- tell ("num(" ++ show n ++ ");") ;;
        ret n
    | Plus e1 e2 => 
        n1 <- eval_log e1 ;;
        n2 <- eval_log e2 ;;
        _  <- tell ("plus(" ++ show n1 ++ "," ++ show n2 ++ ");") ;;
        ret (n1 + n2)
    | Div e1 e2  => 
        n1 <- eval_log e1 ;;
        n2 <- eval_log e2 ;;
        _  <- tell ("div(" ++ show n1 ++ "," ++ show n2 ++ ");") ;;
        ret (n1 / n2)
  end.

Compute (eval_log (Div (Num 6) (Num 2))).
(* ==> ("num(6);num(2);div(6,2);", 3) : LogString nat *)

Compute (eval_log (Div (Num 6) (Plus (Num 0) (Num 7)))).
(* ==> ("num(6);num(0);num(7);plus(0,7);div(6,7);", 0) : LogString nat *)

(** Similar example: *)

Fixpoint eval_cnt0 (e:exp) : nat * nat := 
  match e with 
   | Num n => (1,n)
   | Plus e1 e2 => 
        match eval_cnt0 e1 with
          (s1,n1) => 
              match eval_cnt0 e2 with
                | (s2,n2)  => (s1 + s2 + 1, n1 + n2)
              end
        end
   | Div e1 e2 => 
        match eval_cnt0 e1 with
          (s1,n1) => 
              match eval_cnt0 e2 with
                | (s2,n2)  => (s1 + s2 + 1, n1 / n2)
              end
        end
 end.

Compute (eval_cnt0 (Div (Num 6) (Plus (Num 0) (Num 7)))).
(* ==> (5, 0) : nat * nat *)

(** Using a monad: *)

Definition LogNat (X : Type) : Type := nat * X.

Instance monLogNat : Monad LogNat := 
{
  bind := fun {A B : Type} (x : LogNat A) (f : A -> LogNat B) =>
              let (s ,a) := x in 
              let (s',b) := f a in
              (s + s',b) ;
  ret := fun {A:Type} (x:A) => (0,x)
}.

Fixpoint eval_cnt (e:exp) : LogNat nat := 
  match e with 
    | Num n      => _  <- tell 1 ;;
                    ret n
    | Plus e1 e2 => n1 <- eval_cnt e1 ;;
                    n2 <- eval_cnt e2 ;;
                    _  <- tell 1 ;;
                    ret (n1 + n2)
    | Div e1 e2  => n1 <- eval_cnt e1 ;;
                    n2 <- eval_cnt e2 ;;
                    _  <- tell 1 ;;
                    ret (n1 / n2)
  end.

Compute (eval_cnt (Div (Num 6) (Plus (Num 0) (Num 7)))).
(* ==> (5, 0) : LogNat nat *)

(** Let's generalize... *)

Class SemiGroup (A : Type) := {
  dot : A -> A -> A;
(*   assoc_dot : forall a b c : A, dot a (dot b c) = dot (dot a b) c *)
}.

Class Monoid (A : Type) {H : SemiGroup A} := {
  id : A ;
(*   proof_id : forall a : A, dot a id = a *)
}.

Definition Writer (T : Type) {_ : SemiGroup T} {_: Monoid T}
                  (X : Type) : Type := T * X.

Instance monWriter (T : Type) (_ : SemiGroup T) (_: Monoid T): 
         Monad (Writer T) := 
{
  bind := fun {A B : Type} (x : Writer T A) (f : A -> Writer T B) =>
              let (s ,a) := x in 
              let (s',b) := f a in
              (dot s s',b) ;
  ret := fun {A:Type} (x:A) => (id,x)
}.

Instance stringSemiGroup : SemiGroup string := 
{
  dot := append
}.

Instance stringMonoid : Monoid string := 
{
  id := ""
}.

Fixpoint eval_log' (e:exp) : Writer string nat := 
  match e with 
    | Num n      => 
        _  <- tell ("num(" ++ show n ++ ");") ;;
        ret n
    | Plus e1 e2 => 
        n1 <- eval_log' e1 ;;
        n2 <- eval_log' e2 ;;
        _  <- tell ("plus(" ++ show n1 ++ "," ++ show n2 ++ ");") ;;
        ret (n1 + n2)
    | Div e1 e2  => 
        n1 <- eval_log' e1 ;;
        n2 <- eval_log' e2 ;;
        _  <- tell ("div(" ++ show n1 ++ "," ++ show n2 ++ ");") ;;
        ret (n1 / n2)

  end.

Compute (eval_log' (Div (Num 6) (Plus (Num 0) (Num 7)))).
(* ==> ("num(6);num(0);num(7);plus(0,7);div(6,7);", 0)  : Writer string nat *)

Instance natSemiGroup : SemiGroup nat := 
{
  dot := plus
}.

Instance natMonoid : Monoid nat := 
{
  id := 0
}.

Fixpoint eval_cnt' (e:exp) : Writer nat nat := 
  match e with 
    | Num n      => _  <- tell 1 ;;
                    ret n
    | Plus e1 e2 => n1 <- eval_cnt' e1 ;;
                    n2 <- eval_cnt' e2 ;;
                    _  <- tell 1 ;;
                    ret (n1 + n2)
    | Div e1 e2  => n1 <- eval_cnt' e1 ;;
                    n2 <- eval_cnt' e2 ;;
                    _  <- tell 1 ;;
                    ret (n1 / n2)
  end.

Compute (eval_cnt' (Div (Num 6) (Plus (Num 0) (Num 7)))).
(* ==> (5, 0) : Writer nat nat *)

End Monads.

(* 2022-11-13 16:26 *)
