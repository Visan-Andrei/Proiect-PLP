Require Import Strings.String.
Local Open Scope string_scope.
Scheme Equality for string.
Require Import Arith.
Require Import Ascii.

(*Inductive string : Set :=
  | EmptyString : string
  | String : ascii -> string -> string.*)

Delimit Scope string_scope with string.
Local Open Scope string_scope.


(* Environment *)

Definition Env := string -> nat.
Definition env1 : Env :=
  fun x =>
    if (string_eq_dec x "n")
    then 10
    else 0.
Check env1.

Compute (env1 "coq").
Definition update (env : Env)
           (x : string) (v : nat) : Env :=
  fun y =>
    if (string_eq_dec y x)
    then v
    else (env y).

Definition Env2 := string -> string.
Definition env2 : Env2 :=
  fun x =>
    if (string_eq_dec x "n")
    then ""
    else "".
Check env2.

Definition update2 (env : Env2)
           (x : string) (v : string) : Env2 :=
  fun y =>
    if (string_eq_dec y x)
    then v
    else (env y).

Inductive value :=
| undef : value
| nat_val : nat -> value
| string_val : string -> value.

Scheme Equality for value.

Open Scope char_scope.

Definition charToNat (c : ascii) : nat :=
  match c with
    | "0" => 0
    | "1" => 1
    | "2" => 2
    | "3" => 3
    | "4" => 4
    | "5" => 5
    | "6" => 6
    | "7" => 7
    | "8" => 8
    | "9" => 9
    | _ => 0
  end.

Open Scope string_scope.

Fixpoint read (s : string) (num : nat) : nat :=
  match s with
    | "" => num
    | String c s' =>
      match charToNat c with
        | n => read s' (10*num+n)
      end
  end.

Definition readNat (s : string) : nat :=
  read s 0.

Definition natToChar (n : nat) : ascii :=
  match n with
    | 0 => "0"
    | 1 => "1"
    | 2 => "2"
    | 3 => "3"
    | 4 => "4"
    | 5 => "5"
    | 6 => "6"
    | 7 => "7"
    | 8 => "8"
    | _ => "9"
  end.

Fixpoint write (check n : nat) (s : string) : string :=
  let s' := String (natToChar (Nat.modulo n 10)) s in
  match check with
    | 0 => s'
    | S check' =>
      match (Nat.div n 10) with
        | 0 => s'
        | n' => write check' n' s'
      end
  end.

Definition writeNat (n : nat) : string :=
  write n n "".

Notation "atoi( X )" := (readNat X) (at level 94).
Notation "itoa( X )" := (writeNat X) (at level 94).
Compute atoi("32").
Compute itoa(121).


Notation "S [ V /' X ]" := (update S X V) (at level 0).


Inductive AExp :=
| avar : string -> AExp
| anum : nat -> AExp
| aplus : AExp -> AExp -> AExp
| amin : AExp -> AExp -> AExp 
| adiv : AExp -> AExp -> AExp 
| amod : AExp -> AExp -> AExp 
| amul : AExp -> AExp -> AExp
| apow : AExp -> AExp.

Notation "A +' B" := (aplus A B) (at level 48).
Notation "A -' B" := (amin A B) (at level 48).  
Notation "A /' B" := (adiv A B) (at level 46).  
Notation "A %' B" := (amod A B) (at level 46).  
Notation "pow( A )" := (apow A) (at level 60).
Notation "A *' B" := (amul A B) (at level 46).
Coercion anum : nat >-> AExp.
Coercion avar : string >-> AExp.
Check (3 +' 3 *' 4).
Check (6 +' 2 *' "n").
Check (21 -' "n"). 
Check (21 /' 3). 
Check (21 %' 3). 
Check (pow(3)).
Compute(3 +' 3).
Compute (pow(3)).

Fixpoint divmod x y q u :=
  match x with
    | 0 => (q,u)
    | S x' => match u with
                | 0 => divmod x' y (S q) y
                | S u' => divmod x' y q u'
              end
  end.

Definition div x y :=
  match y with
    | 0 => y
    | S y' => fst (divmod x y' 0 y')
  end.

Definition modulo x y :=
  match y with
    | 0 => y
    | S y' => y' - snd (divmod x y' 0 y')
  end.

Infix "/" := div : nat_scope.
Infix "mod" := modulo (at level 40, no associativity) : nat_scope.

Fixpoint aeval_fun (a : AExp) (env : Env) : nat :=
  match a with
  | avar k => env k
  | anum v => v
  | aplus a1 a2 => (aeval_fun a1 env) + (aeval_fun a2 env)
  | amul a1 a2 => (aeval_fun a1 env) * (aeval_fun a2 env)
  | amin a1 a2 => (aeval_fun a1 env) - (aeval_fun a2 env)
  | adiv a1 a2 => (aeval_fun a1 env) / (aeval_fun a2 env)
  | amod a1 a2 => (aeval_fun a1 env) mod (aeval_fun a2 env)
  | apow a1 => (aeval_fun a1 env) * (aeval_fun a1 env)
  end.

Compute aeval_fun (2 *' 3 *' 5) env1.
Compute aeval_fun (2 +' 3 *' "n") env1.
Compute aeval_fun(pow(3)).

Reserved Notation "A =[ S ]=> N" (at level 60).

Inductive aeval : AExp -> Env -> nat -> Prop :=
| const : forall n sigma, anum n =[ sigma ]=> n 
| var : forall v sigma, avar v =[ sigma ]=> (sigma v) 
| add : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = i1 + i2 ->
    a1 +' a2 =[sigma]=> n
| sub : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = i1 - i2 ->
    a1 -' a2 =[sigma]=> n
| times : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = i1 * i2 ->
    a1 *' a2 =[sigma]=> n
| divided : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = i1 / i2 ->
    a1 /' a2 =[sigma]=> n
| power : forall a1 i1  sigma n,
    a1 =[ sigma ]=> i1 ->
    n = i1 * i1 ->
    pow(a1) =[sigma]=> n
where "a =[ sigma ]=> n" := (aeval a sigma n).


Inductive BExp :=
| btrue : BExp
| bfalse : BExp
| blessthan : AExp -> AExp -> BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp.

Fixpoint beval_fun (b : BExp) (env : Env) : bool :=
  match b with
  | btrue => true
  | bfalse => false
  | blessthan a1 a2 => Nat.leb (aeval_fun a1 env) (aeval_fun a2 env)
  | bnot b' => negb (beval_fun b' env)
  | band b1 b2 => match (beval_fun b1 env), (beval_fun b2 env) with
                  | true, true => false
                  | true, false => true
                  | false, true => true
                  | false, false => false
                  end
  end.


Notation "A <=' B" := (blessthan A B) (at level 53).
Reserved Notation "B ={ S }=> B'" (at level 70).

Inductive SExp :=
| astring : string -> SExp
| toUpper : SExp -> SExp
| toLower : SExp -> SExp.
Coercion astring : string >-> SExp.
Notation "low( A )" := (toLower A) (at level 61).
Notation "upper( A )" := (toUpper A) (at level 61).
Check (low("A")).
Check (upper("a")).
Compute (low("A")).
Compute (upper("a")).

Reserved Notation "B ={ S }=> B'" (at level 70).
Inductive beval : BExp -> Env -> bool -> Prop :=
| e_true : forall sigma, btrue ={ sigma }=> true
| e_false : forall sigma, bfalse ={ sigma }=> false
| e_lessthan : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = Nat.leb i1 i2 ->
    a1 <=' a2 ={ sigma }=> b
| e_nottrue : forall b sigma,
    b ={ sigma }=> true ->
    (bnot b) ={ sigma }=> false
| e_notfalse : forall b sigma,
    b ={ sigma }=> false ->
    (bnot b) ={ sigma }=> true
| e_andtrue : forall b1 b2 sigma t,
    b1 ={ sigma }=> true ->
    b2 ={ sigma }=> t ->
    band b1 b2 ={ sigma }=> t
| e_andfalse : forall b1 b2 sigma,
    b1 ={ sigma }=> false ->
    band b1 b2 ={ sigma }=> false
where "B ={ S }=> B'" := (beval B S B').

Inductive Stmt :=
| assignment : string -> AExp -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
(*| atoi_asg : string -> string -> Stmt
| itoa_asg : AExp -> string -> Stmt*)
| ifthenelse : BExp -> Stmt -> Stmt -> Stmt
| ifsimple : BExp -> Stmt -> Stmt.

Notation "X ::= A" := (assignment X A) (at level 50).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 90).
Notation " 'pentru' ( S1 )( B )( S2 ){ S3 }" := (S1 ;; while B (S2 ;; S3) ) (at level 92).
(*Notation "X ::= 'atoi'( Y )" := (atoi_asg X Y) (at level 93).
Notation "X ::= 'itoa'( Y )" := (itoa_asg X Y) (at level 93).*)
(*
Reserved Notation "S -{ Sigma }-> Sigma'" (at level 60).
Check update.
Inductive eval : Stmt -> Env -> Env -> Prop :=
| e_assignment: forall a i x sigma sigma',
    a =[ sigma ]=> i ->
    sigma' = (update sigma x i) ->
    (x ::= a) -{ sigma }-> sigma'
| e_seq : forall s1 s2 sigma sigma1 sigma2,
    s1 -{ sigma }-> sigma1 ->
    s2 -{ sigma1 }-> sigma2 ->
    (s1 ;; s2) -{ sigma }-> sigma2
| e_whilefalse : forall b s sigma,
    b ={ sigma }=> false ->
    while b s -{ sigma }-> sigma
| e_whiletrue : forall b s sigma sigma',
    b ={ sigma }=> true ->
    (s ;; while b s) -{ sigma }-> sigma' ->
    while b s -{ sigma }-> sigma'
| e_ifsimpletrue : forall b s sigma sigma',
    b ={ sigma }=> true ->
    s -{ sigma }-> sigma' ->
    ifsimple b s -{ sigma }-> sigma'
| e_ifsimplefalse : forall b s sigma,
    b ={ sigma }=> false ->
    ifsimple b s -{ sigma }-> sigma
| e_ifthenelsetrue : forall b c1 c2 sigma sigma',
    b ={ sigma }=> true ->
    c1 -{ sigma }-> sigma' ->
    ifthenelse b c1 c2 -{ sigma }-> sigma'
| e_ifthenelsefalse : forall b c1 c2 sigma sigma',
    b ={ sigma }=> false ->
    c2 -{ sigma }-> sigma' ->
    ifthenelse b c1 c2 -{ sigma }-> sigma'


where "s -{ sigma }-> sigma'" := (eval s sigma sigma').
*)

Fixpoint eval (s : Stmt) (env : Env) (gas : nat) : Env :=
  match gas with
  | 0 => env
  | S gas' =>   match s with
                | assignment Var aexp => update env Var (aeval_fun aexp env)
                | sequence S1 S2 => eval S2 (eval S1 env gas') gas'
                | while cond s' => if (beval_fun cond env)
                                   then eval (s' ;; (while cond s')) env gas'
                                   else env
                | ifthenelse cond s1 s2 => if (beval_fun cond env)
                                           then (eval s1 env) gas'
                                           else (eval s2 env) gas'
                | ifsimple cond s' => if (beval_fun cond env)
                                      then (eval s' env) gas'
                                      else env 

                end
  end.

Notation "X := A" := (assignment X A) (at level 50).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 90).
Reserved Notation "S -{ Sigma }-> Sigma'" (at level 60).

Compute (assignment  "x" (2 +' 7)).
Compute
  "n" := 10 ;;
  "m" := 7;;
ifthenelse (2 <=' 5)
           ("max" := 9)
           ("max" := 5).
Compute
ifsimple (2 <=' 5)
           ("max" := 9).
Compute
while (2 <=' 5)
           ("max" := 9).
Compute
  "n" := 10 ;;
  "m" := 7;;
pentru("n" := 10)( 3 <='4 )("n" := 3+'1){"max" := 9}.



