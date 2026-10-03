structure EpochCodec : sig
  type nat
  type num
  val integer_of_nat : nat -> IntInf.int
  val nat_of_integer : IntInf.int -> nat
  val epoch_decode : nat -> nat -> nat list -> nat option
  val epoch_encode : nat -> nat -> nat -> (nat list) option
  val epoch_checked_successor : nat -> nat -> nat list -> (nat list) option
end = struct

datatype nat = Nat of IntInf.int;

datatype num = One | Bit0 of num | Bit1 of num;

val one_nata : nat = Nat (1 : IntInf.int);

type 'a one = {one : 'a};
val one = #one : 'a one -> 'a;

val one_nat = {one = one_nata} : nat one;

fun integer_of_nat (Nat x) = x;

fun times_nata m n = Nat (IntInf.* (integer_of_nat m, integer_of_nat n));

type 'a times = {times : 'a -> 'a -> 'a};
val times = #times : 'a times -> 'a -> 'a -> 'a;

type 'a power = {one_power : 'a one, times_power : 'a times};
val one_power = #one_power : 'a power -> 'a one;
val times_power = #times_power : 'a power -> 'a times;

val times_nat = {times = times_nata} : nat times;

val power_nat = {one_power = one_nat, times_power = times_nat} : nat power;

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int ord;

fun plus_nat m n = Nat (IntInf.+ (integer_of_nat m, integer_of_nat n));

fun suc n = plus_nat n one_nata;

fun list_all p [] = true
  | list_all p (x :: xs) = p x andalso list_all p xs;

fun apsnd f (x, y) = (x, f y);

fun length_tailrec [] n = n
  | length_tailrec (x :: xs) n = length_tailrec xs (suc n);

fun fst (x1, x2) = x1;

fun snd (x1, x2) = x2;

fun max A_ a b = (if less_eq A_ a b then b else a);

fun minus_nat m n =
  Nat (max ord_integer (0 : IntInf.int)
        (IntInf.- (integer_of_nat m, integer_of_nat n)));

fun equal_nat m n = (((integer_of_nat m) : IntInf.int) = (integer_of_nat n));

val zero_nat : nat = Nat (0 : IntInf.int);

fun power A_ a n =
  (if equal_nat n zero_nat then one (one_power A_)
    else times (times_power A_) a (power A_ a (minus_nat n one_nata)));

fun less_nat m n = IntInf.< (integer_of_nat m, integer_of_nat n);

fun divmod_integer k l =
  (if ((k : IntInf.int) = (0 : IntInf.int))
    then ((0 : IntInf.int), (0 : IntInf.int))
    else (if IntInf.< ((0 : IntInf.int), l)
           then (if IntInf.< ((0 : IntInf.int), k)
                  then IntInf.divMod (IntInf.abs k, IntInf.abs l)
                  else let
                         val (r, s) =
                           IntInf.divMod (IntInf.abs k, IntInf.abs l);
                       in
                         (if ((s : IntInf.int) = (0 : IntInf.int))
                           then (IntInf.~ r, (0 : IntInf.int))
                           else (IntInf.- (IntInf.~ r, (1 : IntInf.int)),
                                  IntInf.- (l, s)))
                       end)
           else (if ((l : IntInf.int) = (0 : IntInf.int))
                  then ((0 : IntInf.int), k)
                  else apsnd IntInf.~
                         (if IntInf.< (k, (0 : IntInf.int))
                           then IntInf.divMod (IntInf.abs k, IntInf.abs l)
                           else let
                                  val (r, s) =
                                    IntInf.divMod (IntInf.abs k, IntInf.abs l);
                                in
                                  (if ((s : IntInf.int) = (0 : IntInf.int))
                                    then (IntInf.~ r, (0 : IntInf.int))
                                    else (IntInf.- (IntInf.~
              r, (1 : IntInf.int)),
   IntInf.- (IntInf.~ l, s)))
                                end))));

fun nat_of_integer k = Nat (max ord_integer (0 : IntInf.int) k);

fun modulo_integer k l = snd (divmod_integer k l);

fun modulo_nat m n = Nat (modulo_integer (integer_of_nat m) (integer_of_nat n));

fun divide_integer k l = fst (divmod_integer k l);

fun divide_nat m n = Nat (divide_integer (integer_of_nat m) (integer_of_nat n));

fun epoch_bytes n k =
  (if equal_nat n zero_nat then []
    else modulo_nat k (nat_of_integer (256 : IntInf.int)) ::
           epoch_bytes (minus_nat n one_nata)
             (divide_nat k (nat_of_integer (256 : IntInf.int))));

fun epoch_value [] = zero_nat
  | epoch_value (b :: bs) =
    plus_nat b
      (times_nata (nat_of_integer (256 : IntInf.int)) (epoch_value bs));

fun less_eq_nat m n = IntInf.<= (integer_of_nat m, integer_of_nat n);

fun epoch_capacity n = power power_nat (nat_of_integer (256 : IntInf.int)) n;

fun size_list xs = length_tailrec xs zero_nat;

fun epoch_decode n l bs =
  (if less_nat l (epoch_capacity n) andalso
        (equal_nat (size_list bs) n andalso
          (list_all (fn b => less_nat b (nat_of_integer (256 : IntInf.int)))
             bs andalso
            less_eq_nat (epoch_value bs) l))
    then SOME (epoch_value bs) else NONE);

fun epoch_encode n l k =
  (if less_nat l (epoch_capacity n) andalso less_eq_nat k l
    then SOME (epoch_bytes n k) else NONE);

fun epoch_checked_successor n l bs =
  (case epoch_decode n l bs of NONE => NONE
    | SOME k => (if less_nat k l then epoch_encode n l (suc k) else NONE));

end; (*struct EpochCodec*)
