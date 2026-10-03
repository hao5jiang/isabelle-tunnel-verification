structure ReceiverGate : sig
  type nat
  val integer_of_nat : nat -> IntInf.int
  type wire_kind
  type train
  type receiver_port
  type 'a tunnel_packet_ext
  val nat_of_integer : IntInf.int -> nat
  val frame_encode_numbers :
    nat -> nat -> nat -> nat -> nat -> (nat list) option
  val receiver_decode_numbers :
    nat -> nat -> nat -> nat list -> (nat * (nat * nat)) option
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

datatype wire_kind = EnterPacket | FencePacket | ClearPacket;

datatype train = A | B;

datatype receiver_port = ControllerPort | DevicePort of train;

datatype 'a tunnel_packet_ext =
  Tunnel_packet_ext of wire_kind * train * nat * 'a;

fun plus_nat m n = Nat (IntInf.+ (integer_of_nat m, integer_of_nat n));

fun suc n = plus_nat n one_nata;

fun list_all p [] = true
  | list_all p (x :: xs) = p x andalso list_all p xs;

fun apsnd f (x, y) = (x, f y);

fun length_tailrec [] n = n
  | length_tailrec (x :: xs) n = length_tailrec xs (suc n);

fun fst (x1, x2) = x1;

fun snd (x1, x2) = x2;

val zero_nat : nat = Nat (0 : IntInf.int);

fun train_tag A = zero_nat
  | train_tag B = one_nata;

fun max A_ a b = (if less_eq A_ a b then b else a);

fun minus_nat m n =
  Nat (max ord_integer (0 : IntInf.int)
        (IntInf.- (integer_of_nat m, integer_of_nat n)));

fun equal_nat m n = (((integer_of_nat m) : IntInf.int) = (integer_of_nat n));

fun power A_ a n =
  (if equal_nat n zero_nat then one (one_power A_)
    else times (times_power A_) a (power A_ a (minus_nat n one_nata)));

fun nat_of_integer k = Nat (max ord_integer (0 : IntInf.int) k);

fun packet_tag EnterPacket = one_nata
  | packet_tag FencePacket = nat_of_integer (2 : IntInf.int)
  | packet_tag ClearPacket = nat_of_integer (3 : IntInf.int);

fun map_option f NONE = NONE
  | map_option f (SOME x2) = SOME (f x2);

fun packet_train
  (Tunnel_packet_ext (packet_kind, packet_train, packet_epoch, more)) =
  packet_train;

fun packet_epoch
  (Tunnel_packet_ext (packet_kind, packet_train, packet_epoch, more)) =
  packet_epoch;

fun packet_kind
  (Tunnel_packet_ext (packet_kind, packet_train, packet_epoch, more)) =
  packet_kind;

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

fun modulo_integer k l = snd (divmod_integer k l);

fun modulo_nat m n = Nat (modulo_integer (integer_of_nat m) (integer_of_nat n));

fun divide_integer k l = fst (divmod_integer k l);

fun divide_nat m n = Nat (divide_integer (integer_of_nat m) (integer_of_nat n));

fun epoch_bytes n k =
  (if equal_nat n zero_nat then []
    else modulo_nat k (nat_of_integer (256 : IntInf.int)) ::
           epoch_bytes (minus_nat n one_nata)
             (divide_nat k (nat_of_integer (256 : IntInf.int))));

fun frame_bytes n p =
  [nat_of_integer (84 : IntInf.int), nat_of_integer (75 : IntInf.int), one_nata,
    packet_tag (packet_kind p), train_tag (packet_train p), n] @
    epoch_bytes n (packet_epoch p);

fun less_nat m n = IntInf.< (integer_of_nat m, integer_of_nat n);

fun epoch_capacity n = power power_nat (nat_of_integer (256 : IntInf.int)) n;

fun frame_config n l =
  less_nat zero_nat n andalso
    (less_nat n (nat_of_integer (256 : IntInf.int)) andalso
      less_nat l (epoch_capacity n));

fun size_list xs = length_tailrec xs zero_nat;

fun less_eq_nat m n = IntInf.<= (integer_of_nat m, integer_of_nat n);

fun epoch_value [] = zero_nat
  | epoch_value (b :: bs) =
    plus_nat b
      (times_nata (nat_of_integer (256 : IntInf.int)) (epoch_value bs));

fun epoch_decode n l bs =
  (if less_nat l (epoch_capacity n) andalso
        (equal_nat (size_list bs) n andalso
          (list_all (fn b => less_nat b (nat_of_integer (256 : IntInf.int)))
             bs andalso
            less_eq_nat (epoch_value bs) l))
    then SOME (epoch_value bs) else NONE);

fun packet_train_of tag =
  (if equal_nat tag zero_nat then SOME A
    else (if equal_nat tag one_nata then SOME B else NONE));

fun packet_kind_of tag =
  (if equal_nat tag one_nata then SOME EnterPacket
    else (if equal_nat tag (nat_of_integer (2 : IntInf.int))
           then SOME FencePacket
           else (if equal_nat tag (nat_of_integer (3 : IntInf.int))
                  then SOME ClearPacket else NONE)));

fun frame_decode n l bs =
  (case bs of [] => NONE | [_] => NONE | [_, _] => NONE | [_, _, _] => NONE
    | [_, _, _, _] => NONE | [_, _, _, _, _] => NONE
    | a :: b :: v :: tag :: who :: width :: payload =>
      (if frame_config n l andalso
            (equal_nat a (nat_of_integer (84 : IntInf.int)) andalso
              (equal_nat b (nat_of_integer (75 : IntInf.int)) andalso
                (equal_nat v one_nata andalso equal_nat width n)))
        then (case packet_kind_of tag of NONE => NONE
               | SOME kind =>
                 (case packet_train_of who of NONE => NONE
                   | SOME i =>
                     (case epoch_decode n l payload of NONE => NONE
                       | SOME k => SOME (Tunnel_packet_ext (kind, i, k, ())))))
        else NONE));

fun frame_encode n l p =
  (if frame_config n l andalso less_eq_nat (packet_epoch p) l
    then SOME (frame_bytes n p) else NONE);

fun equal_train A B = false
  | equal_train B A = false
  | equal_train B B = true
  | equal_train A A = true;

fun equal_receiver_port ControllerPort (DevicePort x2) = false
  | equal_receiver_port (DevicePort x2) ControllerPort = false
  | equal_receiver_port (DevicePort x2) (DevicePort y2) = equal_train x2 y2
  | equal_receiver_port ControllerPort ControllerPort = true;

fun packet_destination p =
  (case packet_kind p of EnterPacket => DevicePort (packet_train p)
    | FencePacket => DevicePort (packet_train p)
    | ClearPacket => ControllerPort);

fun receiver_decode n l r bs =
  (case frame_decode n l bs of NONE => NONE
    | SOME p =>
      (if equal_receiver_port (packet_destination p) r then SOME p else NONE));

fun receiver_port_of tag =
  (if equal_nat tag zero_nat then SOME ControllerPort
    else (if equal_nat tag one_nata then SOME (DevicePort A)
           else (if equal_nat tag (nat_of_integer (2 : IntInf.int))
                  then SOME (DevicePort B) else NONE)));

fun frame_encode_numbers n l tag who k =
  (case packet_kind_of tag of NONE => NONE
    | SOME kind =>
      (case packet_train_of who of NONE => NONE
        | SOME i => frame_encode n l (Tunnel_packet_ext (kind, i, k, ()))));

fun receiver_decode_numbers n l port bs =
  (case receiver_port_of port of NONE => NONE
    | SOME r =>
      map_option
        (fn p =>
          (packet_tag (packet_kind p),
            (train_tag (packet_train p), packet_epoch p)))
        (receiver_decode n l r bs));

end; (*struct ReceiverGate*)
