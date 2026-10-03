(* Independently tested text wrapper, not a formally verified network service.
   The receiver port is supplied by the local caller, not the packet header.
   There is no unbound D command.
   E n L kind train epoch / R n L receiver frame-byte... / V
   Replies: B bytes, P kind train epoch, N (core rejection), X (wrapper rejection).
   RECEIVER_GATE_CORE is a trusted test override, never a packet field. *)

val _ = PolyML.print_depth 0;
val _ = use (case OS.Process.getEnv "RECEIVER_GATE_CORE" of
    NONE => "generated/ReceiverGate.ML"
  | SOME path => path);

structure GeneratedReceiverCli =
struct
  exception InvalidInput;
  val maxLine = 16384;
  val maxTokens = 132;
  val maxDigits = 160;
  val maxWidth : IntInf.int = 64;

  fun decimal token =
    if String.size token = 0 orelse String.size token > maxDigits orelse
       not (List.all (fn c => #"0" <= c andalso c <= #"9") (String.explode token))
    then raise InvalidInput
    else List.foldl
      (fn (c, acc : IntInf.int) => 10 * acc + IntInf.fromInt (Char.ord c - Char.ord #"0"))
      (0 : IntInf.int) (String.explode token);

  fun natural token = ReceiverGate.nat_of_integer (decimal token);
  fun showNat value = IntInf.toString (ReceiverGate.integer_of_nat value);
  fun showBytes NONE = "N"
    | showBytes (SOME values) = "B" ^ String.concat (List.map (fn x => " " ^ showNat x) values);
  fun showPacket NONE = "N"
    | showPacket (SOME (kind, (who, epoch))) =
        "P " ^ showNat kind ^ " " ^ showNat who ^ " " ^ showNat epoch;

  fun execute line =
    let
      val tokens = String.tokens Char.isSpace line;
      val _ = if List.length tokens <= maxTokens then () else raise InvalidInput;
    in
      case tokens of
        ["V"] => "ISABELLE_RECEIVER_GATE_V1"
      | command :: width :: cap :: args =>
          let
            val w = decimal width;
            val _ = if w <= maxWidth then () else raise InvalidInput;
            val n = ReceiverGate.nat_of_integer w;
            val limit = natural cap;
          in
            case (command, args) of
              ("E", [kind, who, epoch]) => showBytes
                (ReceiverGate.frame_encode_numbers n limit (natural kind) (natural who) (natural epoch))
            | ("R", port :: values) => showPacket
                (ReceiverGate.receiver_decode_numbers n limit (natural port) (List.map natural values))
            | _ => raise InvalidInput
          end
      | _ => raise InvalidInput
    end;

  datatype bounded_line = End | TooLong | Line of string;
  fun readLine stream =
    let
      fun finish chars tooLong = if tooLong then TooLong else Line (String.implode (List.rev chars));
      fun scan chars count tooLong seen =
        case TextIO.input1 stream of
          NONE => if seen then finish chars tooLong else End
        | SOME #"\n" => finish chars tooLong
        | SOME c =>
            if not tooLong andalso count < maxLine
            then scan (c :: chars) (count + 1) false true
            else scan [] maxLine true true;
    in scan [] 0 false false end;

  fun writeReply reply = (TextIO.output (TextIO.stdOut, reply ^ "\n"); TextIO.flushOut TextIO.stdOut);
  fun run () =
    case readLine TextIO.stdIn of
      End => TextIO.flushOut TextIO.stdOut
    | TooLong => (writeReply "X"; run ())
    | Line line => (writeReply (execute line handle InvalidInput => "X"); run ());
end;

val _ = (GeneratedReceiverCli.run ()
  handle ex => (TextIO.output (TextIO.stdErr, "Receiver runtime failure: " ^ General.exnMessage ex ^ "\n");
    TextIO.flushOut TextIO.stdErr; OS.Process.exit OS.Process.failure));
