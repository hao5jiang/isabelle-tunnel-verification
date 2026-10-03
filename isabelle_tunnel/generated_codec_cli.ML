(* A small, separately tested text interface to the Isabelle export.
   This wrapper is not part of the formal correctness proof.
   E n L k / D n L byte... / S n L byte... / V
   Replies: N (core None), B byte... (core byte list), V k (core value),
   X (lexical, arity, or resource-policy rejection).
   EPOCH_CODEC_CORE is a trusted test override, not a network input. *)

val _ = PolyML.print_depth 0;
val _ = use (case OS.Process.getEnv "EPOCH_CODEC_CORE" of
    NONE => "generated/EpochCodec.ML"
  | SOME path => path);

structure GeneratedCodecCli =
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

  fun natural token = EpochCodec.nat_of_integer (decimal token);
  fun showNat value = IntInf.toString (EpochCodec.integer_of_nat value);
  fun showBytes NONE = "N"
    | showBytes (SOME values) = "B" ^ String.concat (List.map (fn x => " " ^ showNat x) values);
  fun showValue NONE = "N"
    | showValue (SOME value) = "V " ^ showNat value;

  fun execute line =
    let
      val tokens = String.tokens Char.isSpace line;
      val _ = if List.length tokens <= maxTokens then () else raise InvalidInput;
    in
      case tokens of
        ["V"] => "ISABELLE_EPOCH_CODEC_V1"
      | command :: width :: cap :: args =>
          let
            val w = decimal width;
            val _ = if w <= maxWidth then () else raise InvalidInput;
            val n = EpochCodec.nat_of_integer w;
            val limit = natural cap;
          in
            case (command, args) of
              ("E", [value]) => showBytes (EpochCodec.epoch_encode n limit (natural value))
            | ("D", values) => showValue (EpochCodec.epoch_decode n limit (List.map natural values))
            | ("S", values) => showBytes (EpochCodec.epoch_checked_successor n limit (List.map natural values))
            | _ => raise InvalidInput
          end
      | _ => raise InvalidInput
    end;

  datatype bounded_line = End | TooLong | Line of string;

  (* Keep at most maxLine characters. Drain an oversized line without
     retaining it, then resume at the next command. *)
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

  fun writeReply reply = (TextIO.output (TextIO.stdOut, reply ^ "\n");
    TextIO.flushOut TextIO.stdOut);
  fun run () =
    case readLine TextIO.stdIn of
      End => TextIO.flushOut TextIO.stdOut
    | TooLong => (writeReply "X"; run ())
    | Line line => (writeReply (execute line handle InvalidInput => "X"); run ());
end;

val _ = (GeneratedCodecCli.run ()
  handle ex => (TextIO.output (TextIO.stdErr, "Codec runtime failure: " ^ General.exnMessage ex ^ "\n");
    TextIO.flushOut TextIO.stdErr; OS.Process.exit OS.Process.failure));
