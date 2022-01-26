let encoding_list = ["gp-csp"]
and solvers_list = ["depqbf"; "rareqs"; "caqe"; "qute"; "minisat"; "glucose"; "glucose-syrup"; "picosat"; "lingeling"]
and mode = ref "cspplan"
and encoding = ref "gp-csp"
and inputencoding = ref ""
and domain = ref ""
and problem = ref ""
and constraints = ref ""
and gpminlevel = ref 0
and options = ref ""
and solver = ref "depqbf"
and incrmode = ref 1
and incmin = ref 1
and timeout = ref 0
and verbose = ref 0 (* 0 = not verbose *)
and lint = ref false
and nodewidth = ref 1

let () =
  let usage = "\
Usage: "^Sys.argv.(0)^" [-OPTIONS] DOMAIN PROBLEM [-OPTIONS]

CSPPLAN compiler: generates a CSP encoding (in XML format) of planning problem defined from PDDL files.

DOMAIN: strips planning domain expressed in (typed) PDDL
PROBLEM: strips planning problem expressed in (typed) PDDL

OPTIONS:
"
  and argspecs = [ (* This list enumerates the different flags (-x,-f...)*)
    ("-e", Arg.Symbol (encoding_list, fun s -> encoding:=s), (
        ": CSPPLAN encoding [default: "^ !encoding ^"]\n"^
        "\t- gp-csp : GP-CSP encoding [Do & Kambhampati, 2001] (default)"));

    ("-gpminlevel", Arg.Set_int gpminlevel,
     ("N: set the minimum level of the planning graph [default: "^ string_of_int !gpminlevel ^"]"));

    ("-lint", Arg.Set lint,
     ("check that the syntax of the given domain/problem is correct"));
  ]

  (* The 'alone' arguments (not preceeded by a '--something') are going to be
     processed by this function in the order they appear. The first alone
     argument is interpreted as DOMAIN, the second is PROBLEM. *)
  and process_arg_alone arg =
    match !domain, !problem with
    | "", _ -> domain := arg (*  *)
    | _, "" -> problem := arg
    | _, _  -> (Printf.eprintf "Usage: %s [opts] DOMAIN PROBLEM (see --help).\n"
                  Sys.argv.(0); exit 1)
  in
  Arg.parse argspecs (process_arg_alone) usage; (* Parse command-line args *)
  Utils.begin_time := Utils.get_time ();

  (* Check that the user entered DOMAIN and PROBLEM *)
  if !domain = "" || !problem = "" then
    (Printf.eprintf "Usage: %s [opts] DOMAIN PROBLEM (see --help).\n" Sys.argv.(0); exit 1);

  if !lint then begin
    open_in !domain |> Lexing.from_channel |> Parser.domain Lexer.token |> ignore;
    open_in !problem |> Lexing.from_channel |> Parser.problem Lexer.token |> ignore;
    Printf.eprintf "\n";
  end else
  match !encoding with
    | "gp-csp" -> (new Cspplan.t !problem !domain !gpminlevel)#search
    | _ -> failwith "encoding impossible (tell the dev)"
