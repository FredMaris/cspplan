let _ = 
  Utils.begin_time := Utils.get_time () ;
  let print_help () =
    Utils.eprint "\nUsage: %s DOMAIN PROBLEM [ALGORITHM]\n
DOMAIN: strips temporal planning domain expressed in (typed) PDDL
PROBLEM: strips temporal planning problem expressed in (typed) PDDL
ALGORITHM: one of the following:
\t- cspplan : CSP Planner

\n" Sys.argv.(0) ;
    exit 0
  in
  let nb_args = Array.length Sys.argv in
  let algo = 
    if nb_args < 3 then print_help ()
    else
      if nb_args = 3 then "cspplan" else Sys.argv.(3) in
    match algo with
      | "cspplan" -> (new Cspplan.t Sys.argv.(2) Sys.argv.(1) 0)#search
      | x -> Utils.eprint "\n%s : search procedure unknown.\n" x ; print_help ()
