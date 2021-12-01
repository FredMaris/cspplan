class node_common =
object (self)

  val mutable n = Array.make 256 0
  method n level = n.(level)
  method set_n level nn = n.(level) <- nn

  val mutable level = max_int
  method level = level
  method set_level nlevel = level <- nlevel

end

class fluent atom =
object (self)
  inherit node_common
  inherit [action] Node.fluent atom

  val string = 
    let bs = Bytes.of_string ("F_" ^ atom#pred#to_string ^ 
    (if atom#nb_terms = 0 then "" else "_" ^  (Utils.string_of_array "_" Utils.to_string atom#terms)))
 (*   ^ "[" ^ (string_of_int (fst atom#timeset)) ^ ";" ^ (string_of_int (snd atom#timeset)) ^ "]" *) in
    for i = 0 to (Bytes.length bs) - 1 do
     if (Bytes.get bs i) = '-' then (Bytes.set bs i '_');
    done;
    Bytes.to_string bs

  val mutable agenda_pos = []
  val mutable agenda_neg = []
  val mutable neglevel = max_int

  val mutable maxlevel = -1

  method neglevel = neglevel
  method set_neglevel nneglevel = neglevel <- nneglevel

  method maxlevel = maxlevel
  method set_maxlevel maxl = maxlevel <- maxl


  method to_string = string
end


and action name params duration quality prec nprec add del =
object (self)
  inherit node_common
  inherit [fluent] Node.action name params duration quality prec nprec add del

  val mutable ident_num = 0
  
  val mutable maxlevel = -1
  
  method ident_num = ident_num
  method set_ident_num idn = ident_num <- idn
  
  method maxlevel = maxlevel
  method set_maxlevel maxl = maxlevel <- maxl


  val string =
    let bs = Bytes.of_string ("A_" ^ name ^ if Array.length params = 0 then "" else "_" ^ (Utils.string_of_array "_" Utils.to_string params)) in
    for i = 0 to (Bytes.length bs) - 1 do
     if (Bytes.get bs i) = '-' then (Bytes.set bs i '_');
    done;
    Bytes.to_string bs

  method to_string = string

  method presentation_string = "(" ^ name ^ if Array.length params = 0 then ")" else " " ^ (Utils.string_of_array " " Utils.to_string params) ^ ")"

  method to_complete_string = 
  let changedash s = (String.map (fun c -> if c=='-' then '_' else c) s) in
    let string_of_fluent_array fluents =
      (String.map (fun c -> if c=='-' then '_' else c) (Utils.string_of_array "," Utils.to_string fluents)) in
      "$Cond(" ^ (changedash string) ^ ") = [" ^ string_of_fluent_array prec ^ "]\n" ^
      "$Add(" ^ (changedash string) ^ ") = [" ^ string_of_fluent_array add ^ "]\n" ^
      "$Del(" ^ (changedash string) ^ ") = [" ^ string_of_fluent_array del ^ "]\n" (* ^
      "$minlevel(" ^ (changedash string) ^ ") = " ^ (string_of_int (self)#level) ^ "\n" ^
      "$maxlevel(" ^ (changedash string) ^ ") = " ^ (string_of_int (self)#maxlevel) ^ "\n" *)

(*
  method to_complete_string = 
    let string_of_fluent_array fluents =
      Utils.string_of_array "#" Utils.to_string fluents in
      "s$Prec$" ^ string ^ "#" ^ string_of_fluent_array prec ^ "#\n" ^
      "s$Add$" ^ string ^ "#" ^ string_of_fluent_array add ^ "#\n" ^
      "s$Del$" ^ string ^ "#" ^ string_of_fluent_array del ^ "#\n" *)
end


class plan succes = 
object 
  inherit [fluent, action] SequentialPlan.t succes
end

class ['fluent, 'action, 'plan] tsp_common =
object
  method create_fluent = new fluent
  method create_action = new action
  val plan_succes = new plan true
  val plan_fail = new plan false
  method plan_succes = plan_succes
  method plan_fail = plan_fail
end


let positive_print_int i node = Utils.print "%i " (node#n i)
let positive_print_string i node = Utils.print "%s(%i) " node#to_string i
let negative_print_int i node = Utils.print "-%i " (node#n i)
let negative_print_string i node = Utils.print "-%s(%i) " node#to_string i
let endl_int () = Utils.print "0\n"
let endl_string () = Utils.print "\n"


(* [time_allowed] is in seconds. The same amount of time before timeout is
   given to finding the existence (i.e., increase the depth until the QBF is
   true) and to extracting the plan.
   [verbose] 0 -> not verbose, 1 -> more verbose, 2 -> even more verbose *)
class t (problem:string) (domain:string) (gpminlevel:int) (* (options:string) (encoding : int) (inputencoding : string) (solvernum : int) (nodewidth : int) (incrmode : int) (incmin : int) (time_allowed : int) (verbose : int) *) = 
object (self)
  inherit [fluent, action, plan] PlanningData.t problem domain "" as pdata
  inherit [fluent, action, plan] tsp_common

  (* val mutable solver = (new Smtsolver.t) *)
  val debug_mode = false
  val mutable solved = false
  val mutable nb = 0
  val mutable nbc = 0
  val mutable rpg_max_level = 0
  val mutable plan = []
  val mutable goals = []
  val mutable search_level = 0
val mutable depth_counter = ref 0

  (* val mutable nw = nodewidth *)

  val mutable constraintscalc = true
  val mutable branchc = 0
  val mutable nodec = 0

  method print_statistics = ()
  method run = self#plan_fail

  method virtual create_action : string -> Symb.constant array -> float -> int -> ('fluent*Timedata.t) array -> ('fluent*Timedata.t) array -> ('fluent*Timedata.t) array -> ('fluent*Timedata.t) array -> 'action

(*  method search =
    let (search_time,_) = Utils.my_time "Searching plan (TLP-GP algorithm)" (fun () -> self#notimed_search) in
      Utils.print "Total search time : %.2f\n" search_time *)

  method search = (* notimed_search *)

    (* Utils.print "Searching plan (TLP-GP algorithm) .....\n"; *)

    let get_f_time_bound (f : 'fluent) (a_iset : (('fluent*Timedata.t) array)) = 
      Array.fold_left (fun t ((fluent,timedata) : ('fluent*Timedata.t)) ->
        if (fluent#atom#equal f#atom)
        then (timedata#closed_left,timedata#closed_right)
        else t
      ) (true,true) a_iset
    in

    let get_f_timedata_code (f : 'fluent) (a_iset : (('fluent*Timedata.t) array)) = 
      Array.fold_left (fun t ((fluent,timedata) : ('fluent*Timedata.t)) ->
        if (fluent#atom#equal f#atom)
        then timedata#code
        else t
      ) (-1) a_iset
    in

    let get_f_time f a_iset = 
      Array.fold_left (fun t x -> if ((fst x)#atom#equal f#atom) then (snd x)#timeset else t) (-1.0,-1.0) a_iset
    in
    (*let get_f f a_iset =
      Array.fold_left (fun c x -> if ((fst x)#atom#equal f#atom) then (fst x) else c) f a_iset
    in*)


(* ***
    let exception Timeout in
(* [time_left] returns the number of seconds (as an integer) remaining before
   timeout; if the remaining number of seconds is negative or 0, raise Timeout.
   If the time allowed is zero, then we just say that the time left is 0 (=unlimited) *)
let time_left time_start =
  if time_allowed = 0 then 0.
  else
    let remain = (float_of_int time_allowed) -. (Unix.gettimeofday () -. time_start) in
    if remain <= 0. then (print_float remain; raise Timeout) else remain
in
let command cmd =
  if verbose>0 then begin
    if Unix.isatty Unix.stderr then Printf.eprintf "\x1b[33m%s\x1b[0m\n" cmd
    else Printf.eprintf "%s\n" cmd
  end;
  Sys.command cmd
in
*** *)

(* ***

flush stdout; flush stderr;
Utils.print "Select TouIST\n";
flush stdout; flush stderr;
let returncode = (command "touist --version") in
flush stdout; flush stderr;
if returncode == 0 then Utils.print "\n"
else begin Utils.eprint "[Error %d] please install TouIST with : brew install touist\n" returncode; exit returncode; end;

let stringrules = match encoding with
  | 0 -> "[QBF] Explanatory Frame-axioms"
  | 1 -> "[QBF] No-ops"
  | 2 -> "[QBF] Explanatory Frame-axioms NFLA"
  | 3 -> "[QBF] Open Conditions"
  | 100 -> "[SAT] Explanatory Frame-axioms"
  | 103 -> "[SAT] Open Conditions"
  | 203 -> "[SMT QF_RDL] Open Conditions (temporal)"
  | 213 -> "[SMT QF_RDL] Causal Links (temporal)"
  | 1100 -> "[SAT] Input Encoding Rules from " ^ inputencoding
in
Utils.print "Select [LANGUAGE] EncodingRules: %s\n\n" stringrules;

if nw >1 && encoding==0 then
begin
  Utils.print "Select node width to %d steps.\n\n" nw;
end else
begin
  Utils.print "Ignore node width (not available with selected encoding rules).\n\n";
  nw <- 1
end;

let solvername = match solvernum with
  | 0 -> if encoding<100 then "DepQBF" else if (encoding<200) || (encoding>=1000) then "MiniSat" else "Yices"
  | 1 -> "RAReQS"
  | 2 -> "CAQE"
  | 3 -> "Qute"
  | 101 -> "Glucose"
  | 102 -> "Glucose (multicore)"
  | 103 -> "PicoSat"
  | 104 -> "Lingeling"
in
Utils.print "Select %s SOLVER: %s\n\n" (if encoding<100 then "QBF" else if encoding<200 then "SAT" else "SMT") solvername;

*** *)

    
(** GRAPH for CSPPLAN **)    
   
    let current_level = ref 0 in
    let build_rpg = (* Building the Temporal Relaxed Planning Graph *)
      Utils.print "Building the Temporal Relaxed Planning Graph ...\n";
      Array.iter (fun f ->
                   (if (List.exists (fun p ->
                                        (p#atom#equal f#atom))
                        (Array.to_list pdata#init_state))
                    then f#set_level 0))
      pdata#fluents;
      while (not (!current_level>=gpminlevel && (List.for_all (fun p -> 
                    (List.exists (fun f ->
                       (f#atom#equal p#atom) && (f#level <= !current_level))
                    (Array.to_list pdata#fluents)))
                  (Array.to_list pdata#goal))))
      && (!current_level<=1024) do
        Array.iter (fun a -> (if (a#level > !current_level) &&
          (Array.fold_left (fun b prec -> b &&
            Array.fold_left (fun c f -> c ||
              ((f#atom#equal prec#atom) && (f#level <= !current_level)))
            false pdata#fluents)
          true a#prec)
          then begin
               a#set_level (succ !current_level);
               Array.iter (fun f ->
                   if (f#level > !current_level) && (List.exists (fun add ->
                                 (f#atom#equal add#atom))
                                 (Array.to_list a#add))
                   then f#set_level (succ !current_level))
               pdata#fluents;
               Array.iter (fun f ->
                   if (f#neglevel > !current_level) && (List.exists (fun del ->
                                 (f#atom#equal del#atom))
                                 (Array.to_list a#del))
                   then f#set_neglevel (succ !current_level))
               pdata#fluents;
               end))
          pdata#actions;
 
       current_level := succ !current_level
      done;
      rpg_max_level <- !current_level;
Utils.print "Goal found at level %d.\n" !current_level;
(*Array.iter (fun a -> Utils.print "%s(level[%d])\n" a#to_string a#level) pdata#actions;
Array.iter (fun f -> Utils.print "%s(level[%d],neglevel[%d])\n" f#to_istring f#level f#neglevel) pdata#fluents;*)

    in

      build_rpg;



(* Reducing Graph *)
  let subgoals = ref [] in
  let newsubgoals = ref [] in
    subgoals := (Array.to_list (Array.map (fun f -> (f,rpg_max_level)) pdata#goal));
    Array.iter (fun f -> f#set_maxlevel rpg_max_level) pdata#goal;
    for i = rpg_max_level downto 1 do
      List.iter (fun ((f : 'fluent),lev) ->
        if (lev==i) && (f#level > i) then begin Printf.printf "Subgoal %s unreachable at level %d.\n" f#to_string i; exit 0; end else
        Array.iter (fun (a : 'action) ->
          if (a#maxlevel < i) then
          begin
            a#set_maxlevel i;
            Array.iter (fun (p : 'fluent) ->
            if p#maxlevel < i-1 then begin p#set_maxlevel (i-1); newsubgoals := (p,i-1) :: !newsubgoals; end
            ) a#prec
          end
        ) f#producers
      ) !subgoals;
      subgoals := (List.append !newsubgoals !subgoals);
      newsubgoals := [];
    done;
  Array.iter (fun f -> if f#maxlevel < 0 then f#set_maxlevel 0) pdata#init_state;

(* END GRAPH *)

let lvars = ref [] in

let csplevels = ref [] in
let fluentslist = (Array.to_list pdata#fluents) in

let nb_actions = Array.length pdata#actions in
let nb_fluents = Array.length pdata#fluents in

let action_code action level = string_of_int (nb_actions * level + action#num) in

(* Printf.printf "Nombre actions: %d\n" (Array.length pdata#actions);
Printf.printf "Nombre fluents: %d\n" (Array.length pdata#fluents);

Array.iter (fun a -> Printf.printf "%d: %s [%d,%d]\n" a#num a#to_string a#level a#maxlevel) pdata#actions;
Array.iter (fun f -> Printf.printf "%s [%d,%d]\n" f#to_string f#level f#maxlevel) pdata#fluents; *)


Printf.printf "<instance>
<presentation format=\"XCSP 2.1\" type=\"CSP\" name=\"%s__%s__%d\">
</presentation>\n" pdata#domain_name pdata#problem_name rpg_max_level;

Printf.printf "<planning_data pddl_domain=\"%s\" pddl_problem=\"%s\" plangraph_max_level=\"%d\">\n" pdata#domain_name pdata#problem_name rpg_max_level;

Printf.printf "<init_state nb_fluents=\"%d\"> " (Array.length pdata#init_state);
Array.iter (fun f -> Printf.printf "%s " f#to_string) pdata#init_state; Printf.printf "</init_state>\n" ;

Printf.printf "<goal nb_fluents=\"%d\"> " (Array.length pdata#goal);
Array.iter (fun f -> Printf.printf "%s " f#to_string) pdata#goal; Printf.printf "</goal>\n" ;


Printf.printf "<actions nb_actions=\"%d\">\n" (Array.length pdata#actions);

Array.iter (fun a -> Printf.printf "<action number=\"%d\" name=\"%s\" nb_cond=\"%d\" nb_add=\"%d\" nb_del=\"%d\">\n" a#num a#to_string (Array.length a#prec) (Array.length a#add) (Array.length a#del);
    if (Array.length a#prec) != 0 then begin
      Printf.printf "<cond action_num=\"%d\" nb_fluents=\"%d\"> " a#num (Array.length a#prec);
      Array.iter (fun f -> Printf.printf "%s " f#to_string) a#prec; Printf.printf "</cond>\n" ;
    end;
    if (Array.length a#add) != 0 then begin
      Printf.printf "<add action_num=\"%d\" nb_fluents=\"%d\"> " a#num (Array.length a#add);
      Array.iter (fun f -> Printf.printf "%s " f#to_string) a#add; Printf.printf "</add>\n" ;
    end;
    if (Array.length a#del) != 0 then begin
      Printf.printf "<del action_num=\"%d\" nb_fluents=\"%d\"> " a#num (Array.length a#del);
      Array.iter (fun f -> Printf.printf "%s " f#to_string) a#del; Printf.printf "</del>\n" ;
    end;
    Printf.printf "</action>\n"
  ) pdata#actions;


Printf.printf "</actions>\n";

Printf.printf "</planning_data>\n";



for i=rpg_max_level downto 1 do
  csplevels := 
  (List.map (fun f2 -> (f2, Array.fold_left (fun l a -> if (a#level <= i) && (i <= a#maxlevel) then a::l else l) [] f2#producers)
    ) (List.filter (fun f -> (f#level <= i) && (i<= f#maxlevel)) fluentslist)
  )::!csplevels;
done;

let nb_cspvars = List.fold_left (fun n l -> n+(List.length l)) 0 !csplevels in

(* Affichage Niveaux CSPPLAN *)
(*List.iteri (fun i lf -> Printf.printf "Level %d:\n" (i+1); 
  List.iter (fun (f,l) -> Printf.printf "%s [ " f#to_string;
    List.iter (fun a -> Printf.printf "%s " a#to_string;
    ) l;
    Printf.printf "]\n"
  ) lf 
) !csplevels ; *)


Printf.printf "<domains nbDomains=\"%d\">\n" nb_cspvars;

List.iteri (fun i l -> 
  List.iter (fun (f,fprods) ->
    Printf.printf "<domain name=\"D_%s__%d\" nbValues=\"%d\">\n%s" f#to_string (i+1) ((if i+1==rpg_max_level then 0 else 1) + List.length fprods) (if i+1==rpg_max_level then "" else "-1 ");
    List.iter (fun a ->
      Printf.printf "%s " (action_code a (i+1))
    ) fprods;
    Printf.printf "\n</domain>\n"
  ) l
) !csplevels;


Printf.printf "</domains>\n<variables nbVariables=\"%d\">\n" nb_cspvars;

List.iteri (fun i l ->
  List.iter (fun (f,_)->
    Printf.printf "<variable name=\"%s__%d\" domain=\"D_%s__%d\"/>\n" f#to_string (i+1) f#to_string (i+1)
  ) l
) !csplevels;

Printf.printf "</variables>\n";


let relations = ref [] in
(* Contraintes de causalité entre deux niveaux successifs du graphe de planification *)
for i = 0 to rpg_max_level - 2 do
  List.iter (fun (fprec,_) ->
    List.iter (fun (f,fprods) -> 
      let (tuples,ntuples) = List.fold_left (fun (t,nt) a -> if (Array.memq fprec a#prec) then ((t^(if nt==0 then "" else "|\n")^"-1 "^(action_code a (i+2))^" "),nt+1) else (t,nt)) ("",0) fprods in
      if ntuples != 0 then
      relations := ((Printf.sprintf "<relation name=\"relCausality__%s__%d__%s__%d\" arity=\"2\" nbTuples=\"%d\" semantics=\"conflicts\">\n%s \n</relation>\n" fprec#to_string (i+1) f#to_string (i+2) ntuples tuples),
      (Printf.sprintf "<constraint name=\"constrCausality__%s__%d__%s__%d\" arity=\"2\" reference=\"relCausality__%s__%d__%s__%d\" scope=\"%s__%d %s__%d\"/>\n" fprec#to_string (i+1) f#to_string (i+2) fprec#to_string (i+1) f#to_string (i+2) fprec#to_string (i+1) f#to_string (i+2))
      )::!relations
    ) (List.nth !csplevels (i+1))
  ) (List.nth !csplevels i)
done;
(* Contraintes de mutex dans un même niveau du graphe de planification *)
let is_mutex a1 a2 =
  (Array.exists (fun f1 -> (Array.memq f1 a2#add)||(Array.memq f1 a2#prec)) a1#del)
  ||(Array.exists (fun f2 -> (Array.memq f2 a1#add)||(Array.memq f2 a1#prec)) a2#del)
  in
let rec genmutex l i =
  match l with
  (f1,fprods1)::l2 -> List.iter (fun (f2,fprods2) -> 
                        let (tuples,ntuples) = List.fold_left (fun (t1,nt1) a1 -> 
                                                List.fold_left (fun (t2,nt2) a2 ->
                                                  if is_mutex a1 a2 then ((t2^(if nt2==0 then "" else "|\n")^(action_code a1 (i+1))^" "^(action_code a2 (i+1))^" "),nt2+1) else (t2,nt2)
                                                ) (t1,nt1) fprods2
                                              ) ("",0) fprods1 in
                        if ntuples != 0 then
                        relations := ((Printf.sprintf "<relation name=\"relMutex__%s__%d__%s__%d\" arity=\"2\" nbTuples=\"%d\" semantics=\"conflicts\">\n%s \n</relation>\n" f1#to_string (i+1) f2#to_string (i+1) ntuples tuples),
                        (Printf.sprintf "<constraint name=\"constrMutex__%s__%d__%s__%d\" arity=\"2\" reference=\"relMutex__%s__%d__%s__%d\" scope=\"%s__%d %s__%d\"/>\n" f1#to_string (i+1) f2#to_string (i+1) f1#to_string (i+1) f2#to_string (i+1) f1#to_string (i+1) f2#to_string (i+1))
                        )::!relations
                      ) l2;
                      genmutex l2 i;
  | [] -> ()
  in
for i = 0 to rpg_max_level - 1 do
  genmutex (List.nth !csplevels i) i;
done;


Printf.printf "<relations nbRelations=\"%d\">\n" (List.length !relations);
List.iter (fun (s,_) ->
  Printf.printf "%s" s;
) !relations;


Printf.printf "</relations>\n";

Printf.printf "<constraints nbConstraints=\"%d\">\n" (List.length !relations);
List.iter (fun (_,s) ->
  Printf.printf "%s" s;
) !relations;


Printf.printf "</constraints>\n";


Printf.printf "</instance>\n";



exit 0;






(* *******************************


(* QBFPLAN-SATPLAN / options : (0) QBF-EFA (1) QBF-NOOP (2) QBF-EFA-NFLA (100) SAT-EFA *)

if encoding == 0 then
begin (* option QBF-EFA Nodes-Fluents-Actions Leafs-Fluents-Actions *)
Utils.print "Searching solution with QBFPLAN (Explanatory Frame-Axioms [Gasquet et al., 2018])...\n\n";
end else if encoding == 1 then
begin (* option QBF-NOOP *)
Utils.print "Searching solution with QBFPLAN (Noop Actions [Cashmore et al., 2012])...\n\n";
end else if encoding == 2 then
begin (* option QBF-EFA-NFLA Nodes-Fluents Leafs-Actions *)
Utils.print "Searching solution with QBFPLAN (Explanatory Frame-Axioms, NFLA)...\n\n";
end else if encoding == 3 then
begin (* option QBF-OPEN *)
Utils.print "Searching solution with QBFPLAN (Open Conditions [Gasquet et al., 2018])...\n\n";
end else if encoding == 100 then
begin (* option SAT-EFA *)
Utils.print "Searching solution with SATPLAN (Explanatory Frame-Axioms [Kautz & Selman, 1992])...\n\n";
end else if encoding == 103 then
begin (* option SAT-OPEN *)
Utils.print "Searching solution with SATPLAN (Open Conditions [Gasquet et al., 2018])...\n\n";
end else if encoding == 203 then
begin (* option SMT-OPEN *)
Utils.print "Searching solution with SMTPLAN (Open Conditions [Maris et al., 2018])...\n\n";
end else if encoding == 213 then
begin (* option SMT-LINK *)
Utils.print "Searching solution with SMTPLAN (TLP-GP-2 Causal Links [Maris & Regnier, 2008])...\n\n";
end else if encoding == 1100 then
begin (* option SAT with input file *)
Utils.print "Searching solution with SATPLAN (Encoding from %s)...\n\n" inputencoding;
end;
ignore (command "rm solvedata/*.txt");

(* Génération des quantificateurs *)

let genquantifiers n nexistsb =
if encoding == 0 && nw == 1 then (* QBF-EFA *)
begin
 let quantifiersfile = Unix.openfile "solvedata/in.quantifiers.txt" [Unix.O_TRUNC;Unix.O_CREAT;Unix.O_WRONLY] 0o640 in
 let quantifierswrite s =
   ignore (Unix.write quantifiersfile (Bytes.of_string s) 0 (String.length s)) in
  for i = n downto nexistsb do
    quantifierswrite (Printf.sprintf "exists $A(%d) for $A in $O:\nexists $f(%d) for $f in $F:\nexists b(%d):\n" i i i);
  done;
  for i = nexistsb - 1 downto 1 do
    quantifierswrite (Printf.sprintf "exists $A(%d) for $A in $O:\nexists $f(%d) for $f in $F:\nforall b(%d):\n" i i i);
  done;
  quantifierswrite "exists $A(0) for $A in $O:\nexists $f(0) for $f in $F:\n";
 Unix.close quantifiersfile;
end
else if encoding == 1 then (* QBF-NOOP *)
begin
 let quantifiersfile = Unix.openfile "solvedata/in.quantifiers.txt" [Unix.O_TRUNC;Unix.O_CREAT;Unix.O_WRONLY] 0o640 in
 let quantifierswrite s =
   ignore (Unix.write quantifiersfile (Bytes.of_string s) 0 (String.length s)) in
  for i = n downto nexistsb do
    quantifierswrite (Printf.sprintf "exists $A(%d) for $A in $O:\nexists Noop($f,%d) for $f in $F:\nexists b(%d):\n" i i i);
  done;
  for i = nexistsb - 1 downto 1 do
    quantifierswrite (Printf.sprintf "exists $A(%d) for $A in $O:\nexists Noop($f,%d) for $f in $F:\nforall b(%d):\n" i i i);
  done;
  quantifierswrite "exists $A(0) for $A in $O:\nexists Noop($f,0) for $f in $F:\n";
 Unix.close quantifiersfile;
 end
else if encoding == 2 then (* QBF-EFA-NFLA *)
begin
 let quantifiersfile = Unix.openfile "solvedata/in.quantifiers.txt" [Unix.O_TRUNC;Unix.O_CREAT;Unix.O_WRONLY] 0o640 in
 let quantifierswrite s =
   ignore (Unix.write quantifiersfile (Bytes.of_string s) 0 (String.length s)) in
  for i = n downto nexistsb do
    quantifierswrite (Printf.sprintf "exists $f(%d) for $f in $F:\nexists b(%d):\n" i i);
  done;
  for i = nexistsb - 1 downto 1 do
    quantifierswrite (Printf.sprintf "exists $f(%d) for $f in $F:\nforall b(%d):\n" i i);
  done;
  quantifierswrite "exists $A(0) for $A in $O:\n";
 Unix.close quantifiersfile;
end
else if encoding == 3 then (* QBF-OPEN *)
begin
 let quantifiersfile = Unix.openfile "solvedata/in.quantifiers.txt" [Unix.O_TRUNC;Unix.O_CREAT;Unix.O_WRONLY] 0o640 in
 let quantifierswrite s =
   ignore (Unix.write quantifiersfile (Bytes.of_string s) 0 (String.length s)) in
  for i = n downto nexistsb do
    quantifierswrite (Printf.sprintf "exists $A(%d) for $A in $O:\nexists open($f,%d) for $f in $F:\nexists b(%d):\n" i i i);
  done;
  for i = nexistsb - 1 downto 1 do
    quantifierswrite (Printf.sprintf "exists $A(%d) for $A in $O:\nexists open($f,%d) for $f in $F:\nforall b(%d):\n" i i i);
  done;
  quantifierswrite "exists $A(0) for $A in $O:\nexists open($f,0) for $f in $F:\n";
 Unix.close quantifiersfile;
 end
else if encoding == 0 && nw > 1 then (* QBF-EFA with node width >1 *)
begin
 let quantifiersfile = Unix.openfile "solvedata/in.quantifiers.txt" [Unix.O_TRUNC;Unix.O_CREAT;Unix.O_WRONLY] 0o640 in
 let quantifierswrite s =
   ignore (Unix.write quantifiersfile (Bytes.of_string s) 0 (String.length s)) in
  (* On définit le nombre d'étapes par noeud avant les quantificateurs *)
  quantifierswrite (Printf.sprintf "$nodewidth = %d\n\n" nw);
  for i = n downto nexistsb do
   for j = 1 to nw do
    quantifierswrite (Printf.sprintf "exists $A(%d,%d) for $A in $O:\nexists $f(%d,%d) for $f in $F:\n" i j i j);
   done;
   quantifierswrite (Printf.sprintf "exists b(%d):\n" i);
  done;
  for i = nexistsb - 1 downto 1 do
   for j = 1 to nw do
    quantifierswrite (Printf.sprintf "exists $A(%d,%d) for $A in $O:\nexists $f(%d,%d) for $f in $F:\n" i j i j);
   done;
   quantifierswrite (Printf.sprintf "forall b(%d):\n" i);
  done;
  for j = 1 to nw do
   quantifierswrite (Printf.sprintf "exists $A(0,%d) for $A in $O:\nexists $f(0,%d) for $f in $F:\n" j j);
  done;
 Unix.close quantifiersfile;
end;
in

(* Génération des formules non quantifiées *)

if encoding == 0 && nw == 1 then (* option QBF-EFA *)
begin
 let qfformulafile = Unix.openfile "solvedata/in.qfformula.txt" [Unix.O_TRUNC;Unix.O_CREAT;Unix.O_WRONLY] 0o640 in
 let qfformulawrite s =
   ignore (Unix.write qfformulafile (Bytes.of_string s) 0 (String.length s)) in  
    let efaprint fsrc fdst adddel adst bi bj = "\\\and\nbigand $i in [1..$depth]:\n  bigand $f in $F:\n      " ^ fsrc ^ " or " ^ fdst ^ "\n      or bigor $A in $O when $f in $" ^ adddel ^ "($A):\n         " ^ adst ^ "\n      end\n      or " ^ bi ^ "\n      or bigor $j in [1..$i-1]:\n         " ^ bj ^ "\n      end\n  end\nend\n" in
(**     qfformulawrite "\n;; (QBF-EFA1.1) Etat initial vérifié pour la feuille la plus à gauche\n\nbigand $f in $I:\n  $f(0)\n  or bigor $i in [1..$depth]:\n    b($i)\n  end\nend\n\nand\nbigand $f in ($F diff $I):\n  not $f(0)\n  or bigor $i in [1..$depth]:\n    b($i)\n  end\nend\n"; **)
     qfformulawrite "\n;; (QBF-EFA1.2) But vérifié pour la feuille la plus à droite (propagation si but atteint avant)\n\nbigand $f in $G:\n  $f(0)\n  or bigor $i in [1..$depth]:\n    not b($i)\n  end\nend\n";
    qfformulawrite "\n;; (QBF-EFA2.0) Conditions des actions de la première étape\n\n\\\and bigand $A in $O when not ($Cond($A) subset $I):\n  not $A(0)\n  or bigor $i in [1..$depth]:\n    b($i)\n  end\nend\n";
    qfformulawrite "\n;; (QBF-EFA2.1) Effets des actions\n\n\\\and\nbigand $i in [0..$depth]:\n  bigand $A in $O:\n    bigand $f in $Add($A):\n      not $A($i) or $f($i)\n    end\n    and\n    bigand $f in $Del($A):\n      not $A($i) or not $f($i)\n    end\n  end\nend\n";
(**     qfformulawrite "\nand\nbigand $A in $O:\n  not $A(0)\n  or bigor $i in [1..$depth]:\n    b($i)\n  end\nend\n"; **)
    qfformulawrite "\n;; (QBF-EFA2.2) Conditions des actions (transition feuille -> noeud)\n\n\\\and\nbigand $i in [1..$depth]:\n  bigand $A in $O:\n    bigand $f in $Cond($A):\n      not $A($i)\n      or $f(0)\n      or b($i)\n      or bigor $j in [1..$i-1]:\n         not b($j)\n      end\n    end\n  end\nend\n";
    qfformulawrite "\n;; (QBF-EFA2.3) Conditions des actions (transition noeud -> feuille)\n\n\\\and\nbigand $i in [1..$depth]:\n  bigand $A in $O:\n    bigand $f in $Cond($A):\n      not $A(0)\n      or $f($i)\n      or not b($i)\n      or bigor $j in [1..$i-1]:\n         b($j)\n      end\n    end\n  end\nend\n";
    qfformulawrite "\n;; (QBF-EFA3.1.0) Frames-Axiomes d'ajout (état initial)\n\n\\\and bigand $f in ($F diff $I):\n  not $f(0)\n  or bigor $A in $O when ($f in $Add($A)) and ($Cond($A) subset $I):\n     $A(0)\n  end\n  or bigor $i in [1..$depth]:\n    b($i)\n  end\nend\n";
    qfformulawrite (Printf.sprintf "\n;; (QBF-EFA3.1.1) Frames-axiomes d'ajout (transition feuille -> noeud)\n\n%s" (efaprint "$f(0)" "not $f($i)" "Add" "$A($i)" "b($i)" "not b($j)"));
    qfformulawrite (Printf.sprintf "\n;; (QBF-EFA3.1.2) Frames-axiomes d'ajout (transition noeud -> feuille)\n\n%s" (efaprint "$f($i)" "not $f(0)" "Add" "$A(0)" "not b($i)" "b($j)"));
    qfformulawrite "\n;; (QBF-EFA3.2.0) Frames-Axiomes de retrait (état initial)\n\n\\\and bigand $f in $I:\n  $f(0)\n  or bigor $A in $O when ($f in $Del($A)) and ($Cond($A) subset $I):\n     $A(0)\n  end\n  or bigor $i in [1..$depth]:\n    b($i)\n  end\nend\n";
    qfformulawrite (Printf.sprintf "\n;; (QBF-EFA3.2.1) Frames-axiomes de retrait (transition feuille -> noeud)\n\n%s" (efaprint "not $f(0)" "$f($i)" "Del" "$A($i)" "b($i)" "not b($j)"));
    qfformulawrite (Printf.sprintf "\n;; (QBF-EFA3.2.2) Frames-axiomes de retrait (transition noeud -> feuille)\n\n%s" (efaprint "not $f($i)" "$f(0)" "Del" "$A(0)" "not b($i)" "b($j)"));
    qfformulawrite "\n;; (QBF-EFA4) Mutex (Forall-step semantics)\n\n\\\and\nbigand $i in [0..$depth]:\n  bigand $A in $O:\n    bigand $f in $Cond($A):\n      bigand $B in $O when $A!=$B and $f in $Del($B):\n        not $A($i) or not $B($i)\n      end\n    end\n  end\nend\n";
(*    qfformulawrite "\n;; (QBF-EFA4bis) Mutex (Exists-step semantics)\n\n\\\and\nbigand $i in [0..$depth]:\n  bigand $A in $O:\n    bigand $B in $O when $A!=$B\n                         and inter($Cond($A),$Del($B))!=[]\n                         and inter($Cond($B),$Del($A))!=[]\n                         and inter($Add($A),$Del($B))==[]\n                         and inter($Add($B),$Del($A))==[]:\n      not $A($i) or not $B($i)\n    end\n  end\nend\n"; *)
 Unix.close qfformulafile;
 if constraintscalc then
 begin
   (* Constraints QBF-EFA1.1 *)
     branchc <- branchc + (Array.length pdata#goal);
     nodec <- nodec + 0;
 end;
end else if encoding == 1 then (* option QBF-NOOP *)
begin
 let qfformulafile = Unix.openfile "solvedata/in.qfformula.txt" [Unix.O_TRUNC;Unix.O_CREAT;Unix.O_WRONLY] 0o640 in
 let qfformulawrite s =
   ignore (Unix.write qfformulafile (Bytes.of_string s) 0 (String.length s)) in
    qfformulawrite "\n;; (QBF-NOOP1.1) Etat initial vérifié pour la feuille la plus à gauche\n\nbigand $A in $O when not ($Cond($A) subset $I):\n  not $A(0)\n  or (bigor $i in [1..$depth]:\n    b($i)\n  end)\nend\n";
    qfformulawrite "\n\\\and bigand $f in ($F diff $I):\n  not Noop($f,0)\n  or (bigor $i in [1..$depth]:\n    b($i)\n  end)\nend\n";
    qfformulawrite "\n;; (QBF-NOOP1.2) But vérifié pour la feuille la plus à droite\n\n\\\and bigand $f in $G:\n  (bigor $A in $O when $f in $Add($A):\n    $A(0)\n  end)\n  or Noop($f,0)\n  or (bigor $i in [1..$depth]:\n    not b($i)\n  end)\nend\n";
    qfformulawrite ";; (QBF-NOOP2.1) Liens causaux : Feuille -> Noeud\n\n\\\and bigand $i in [1..$depth]:\n  bigand $A in $O:\n    bigand $f in $Cond($A):\n      not $A($i)\n      or (bigor $B in $O when $f in $Add($B):\n        $B(0)\n      end)\n      or Noop($f,0)\n      or b($i)\n      or (bigor $j in [1..$i-1]:\n        not b($j)\n      end)\n    end\n  end\nend\n";
    qfformulawrite "\\\and bigand $i in [1..$depth]:\n  bigand $f in $F:\n    not Noop($f,$i)\n    or (bigor $B in $O when $f in $Add($B):\n      $B(0)\n    end)\n    or Noop($f,0)\n    or b($i)\n    or (bigor $j in [1..$i-1]:\n      not b($j)\n    end)\n  end\nend\n";
    qfformulawrite ";; (QBF-NOOP2.2) Liens causaux : Noeud -> Feuille\n\n\\\and bigand $i in [1..$depth]:\n  bigand $A in $O:\n    bigand $f in $Cond($A):\n      not $A(0)\n      or (bigor $B in $O when $f in $Add($B):\n        $B($i)\n      end)\n      or Noop($f,$i)\n      or not b($i)\n      or (bigor $j in [1..$i-1]:\n        b($j)\n      end)\n    end\n  end\nend\n";
    qfformulawrite "\n\\\and bigand $i in [1..$depth]:\n  bigand $f in $F:\n    not Noop($f,0)\n    or (bigor $B in $O when $f in $Add($B):\n      $B($i)\n    end)\n    or Noop($f,$i)\n    or not b($i)\n    or (bigor $j in [1..$i-1]:\n      b($j)\n    end)\n  end\nend\n";
    qfformulawrite ";; (QBF-NOOP3) Mutex\n\n\\\and bigand $i in [0..$depth]:\n  bigand $A in $O:\n    bigand $f in ($Cond($A) union $Add($A)):\n      bigand $B in $O when ($A != $B) and ($f in $Del($B)):\n        (not $A($i) or not $B($i))\n      end\n    end\n  end\nend\n";
    qfformulawrite "\n\\\and bigand $i in [0..$depth]:\n  bigand $f in $F:\n    bigand $A in $O when ($f in $Del($A)):\n      (not Noop($f,$i) or not $A($i))\n    end\n  end\nend\n";    
 Unix.close qfformulafile;
end else if encoding == 3 then (* option QBF-OPEN *)
begin
 let qfformulafile = Unix.openfile "solvedata/in.qfformula.txt" [Unix.O_TRUNC;Unix.O_CREAT;Unix.O_WRONLY] 0o640 in
 let qfformulawrite s =
   ignore (Unix.write qfformulafile (Bytes.of_string s) 0 (String.length s)) in
    qfformulawrite "\n;; Ouverture des conditions des actions\n\nbigand $i in [0..$depth]:\n  bigand $A in $O:\n    $A($i) => bigand $f in $Cond($A): open($f,$i) end\n  end\nend\n";
    qfformulawrite "\n;; Ouverture des buts\n\n\\\and (bigand $i in [1..$depth]:\n  b($i) end => bigand $f in $G:\n    open($f,0)\n    or bigor $A in $O when $f in $Add($A):\n      $A(0)\n    end\n  end)\n";
    qfformulawrite "\n;; Fermeture des conditions qui ne sont pas dans I\n\n\\\and (bigand $i in [1..$depth]:\n  not b($i) end => bigand $f in $F diff $I: not open($f,0) end)\n";
    qfformulawrite "\n;; Fermeture des conditions ouvertes\n\n\\\and bigand $i in [1..$depth]:\n  bigand $f in $F:\n    (open($f,$i)\n    and not b($i) \n    and bigand $j in [1..$i-1]:\n      b($j)\n    end)\n    => (open($f,0)\n    or bigor $A in $O when $f in $Add($A):\n      $A(0)\n    end)\n  end\nend\n";
    qfformulawrite "\n\n\\\and bigand $i in [1..$depth]:\n  bigand $f in $F:\n    (open($f,0)\n    and b($i) \n    and bigand $j in [1..$i-1]:\n      not b($j)\n    end)\n    => (open($f,$i)\n    or bigor $A in $O when $f in $Add($A):\n      $A($i)\n    end)\n  end\nend\n";
    qfformulawrite "\n;; Protection des conditions ouvertes\n\n\\\and bigand $i in [1..$depth]:\n  bigand $f in $F:\n    (open($f,$i)\n    and not b($i) \n    and bigand $j in [1..$i-1]:\n      b($j)\n    end)\n    => bigand $A in $O when $f in $Del($A):\n      not $A(0)\n    end\n  end\nend\n";
    qfformulawrite "\n\n\\\and bigand $i in [1..$depth]:\n  bigand $f in $F:\n    (open($f,0)\n    and b($i) \n    and bigand $j in [1..$i-1]:\n      not b($j)\n    end)\n    => bigand $A in $O when $f in $Del($A):\n      not $A($i)\n    end\n  end\nend\n";
    qfformulawrite "\n;; Mutex\n\n\\\and\nbigand $i in [0..$depth]:\n  bigand $A in $O:\n    bigand $f in ($Add($A) union $Cond($A)):\n      bigand $B in $O when $A!=$B and $f in $Del($B):\n        not $A($i) or not $B($i)\n      end\n    end\n  end\nend\n";
 Unix.close qfformulafile;
end else if encoding == 0 && nw > 1 then (* option QBF-EFA with node width >1 *)
begin
 let qfformulafile = Unix.openfile "solvedata/in.qfformula.txt" [Unix.O_TRUNC;Unix.O_CREAT;Unix.O_WRONLY] 0o640 in
 let qfformulawrite s =
   ignore (Unix.write qfformulafile (Bytes.of_string s) 0 (String.length s)) in  
    let efaprint fsrc fdst adddel adst bi bj = "\\\and\nbigand $i in [1..$depth]:\n  bigand $f in $F:\n      " ^ fsrc ^ " or " ^ fdst ^ "\n      or bigor $A in $O when $f in $" ^ adddel ^ "($A):\n         " ^ adst ^ "\n      end\n      or " ^ bi ^ "\n      or bigor $j in [1..$i-1]:\n         " ^ bj ^ "\n      end\n  end\nend\n" in
    qfformulawrite "\n;; (QBF-EFA1.2) But vérifié pour la feuille la plus à droite (propagation si but atteint avant)\n\nbigand $f in $G:\n  $f(0,$nodewidth)\n  or bigor $i in [1..$depth]:\n    not b($i)\n  end\nend\n";
    qfformulawrite "\n;; (QBF-EFA2.0) Conditions des actions de la première étape\n\n\\\and bigand $A in $O when not ($Cond($A) subset $I):\n  not $A(0,1)\n  or bigor $i in [1..$depth]:\n    b($i)\n  end\nend\n";
    qfformulawrite "\n;; (QBF-EFA2.1) Effets des actions\n\n\\\and\nbigand $i in [0..$depth]:\n  bigand $m in [1..$nodewidth]:\n    bigand $A in $O:\n      bigand $f in $Add($A):\n        not $A($i,$m) or $f($i,$m)\n      end\n      and\n      bigand $f in $Del($A):\n        not $A($i,$m) or not $f($i,$m)\n      end\n    end\n  end\nend\n";
    qfformulawrite "\n;; (QBF-EFA2.2) Conditions des actions (transition feuille -> noeud)\n\n\\\and\nbigand $i in [1..$depth]:\n  bigand $A in $O:\n    bigand $f in $Cond($A):\n      not $A($i,1)\n      or $f(0,$nodewidth)\n      or b($i)\n      or bigor $j in [1..$i-1]:\n         not b($j)\n      end\n    end\n  end\nend\n";
    qfformulawrite "\n;; (QBF-EFA2.3) Conditions des actions (transition noeud -> feuille)\n\n\\\and\nbigand $i in [1..$depth]:\n  bigand $A in $O:\n    bigand $f in $Cond($A):\n      not $A(0,1)\n      or $f($i,$nodewidth)\n      or not b($i)\n      or bigor $j in [1..$i-1]:\n         b($j)\n      end\n    end\n  end\nend\n";
    qfformulawrite "\n;; Conditions des actions (in node)\n\n\\\and\nbigand $i in [0..$depth]:\n  bigand $m in [2..$nodewidth]:\n    bigand $A in $O:\n      bigand $f in $Cond($A):\n        not $A($i,$m)\n        or $f($i,$m-1)\n      end\n    end\n  end\nend";
    qfformulawrite "\n;; (QBF-EFA3.1.0) Frames-Axiomes d'ajout (état initial)\n\n\\\and bigand $f in ($F diff $I):\n  not $f(0,1)\n  or bigor $A in $O when ($f in $Add($A)) and ($Cond($A) subset $I):\n     $A(0,1)\n  end\n  or bigor $i in [1..$depth]:\n    b($i)\n  end\nend\n";
    qfformulawrite (Printf.sprintf "\n;; (QBF-EFA3.1.1) Frames-axiomes d'ajout (transition feuille -> noeud)\n\n%s" (efaprint "$f(0,$nodewidth)" "not $f($i,1)" "Add" "$A($i,1)" "b($i)" "not b($j)"));
    qfformulawrite (Printf.sprintf "\n;; (QBF-EFA3.1.2) Frames-axiomes d'ajout (transition noeud -> feuille)\n\n%s" (efaprint "$f($i,$nodewidth)" "not $f(0,1)" "Add" "$A(0,1)" "not b($i)" "b($j)"));
    qfformulawrite "\n;; Frames-axiomes d'ajouts (in node)\n\\\and\nbigand $i in [0..$depth]:\n  bigand $m in [2..$nodewidth]:\n    bigand $f in $F:\n      $f($i,$m-1) or not $f($i,$m)\n      or bigor $A in $O when $f in $Add($A):\n         $A($i,$m)\n      end  \n    end\n  end\nend\n";
    qfformulawrite "\n;; (QBF-EFA3.2.0) Frames-Axiomes de retrait (état initial)\n\n\\\and bigand $f in $I:\n  $f(0,1)\n  or bigor $A in $O when ($f in $Del($A)) and ($Cond($A) subset $I):\n     $A(0,1)\n  end\n  or bigor $i in [1..$depth]:\n    b($i)\n  end\nend\n";
    qfformulawrite (Printf.sprintf "\n;; (QBF-EFA3.2.1) Frames-axiomes de retrait (transition feuille -> noeud)\n\n%s" (efaprint "not $f(0,$nodewidth)" "$f($i,1)" "Del" "$A($i,1)" "b($i)" "not b($j)"));
    qfformulawrite (Printf.sprintf "\n;; (QBF-EFA3.2.2) Frames-axiomes de retrait (transition noeud -> feuille)\n\n%s" (efaprint "not $f($i,$nodewidth)" "$f(0,1)" "Del" "$A(0,1)" "not b($i)" "b($j)"));
    qfformulawrite "\n;; Frames-axiomes de retrait (in node)\n\\\and\nbigand $i in [0..$depth]:\n  bigand $m in [2..$nodewidth]:\n    bigand $f in $F:\n      not $f($i,$m-1) or $f($i,$m)\n      or bigor $A in $O when $f in $Del($A):\n         $A($i,$m)\n      end  \n    end\n  end\nend";
    qfformulawrite "\n;; (QBF-EFA4) Mutex (Forall-step semantics)\n\n\\\and\nbigand $i in [0..$depth]:\n  bigand $m in [1..$nodewidth]:\n    bigand $A in $O:\n      bigand $f in $Cond($A):\n        bigand $B in $O when $A!=$B and $f in $Del($B):\n          not $A($i,$m) or not $B($i,$m)\n        end\n      end\n    end\n  end\nend\n";
 Unix.close qfformulafile;
end else if encoding == 100 then (* option SAT-EFA *)
begin
 let qfformulafile = Unix.openfile "solvedata/in.qfformula.txt" [Unix.O_TRUNC;Unix.O_CREAT;Unix.O_WRONLY] 0o640 in
 let qfformulawrite s =
   ignore (Unix.write qfformulafile (Bytes.of_string s) 0 (String.length s)) in 
    qfformulawrite "\n;; (SAT-EFA1) Etat initial et but\n\nbigand $f in $I: $f(0) end\nbigand $f in ($F diff $I): not $f(0) end\nbigand $f in $G: $f($length) end\n";
    qfformulawrite "\n;; (SAT-EFA2) Conditions et effets des actions\n\nbigand $i in [1..$length]:\n  bigand $a in $O:\n    ($a($i) =>\n      ((bigand $f in $Cond($a): $f($i-1) end)\n        and\n        (bigand $f in $Add($a): $f($i) end)\n        and\n        (bigand $f in $Del($a): (not $f($i)) end)))\n  end\nend\n";
    qfformulawrite "\n;; (SAT-EFA3.1) Frames-axiomes de retrait\n\nbigand $i in [1..$length]:\n  bigand $f in $F:\n    ($f($i-1) and not $f($i))\n    => (bigor $a in $O when $f in $Del($a): $a($i) end)\n  end\nend\n";
    qfformulawrite "\n;; (SAT-EFA3.2) Frames-axiomes d'ajout\n\nbigand $i in [1..$length]:\n  bigand $f in $F:\n    (not $f($i-1) and $f($i))\n    => (bigor $a in $O when $f in $Add($a): $a($i) end)\n  end\nend\n";
    qfformulawrite "\n;; (SAT-EFA4) Mutex (Forall-step semantics)\nbigand $i in [1..$length]:\n  bigand $a1 in $O:\n    bigand $f in $Cond($a1):\n      bigand $a2 in $O when ($a1 != $a2) and ($f in $Del($a2)):\n        (not $a1($i) or not $a2($i))\n      end\n    end\n  end\nend\n";
 Unix.close qfformulafile;
end else if encoding == 103 then (* option SAT-OPEN *)
begin
 let qfformulafile = Unix.openfile "solvedata/in.qfformula.txt" [Unix.O_TRUNC;Unix.O_CREAT;Unix.O_WRONLY] 0o640 in
 let qfformulawrite s =
   ignore (Unix.write qfformulafile (Bytes.of_string s) 0 (String.length s)) in 
    qfformulawrite "\n;; Ouverture des conditions des actions\n\nbigand $i in [1..$length]:\n  bigand $A in $O:\n    $A($i) => bigand $f in $Cond($A): open($f,$i) end\n  end\nend\n";
    qfformulawrite "\n;; Ouverture des buts\n\nbigand $f in $G:\n  open($f,$length)\n  or bigor $A in $O when $f in $Add($A):\n    $A($length)\n  end\nend\n";
    qfformulawrite "\n;; Fermeture des conditions qui ne sont pas dans I\n\nbigand $f in $F diff $I: not open($f,1) end\n";
    qfformulawrite "\n;; Fermeture des conditions ouvertes\n\nbigand $i in [2..$length]:\n  bigand $f in $F:\n    open($f,$i)\n    => (open($f,$i-1)\n    or bigor $A in $O when $f in $Add($A):\n      $A($i-1)\n    end)\n  end\nend\n";
    qfformulawrite "\n;; Protection des conditions ouvertes\n\nbigand $i in [2..$length]:\n  bigand $f in $F:\n    open($f,$i) => bigand $A in $O when $f in $Del($A):\n      not $A($i-1)\n    end\n  end\nend\n";
    qfformulawrite "\n;; Mutex\n\nbigand $i in [1..$length]:\n  bigand $A in $O:\n    bigand $f in ($Add($A) union $Cond($A)):\n      bigand $B in $O when $A!=$B and $f in $Del($B):\n        not $A($i) or not $B($i)\n      end\n    end\n  end\nend\n";
 Unix.close qfformulafile;
end else if encoding == 150 then (* option SELECT-SAT-EFA *)
begin
 let qfformulafile = Unix.openfile "solvedata/in.qfformula.txt" [Unix.O_TRUNC;Unix.O_CREAT;Unix.O_WRONLY] 0o640 in
 let qfformulawrite s =
   ignore (Unix.write qfformulafile (Bytes.of_string s) 0 (String.length s)) in 
    qfformulawrite "\n;; (SELECT-SAT-EFA1) Etat initial et but\n\nbigand $f in $I: $f(0) end\nbigand $f in ($F diff $I): not $f(0) end\nbigand $f in $G: $f($length) end\n";
    qfformulawrite "\n;; (SELECT-SAT-EFA2) Conditions et effets des actions\n\nbigand $i in [1..$length]:\n  bigand $a in $O:\n    ($a($i) =>\n      ((bigand $f in $Cond($a): $f($i-1) end)\n        and\n        (bigand $f in $Add($a): $f($i) end)\n        and\n        (bigand $f in $Del($a): (not $f($i)) end)))\n  end\nend\n";
    qfformulawrite "\n;; (SELECT-SAT-EFA3.1) Frames-axiomes de retrait\n\nbigand $i in [1..$length]:\n  bigand $f in $F:\n    ($f($i-1) and not $f($i))\n    => (bigor $a in $O when $f in $Del($a): $a($i) end)\n  end\nend\n";
    qfformulawrite "\n;; (SELECT-SAT-EFA3.2) Frames-axiomes d'ajout\n\nbigand $i in [1..$length]:\n  bigand $f in $F:\n    (not $f($i-1) and $f($i))\n    => (bigor $a in $O when $f in $Add($a): $a($i) end)\n  end\nend\n";
    qfformulawrite "\n;; (SELECT-SAT-EFA4) Mutex (Forall-step semantics)\nbigand $i in [1..$length]:\n  bigand $a1 in $O:\n    bigand $f in $Cond($a1):\n      bigand $a2 in $O when ($a1 != $a2) and ($f in $Del($a2)):\n        (not $a1($i) or not $a2($i))\n      end\n    end\n  end\nend\n";
 Unix.close qfformulafile;
end else if encoding == 203 then (* option SMT-OPEN *)
begin
 let qfformulafile = Unix.openfile "solvedata/in.qfformula.txt" [Unix.O_TRUNC;Unix.O_CREAT;Unix.O_WRONLY] 0o640 in
 let qfformulawrite s =
   ignore (Unix.write qfformulafile (Bytes.of_string s) 0 (String.length s)) in
    qfformulawrite "\n;; Ouverture des conditions des actions\n\nbigand $i in [1..$length]:\n  bigand $A in $O:\n    $A($i) => bigand $f in $Cond($A):\n      open($f,$i)\n      \\\and (t($A,$i) - 0.0 >= t_s_open($f,$i) - $t_cond_begin($f,$A))\n      \\\and (t($A,$i) - 0.0 <= t_e_open($f,$i) - $t_cond_begin($f,$A))\n    end\n  end\nend\n";
    qfformulawrite "\n;; Ouverture des buts\n\nbigand $f in $G:\n  open($f,$length)\n  or bigor $A in $O when $f in $Add($A):\n    $A($length)\n    \\\and (t($A,$length) - 0.0 == t_s_open($f,$length) - $t_add_begin($A,$f))\n    \\\and (t_Goal - 0.0 == t_e_open($f,$length) - 0.0)\n  end\nend\n";
    qfformulawrite "\n;; Fermeture des conditions qui ne sont pas dans I\n\nbigand $f in $F diff $I:\n  not open($f,1)\nend\n";
    qfformulawrite "\n;; Fermeture des conditions par I\n\nbigand $f in $I:\n  open($f,1) => (t_Init - 0.0 == t_s_open($f,1) - 0.0)\nend\n";
    qfformulawrite "\n;; Fermeture des conditions ouvertes\n\nbigand $i in [2..$length]:\n  bigand $f in $F:\n    open($f,$i)\n    => ((open($f,$i-1)\n        \\\and (t_s_open($f,$i-1) - 0.0 == t_s_open($f,$i) - 0.0)\n        \\\and (t_e_open($f,$i-1) - 0.0 == t_e_open($f,$i) - 0.0))\n    \\\or bigor $A in $O when $f in $Add($A):\n      $A($i-1) and (t($A,$i-1) - 0.0 == t_s_open($f,$i) - $t_add_begin($A,$f))\n    end)\n  end\nend\n";
    qfformulawrite "\n;; Mutex temporellement étendues 1 (Protection des conditions ouvertes)\n\nbigand $i in [1..$length]:\n  bigand $j in [1..$length]:\n    bigand $f in $F:\n      bigand $A in $O when $f in $Del($A):\n        (open($f,$i) and $A($j)) =>\n          ((t($A,$j) - 0.0 <  t_s_open($f,$i) - $t_del_end($A,$f))\n          \\\or (t_e_open($f,$i) - $t_del_begin($A,$f) < t($A,$j) - 0.0))\n      end\n    end\n  end\nend\n";
    qfformulawrite "\n;; Mutex temporellement étendues 2 (Effets contradictoires)\n\nbigand $i in [1..$length]:\n  bigand $j in [1..$length]:\n    bigand $A in $O:\n      bigand $f in $Add($A):\n        bigand $B in $O when (($i!=$j) or ($A!=$B)) and $f in $Del($B):\n          ($A($i) and $B($j)) =>\n            ((t($A,$i) - $t_del_begin($B,$f) < t($B,$j) - $t_add_end($A,$f))\n            \\\or (t($B,$j) - $t_add_begin($A,$f) < t($A,$i) - $t_del_end($B,$f)))\n        end\n      end\n    end\n  end\nend\n";
    qfformulawrite "\n;; Mutex temporellement étendues 3 (Condition/Effet)\n\nbigand $i in [1..$length]:\n  bigand $j in [1..$length]:\n    bigand $A in $O:\n      bigand $f in $Cond($A):\n        bigand $B in $O when (($i!=$j) or ($A!=$B)) and $f in $Del($B):\n          ($A($i) and $B($j)) =>\n            ((t($A,$i) - $t_del_begin($B,$f) < t($B,$j) - $t_cond_end($f,$A))\n            \\\or (t($B,$j) - $t_cond_begin($f,$A) < t($A,$i) - $t_del_end($B,$f)))\n        end\n      end\n    end\n  end\nend\n";
    qfformulawrite "\n;; Bornes\n(t_Init == 0.0)\nbigand $i in [1..$length]:\n  bigand $A in $O:\n    $A($i) =>\n    (bigand $f in $Cond($A):\n      (t_Init - $t_cond_begin($f,$A) <= t($A,$i) - 0.0)\n      \\\and (t_Goal - $t_cond_end($f,$A) >= t($A,$i) - 0.0)\n    end\n    \\\and bigand $f in $Add($A):\n      (t_Init - $t_add_begin($A,$f) <= t($A,$i) - 0.0)\n      \\\and (t_Goal - $t_add_end($A,$f) >= t($A,$i) - 0.0)\n    end\n    \\\and bigand $f in $Del($A):\n      (t_Init - $t_del_begin($A,$f) <= t($A,$i) - 0.0)\n      \\\and (t_Goal - $t_del_end($A,$f) >= t($A,$i) - 0.0)\n    end)\n    \\\and (not $A($i) => (t($A,$i) < t_Init - 1000.0))\n  end\nend\n";
    qfformulawrite "\n(t(A____Spy___,1) - t_Init == 1.0)\n";
 Unix.close qfformulafile;
end else if encoding == 213 then (* option SMT-LINK *)
begin
 let qfformulafile = Unix.openfile "solvedata/in.qfformula.txt" [Unix.O_TRUNC;Unix.O_CREAT;Unix.O_WRONLY] 0o640 in
 let qfformulawrite s =
   ignore (Unix.write qfformulafile (Bytes.of_string s) 0 (String.length s)) in
   qfformulawrite ";; INIT VARIABLES\n\n(t(Init,0) == 0.0)\n(t(Spy_variable) - 1.0 == t(Init,0))\n";
   qfformulawrite "\n;; SMT-LINK.0 : Production des buts par liens causaux\nbigand $f in $G:\n  bigor $i in [1..$length]:\n    bigor $A in $O when $f in $Add($A):\n      Link($A,$i,$f,Goal,$length+1)\n    end\n    or bigor $A in [Init] when $f in $I: Link($A,0,$f,Goal,$length+1) end\n  end\nend\n";
   qfformulawrite "\n;; SMT-LINK.1 : Production des préconditions par liens causaux\n\nbigand $i in [1..$length]:\n  bigand $A in $O:\n    $A($i) => bigand $f in $Cond($A):\n      bigor $j in [1..$i-1]:\n        bigor $B in $O when $f in $Add($B):\n          Link($B,$j,$f,$A,$i)\n        end\n      end\n      or bigor $B in [Init] when $f in $I: Link($B,0,$f,$A,$i) end\n    end\n  end\nend\n";
   qfformulawrite "\n;; SMT-LINK.2 : Activation des actions et ordre partiel\n\nbigand $i in [1..$length]:\n  bigand $j in [1..$i-1]:\n    bigand $A in $O:\n      bigand $B in $O:\n        bigand $f in $Cond($A) inter $Add($B):\n          Link($B,$j,$f,$A,$i) =>\n          ($B($j) and $A($i) and ((t($B,$j) - $t_cond_begin($f,$A)) <= (t($A,$i) - $t_add_begin($B,$f))))\n        end\n      end\n    end  \n  end\nend\nbigand $i in [1..$length]:\n  bigand $A in $O:\n    bigand $f in $G inter $Add($A):\n      Link($A,$i,$f,Goal,$length+1) =>\n      ($A($i) and (t($A,$i) - 0.0 <= t(Goal,$length+1) - $t_add_begin($A,$f)))\n    end\n  end\nend\n";
   qfformulawrite "\n;; SMT-LINK.3 : Protection des liens causaux\n\nbigand $i in [1..$length]:\n  bigand $j in [1..$i-1]:\n    bigand $k in [1..$length]:\n      bigand $A in $O:\n        bigand $B in $O:\n          bigand $f in $Cond($A) inter $Add($B):\n            bigand $C in $O when ($i!=$k or $A!=$C) and $f in $Del($C):\n              (Link($B,$j,$f,$A,$i) and $C($k)) =>\n              ((t($C,$k) - $t_add_begin($B,$f) < t($B,$j) - $t_del_end($C,$f))\n              or (t($A,$i) - $t_del_begin($C,$f) < t($C,$k) - $t_cond_end($f,$A)))\n            end\n          end\n        end\n      end\n    end  \n  end\nend\nbigand $i in [1..$length]:\n  bigand $A in $O:\n    bigand $f in $Cond($A) inter $I:\n      bigand $j in [1..$length]:\n        bigand $B in $O when ($i!=$j or $A!=$B) and $f in $Del($B):\n          (Link(Init,0,$f,$A,$i) and $B($j)) =>\n          (t($A,$i) - $t_del_begin($B,$f) < t($B,$j) - $t_cond_end($f,$A))\n        end\n      end\n    end\n  end\nend\nbigand $i in [1..$length]:\n  bigand $A in $O:\n    bigand $f in $Add($A) inter $G:\n      bigand $j in [1..$length]:\n        bigand $B in $O when ($i!=$j or $A!=$B) and $f in $Del($B):\n          (Link($A,$i,$f,Goal,$length+1) and $B($j)) =>\n          (t($B,$j) - $t_add_begin($A,$f) < t($A,$i) - $t_del_end($B,$f))\n        end\n      end\n    end\n  end\nend\nbigand $i in [1..$length]:\n  bigand $f in $I inter $G:\n    bigand $A in $O when $f in $Del($A):\n      (not Link(Init,0,$f,Goal,$length+1)) or (not $A($i))\n    end\n  end\nend\n";
   qfformulawrite "\n;; SMT-LINK.4 : Prévention des interactions négatives\n\nbigand $i in [1..$length]:\n  bigand $j in [1..$length]:\n    bigand $A in $O:\n      bigand $B in $O when $i!=$j or $A!=$B:\n        bigand $f in $Add($A) inter $Del($B):\n          ($A($i) and $B($j)) =>\n          ((t($A,$i) - $t_del_begin($B,$f) < t($B,$j) - $t_add_end($A,$f))\n          or (t($B,$j) - $t_add_begin($A,$f) < t($A,$i) - $t_del_end($B,$f)))\n        end\n      end\n    end\n  end\nend\n";
   qfformulawrite "\n;; Bornes\n\nbigand $i in [1..$length]:\n  bigand $A in $O:\n    $A($i) =>\n    (bigand $f in $Cond($A):\n      (t(Init,0) - $t_cond_begin($f,$A) <= t($A,$i) - 0.0)\n      \\\and (t(Goal,$length+1) - $t_cond_end($f,$A) >= t($A,$i) - 0.0)\n    end\n    \\\and bigand $f in $Add($A):\n      (t(Init,0) - $t_add_begin($A,$f) <= t($A,$i) - 0.0)\n      \\\and (t(Goal,$length+1) - $t_add_end($A,$f) >= t($A,$i) - 0.0)\n    end\n    \\\and bigand $f in $Del($A):\n      (t(Init,0) - $t_del_begin($A,$f) <= t($A,$i) - 0.0)\n      \\\and (t(Goal,$length+1) - $t_del_end($A,$f) >= t($A,$i) - 0.0)\n    end)\n    \\\and (not $A($i) => (t($A,$i) < t(Init,0) - 1.0))\n  end\nend\n";
 Unix.close qfformulafile;
end else if encoding == 1100 then (* option SAT encoding file *)
begin
   let copyfile = (command (Printf.sprintf "cp %s solvedata/in.qfformula.txt" inputencoding)) in
   if copyfile != 0 then exit copyfile;
end;


(* Génération des ensembles à partir du problème de planification *)

 let setsfile = Unix.openfile "solvedata/in.sets.txt" [Unix.O_TRUNC;Unix.O_CREAT;Unix.O_WRONLY] 0o640 in
 let setswrite s =
   ignore (Unix.write setsfile (Bytes.of_string s) 0 (String.length s)) in  
    let changedash s = (String.map (fun c -> if c=='-' then '_' else c) s) in
    let string_of_fluent_array fluents = Utils.string_of_array "," Utils.to_string fluents in
    setswrite (Printf.sprintf "\n$I = [%s]" (string_of_fluent_array self#init_state));
    setswrite (Printf.sprintf "\n\n$G = [%s]" (string_of_fluent_array self#goal));
    setswrite (Printf.sprintf "\n\n$O = [%s]" (string_of_fluent_array 
      (Array.of_list
        (Array.fold_left (fun l a -> (* if (a#level <= rpg_max_level) && (a#maxlevel >= 0) then *) a::l (* else l*)) [] self#actions)
      )
     ));
    setswrite (Printf.sprintf "\n\n$F = [%s]" (string_of_fluent_array self#fluents));
    setswrite (Printf.sprintf "\n\n$Fp = [%s]\n" (Utils.string_of_list "," Utils.to_string (Array.fold_left (fun l f -> if f#consumers <> [| |] then f::l else l) [] self#fluents)));
    setswrite (Printf.sprintf "\n$Fa = [%s]\n" (Utils.string_of_list "," Utils.to_string (Array.fold_left (fun l f -> if f#producers <> [| |] then f::l else l) [] self#fluents)));
    setswrite (Printf.sprintf "\n$Fd = [%s]\n" (Utils.string_of_list "," Utils.to_string (Array.fold_left (fun l f -> if f#deleters <> [| |] then f::l else l) [] self#fluents)));
    setswrite (Printf.sprintf "\n");
    Array.iter (fun a -> (* if (a#level <= rpg_max_level) && (a#maxlevel >= 0) then *)
     begin
      setswrite (Printf.sprintf "\n%s" a#to_complete_string);
if encoding >= 200 then begin (* SMT Temporal Planning *)
      Array.iter (fun (f,timedata) ->
          setswrite (Printf.sprintf "$t_cond_begin(%s,%s) = %f\n" (changedash f#to_string) (changedash a#to_string) (fst timedata#timeset));
          setswrite (Printf.sprintf "$t_cond_end(%s,%s) = %f\n" (changedash f#to_string) (changedash a#to_string) (snd timedata#timeset))
      ) a#iprec ;
      Array.iter (fun (f,timedata) ->
          setswrite (Printf.sprintf "$t_add_begin(%s,%s) = %f\n" (changedash a#to_string) (changedash f#to_string) (fst timedata#timeset));
          setswrite (Printf.sprintf "$t_add_end(%s,%s) = %f\n" (changedash a#to_string) (changedash f#to_string) (snd timedata#timeset))
      ) a#iadd ;
      Array.iter (fun (f,timedata) ->
          setswrite (Printf.sprintf "$t_del_begin(%s,%s) = %f\n" (changedash a#to_string) (changedash f#to_string) (fst timedata#timeset));
          setswrite (Printf.sprintf "$t_del_end(%s,%s) = %f\n" (changedash a#to_string) (changedash f#to_string) (snd timedata#timeset))
      ) a#idel ;
end (* end SMT Temporal Planning *)

     end
    ) self#actions ;
 Unix.close setsfile;



(** START QBFPLAN-SOLVE **)
if encoding < 100 then
begin


let touistsolveqbf maxdepth branchdepth addatom timeout =
  let touistcode = ref 0 in
  genquantifiers maxdepth branchdepth;
  let atomsfiles = if branchdepth <= maxdepth then (Printf.sprintf " solvedata/in.atoms%d.txt" branchdepth) else "" in
(* Utils.print "TouIST solve / depth = %d / branch = %d / atomsfiles = %s / addatom = %s\n" maxdepth branchdepth atomsfiles addatom; *)
Utils.print "--- TouIST solve (QBF) / branch atom = %s ---\n" addatom;
flush stdout; flush stderr;
let timeout_cmd = if timeout>0. then "timeout "^string_of_float timeout^"" else "" in
(* INERNAL SOLVER *) (* ignore (command (Printf.sprintf "(echo '$depth = %d' ; cat solvedata/in.sets.txt solvedata/in.quantifiers.txt ; cat solvedata/in.qfformula.txt%s ; echo '%s') | timeout %d touist --qbf --solve - > solvedata/out.emodel.txt 2> solvedata/out.touisterr.txt" maxdepth atomsfiles addatom)); *)
(* EXTERNAL SOLVER: *)  
if solvernum == 0 then touistcode := (command (Printf.sprintf "(echo '$depth = %d' ; cat solvedata/in.sets.txt solvedata/in.quantifiers.txt ; cat solvedata/in.qfformula.txt%s ; echo '%s') | %s touist --qbf -v --solver 'depqbf --qdo --no-dynamic-nenofex' - > solvedata/out.emodel.txt 2> solvedata/out.touisterr.txt" maxdepth atomsfiles addatom timeout_cmd));
if solvernum == 1 then touistcode := (command (Printf.sprintf "(echo '$depth = %d' ; cat solvedata/in.sets.txt solvedata/in.quantifiers.txt ; cat solvedata/in.qfformula.txt%s ; echo '%s') | %s touist --qbf -v --solver rareqs - > solvedata/out.emodel.txt 2> solvedata/out.touisterr.txt" maxdepth atomsfiles addatom timeout_cmd));
if solvernum == 2 then touistcode := (command (Printf.sprintf "(echo '$depth = %d' ; cat solvedata/in.sets.txt solvedata/in.quantifiers.txt ; cat solvedata/in.qfformula.txt%s ; echo '%s') | %s touist --qbf -v --solver './solvers/caqe-mac --partial-assignments' - > solvedata/out.emodel.txt 2> solvedata/out.touisterr.txt" maxdepth atomsfiles addatom timeout_cmd));
if solvernum == 3 then touistcode := (command (Printf.sprintf "(echo '$depth = %d' ; cat solvedata/in.sets.txt solvedata/in.quantifiers.txt ; cat solvedata/in.qfformula.txt%s ; echo '%s') | %s touist --qbf -v --solver 'qute --partial-certificate --prefix-mode' - > solvedata/out.emodel.txt 2> solvedata/out.touisterr.txt" maxdepth atomsfiles addatom timeout_cmd));
(* FICHIER DEBUG: *)  ignore (command (Printf.sprintf "(echo '$depth = %d' ; cat solvedata/in.sets.txt solvedata/in.quantifiers.txt ; cat solvedata/in.qfformula.txt%s ; echo '%s') > debug.touistl" maxdepth atomsfiles addatom));
  ignore (command (Printf.sprintf "((cat solvedata/out.emodel.txt | grep '1 ' | sed -e 's/1 /and /') ; (cat solvedata/out.emodel.txt | grep '0 ' | sed -e 's/0 /and not /')) > solvedata/in.atoms%d.txt" (branchdepth - 1)));
if branchdepth <= maxdepth then ignore (command (Printf.sprintf "cat solvedata/in.atoms%d.txt | grep 'and A_' | grep '\\((%d\\)\\(,\\|)\\)'" (branchdepth - 1) (branchdepth - 1)));
if (encoding == 1) && (branchdepth <= maxdepth) then ignore (command (Printf.sprintf "cat solvedata/in.atoms%d.txt | grep 'and A_' | grep '\\((%d\\)\\(,\\|)\\)'" (branchdepth - 1) (branchdepth)));
(*for i = maxdepth downto branchdepth - 1 do
  command (Printf.sprintf "cat solvedata/out.emodel.txt | grep '? ' | grep '\\((\\|,\\)%d)'" i) |> ignore;
  if 0 = command (Printf.sprintf "cat solvedata/out.emodel.txt | grep '? ' | grep '\\((\\|,\\)%d)' | grep '\\(A_\\|F_\\)' >/dev/null" i)
  then (Printf.eprintf "Solver did not quantify one of the outer-existentially-quantified variable; cannot continue!";exit 100); (* when some outer quantified variable is not quantified *)
  flush stdout; flush stderr;
done;*)
!touistcode
in

let treedepthbound = Array.length pdata#fluents
in
Utils.print "Maximum tree depth: |Fluents|=%d.\n" treedepthbound;
flush stdout; flush stderr;

let treedepth = ref incmin in
let qbftrue = ref false in

let plansat () =
let time_start = Unix.gettimeofday () (* in seconds *) in
while (!treedepth < treedepthbound) && (not !qbftrue) do
  treedepth := !treedepth + 1;
  Utils.print "Searching solution at depth %d...\n" !treedepth;
  flush stdout; flush stderr;
  (* We want to use the shell command 'timeout'; 'timeout' takes a positive
     integer as first argument (time_left). If we put 0, it means
     'no timeout' so I put a 1 second timeout instead to force the timeout. *)
  match touistsolveqbf !treedepth (!treedepth + 1) "" (time_left time_start) with
  | 0 -> qbftrue:=true
  | 8 -> qbftrue:=false
  | exception Timeout -> (Utils.eprint "Timeout when searching solution of lenght %d.\n" !treedepth; exit 124)
  | 124 -> (* code returned by 'timeout' *) (Utils.eprint "Timeout when searching solution at depth %d.\n" !treedepth; exit 124)
  | touistcode -> (Utils.eprint "Solver error %d.\n" touistcode; exit touistcode)
(**  let resultfile = (Unix.openfile "solvedata/out.touisterr.txt" [Unix.O_RDONLY] 0o640) in
  let c = Unix.in_channel_of_descr resultfile in
  let result = try input_line c with End_of_file -> "sat" in
(* INTERNAL SOLVER *)  (* if (String.compare result "unsat") != 0 then qbftrue:=true; *)
  if solvernum == 0 then (* DEPQBF EXTERNAL SOLVER *) if (String.compare result "Command 'depqbf --qdo --no-dynamic-nenofex' returned code 20 and no lines beginning with 'v'") != 0 then qbftrue:=true;
  if solvernum == 1 then if (String.compare result "Command 'rareqs' returned code 127 and no lines beginning with 'v'") != 0 then qbftrue:=true;
**)
done in

let (plansat_time,_) = Utils.my_time2bis (fun () -> plansat ()) in
Utils.print "Plan existence time (PLANSAT): %.2f\n" plansat_time;
(* Show number of literals & clauses *) ignore @@ command ("cat solvedata/out.touisterr.txt >&2");

  let rec extract depth time_start =
    match depth with
    | 0 -> ();
    | i -> begin
             touistsolveqbf !treedepth i (Printf.sprintf "and not b(%d)" i) (time_left time_start) |> ignore;
             extract (i - 1) time_start;
             touistsolveqbf !treedepth i (Printf.sprintf "and b(%d)" i) (time_left time_start) |> ignore;
             extract (i - 1) time_start;
           end;
  in

let extract_time = ref 0.0 in
if !qbftrue then
begin
  Utils.print "Solution found at depth %d.\n" !treedepth; flush stdout; flush stderr;
  ignore (command (Printf.sprintf "cat solvedata/in.atoms%d.txt | grep 'and A_' | grep '\\((%d\\)\\(,\\|)\\)'" !treedepth !treedepth));
  flush stdout; flush stderr;
  try let (extr_time,_) = Utils.my_time2bis (fun () -> extract !treedepth (Unix.gettimeofday ())) in extract_time := extr_time
  with Timeout -> (Utils.eprint "Timeout when extracting\n"; exit 125)
end else Utils.eprint "No solution at maximum depth bound.\nThe planning problem does not have any solution.\n";
Utils.print "Plan existence time (PLANSAT): %.2f\n" plansat_time;
if !qbftrue then Utils.print "Plan extract time: %.2f\n" !extract_time;
flush stdout; flush stderr;

exit 0;
end;
(** END QBFPLAN-SOLVE **)


(** START SATPLAN-SOLVE **)
if (encoding < 200) || (encoding>=1000) then
begin

let touistsolvesat length timeout =
  let touistcode = ref 0 in
  Utils.print "--- TouIST solve (SAT) / length = %d ---\n" length;
  flush stdout; flush stderr;
  let timeout_cmd = if timeout>0. then "timeout "^ string_of_float timeout else "" in
  if solvernum == 0 then touistcode := (command (Printf.sprintf "(echo '$length = %d' ; cat solvedata/in.sets.txt ; cat solvedata/in.qfformula.txt) | %s touist --sat --solve - > solvedata/out.emodel.txt 2> solvedata/out.touisterr.txt" length timeout_cmd));
  if solvernum == 101 then touistcode := (command (Printf.sprintf "(echo '$length = %d' ; cat solvedata/in.sets.txt ; cat solvedata/in.qfformula.txt) | %s touist --sat --solver 'glucose -model' - > solvedata/out.emodel.txt 2> solvedata/out.touisterr.txt" length timeout_cmd));
  if solvernum == 102 then touistcode := (command (Printf.sprintf "(echo '$length = %d' ; cat solvedata/in.sets.txt ; cat solvedata/in.qfformula.txt) | %s touist --sat --solver 'glucose-syrup -model' - > solvedata/out.emodel.txt 2> solvedata/out.touisterr.txt" length timeout_cmd));
  if solvernum == 103 then touistcode := (command (Printf.sprintf "(echo '$length = %d' ; cat solvedata/in.sets.txt ; cat solvedata/in.qfformula.txt) | %s touist --sat --solver 'picosat --partial' - > solvedata/out.emodel.txt 2> solvedata/out.touisterr.txt" length timeout_cmd));
  if solvernum == 104 then touistcode := (command (Printf.sprintf "(echo '$length = %d' ; cat solvedata/in.sets.txt ; cat solvedata/in.qfformula.txt) | %s touist --sat --solver 'lingeling' - > solvedata/out.emodel.txt 2> solvedata/out.touisterr.txt" length timeout_cmd));
  (* FICHIER DEBUG: *) ignore (command (Printf.sprintf "(echo '$length = %d' ; cat solvedata/in.sets.txt ; cat solvedata/in.qfformula.txt) > debug.touistl" length));
  !touistcode
in

let planlengthbound = 256 (* (Array.length pdata#fluents) * (Array.length pdata#fluents) *)
in
Utils.print "Maximum plan length: 2^|Fluents|=%d.\n" planlengthbound;
flush stdout; flush stderr;

let planlength = ref incmin in
let sattrue = ref false in
let time_start = Unix.gettimeofday () in
while (!planlength < planlengthbound) && (not !sattrue) do
  if incrmode <= 1 then planlength := !planlength + 1
  else if !planlength == 0 then planlength := 1
       else planlength := !planlength * incrmode;
  Utils.print "Searching solution with length %d...\n" !planlength;
  flush stdout; flush stderr;
  match touistsolvesat !planlength (time_left time_start) with
  | 0 -> sattrue:=true
  | 8 -> sattrue:=false
  | exception Timeout -> (Utils.eprint "Timeout when searching solution of lenght %d.\n" !planlength; exit 124)
  | 124 -> (Utils.eprint "Timeout when searching solution of lenght %d.\n" !planlength; exit 124)
  | touistcode -> begin Utils.eprint "Solver error %d.\n" touistcode; exit touistcode; end;
(*  let resultfile = (Unix.openfile "solvedata/out.touisterr.txt" [Unix.O_RDONLY] 0o640) in
  let c = Unix.in_channel_of_descr resultfile in
  let result = try input_line c with End_of_file -> "sat" in
  if (String.compare result "unsat") != 0 then sattrue:=true; *)
done;

if !sattrue then
begin
  Utils.print "Solution found at length %d.\n" !planlength; flush stdout; flush stderr;
  for i = 1 to !planlength do
    ignore (command (Printf.sprintf "cat solvedata/out.emodel.txt | grep '1 A_' | grep '(%d)'" i));
    flush stdout; flush stderr;
  done;
end else Utils.eprint "No solution at maximum length bound.\nThe planning problem does not have any solution.\n";

exit 0;
end;
(** END SATPLAN-SOLVE **)

(** START SMTPLAN-SOLVE **)
if encoding < 300 then
begin

let touistsolvesat length timeout : int =
  Utils.print "--- TouIST solve (SMT) / length = %d ---\n" length;
  flush stdout; flush stderr;
  let timeout_cmd = if timeout>0. then "timeout "^ string_of_float timeout else "" in
  let status = command (Printf.sprintf "(echo '$length = %d' ; cat solvedata/in.sets.txt ; cat solvedata/in.qfformula.txt) | %s touist --smt QF_RDL --solve - > solvedata/out.emodel.txt 2> solvedata/out.touisterr.txt" length timeout_cmd) in
  (* FICHIER DEBUG: *) ignore (command (Printf.sprintf "(echo '$length = %d' ; cat solvedata/in.sets.txt ; cat solvedata/in.qfformula.txt) > debug.touistl" length));
  status
in

let planlengthbound = 256 (* (Array.length pdata#fluents) * (Array.length pdata#fluents) *)
in
Utils.print "Maximum plan length: 2^|Fluents|=%d.\n" planlengthbound;
flush stdout; flush stderr;

let planlength = ref 0 in
let sattrue = ref false in
let time_start = Unix.gettimeofday () in
while (!planlength < planlengthbound) && (not !sattrue) do
  planlength := !planlength + 1;
  Utils.print "Searching solution with length %d...\n" !planlength;
  flush stdout; flush stderr;
  match touistsolvesat !planlength (time_left time_start) with
  | 0 -> sattrue := true
  | 8 -> sattrue := false
  | exception Timeout -> (Utils.eprint "Timeout when searching solution of lenght %d.\n" !planlength; exit 124)
  | 124 -> (Utils.eprint "Timeout when searching solution of lenght %d.\n" !planlength; exit 124)
  | touistcode -> begin Utils.eprint "Solver error %d.\n" touistcode; exit touistcode; end
done;

if !sattrue then
begin
  Utils.print "Solution found at length %d.\n" !planlength; flush stdout; flush stderr;
  for i = 1 to !planlength do
    ignore (command (Printf.sprintf "cat solvedata/out.emodel.txt | grep '1 A_' | grep '(%d)'" i));
    ignore (command (Printf.sprintf "cat solvedata/out.emodel.txt | sed -e '/^-/ d' | grep 't(A_' | grep ',%d)'" i));
    flush stdout; flush stderr;
  done;
end else Utils.eprint "No solution at maximum length bound.\nThe planning problem does not have any solution.\n";

exit 0;
end;
(** END SMTPLAN-SOLVE **)


(* END QBF-TOUISTPLAN without GP *)
exit 0;


************************ *)






let timedata_null = new Timedata.t (0.0,0.0) 0 in

let action_init =
  self#create_action "Init" [| |] 0.0 0 [| |] [| |] (Array.of_list (Array.fold_left (fun x f -> (f,f#atom#timedata(*timedata_null*)) :: x) [] pdata#init_state)) [| |]
in

let action_goal =
  self#create_action "Goal" [| |] 0.0 0 (Array.of_list (Array.fold_left (fun x f -> (f,timedata_null) :: x) [] pdata#goal)) [| |] [| |] [| |]
in



  (* print_agenda agenda; *)


    let expand_rpg = (* Expanding the Temporal Relaxed Planning Graph to next level *)
      Utils.print "Expanding the Temporal Relaxed Planning Graph from level %d to level %d ...\n" rpg_max_level (succ rpg_max_level);
        Array.iter (fun a -> (if (a#level > rpg_max_level) &&
          (Array.fold_left (fun b prec -> b &&
            Array.fold_left (fun c f -> c ||
              ((f#atom#equal prec#atom) && (f#level <= rpg_max_level)))
            false pdata#fluents)
          true a#prec)
          then begin
               a#set_level (succ rpg_max_level);
               Array.iter (fun f ->
                   if (f#level > rpg_max_level) && (List.exists (fun add ->
                                 (f#atom#equal add#atom))
                                 (Array.to_list a#add))
                   then f#set_level (succ rpg_max_level))
               pdata#fluents;
               Array.iter (fun f ->
                   if (f#neglevel > rpg_max_level) && (List.exists (fun del ->
                                 (f#atom#equal del#atom))
                                 (Array.to_list a#del))
                   then f#set_neglevel (succ rpg_max_level))
               pdata#fluents;
               end))
          pdata#actions;
      rpg_max_level <- succ rpg_max_level;
 in
 expand_rpg;


end