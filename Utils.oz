%Author: Mehdi Dumoulin, EPL, UCL.
functor
import
   Parser
   Main
   Interpreter
   System
export
   NewActive
   NewPortObject
   PrepareArgProc
   ParserList
   GetIdFromIndex
   FindAllIndexFreeVars
   InsertRecurRecord
   CheckArity
   CheckStore
   SearchIndex
   SearchOneIndex
   FindIndexActualP
   CleanEnv
   CheckRecursifTerm
   PrepareStack
   FctSmart
define

   /* Function uses to use a port */
   fun{NewActive Class Init}
      Obj = {New Class Init}
      P
   in
      thread S in
	 {NewPort S P}
	 for M in S do {Obj M} end
      end
      proc {$ M} {Send P M} end
   end
   fun{NewPortObject Init Fun}
      proc {MsgLoop S1 State}
	 case S1 of Msg|S2 then
	    {MsgLoop S2 {Fun Msg State}}
	 [] nil then skip end
      end
      Sin
   in
      thread  {Cell.assign Main.listOfThreadInProcess {List.append @(Main.listOfThreadInProcess) [{Thread.this}]}} {MsgLoop Sin Init} end
     
      {NewPort Sin}
   end
   
   
   /*
   * Function which declare variables uses during exercises
   */
   fun{PrepareArgProc ExerciseNr}
      Rarg Ar
      fun{Loop L}
	 case L of nil then "Rep} end"
	 []H|T then
	    {Append "A" {Append {Int.toString H} {Append " " {Loop T}}}}
	 end
      end
      fun{Asign L}
	 case L of nil then " "
	 []H|T then Temp Type in
	    Type = {Value.type Rarg.H}
	    if Type == int then
	       Temp = {Int.toString Rarg.H}
	    elseif Type == float then
	       Temp = {Int.toString Rarg.H} 
	    elseif Type == atom then
	       Temp = {Int.toString Rarg.H}
	    elseif Type == tuple then
	       Temp = Rarg.H
	    else
	       Temp = {Value.toVirtualString Rarg.H 1000 1000}
	    end
	    {Append "A" {Append {Int.toString H} {Append " = " {Append Temp {Append " " {Asign T}}}}}}
	 end
      end
      fun{CreateLocal L T}
	 case L of nil then
	    if T == 0 then
	       {Append {Asign Ar} {Append "local Rep in " {CreateLocal L 1}}}
	    else
	       {Append " {" {Append {List.nth @(Main.nameProcEx) ExerciseNr} {Append " " {Loop Ar}}}}
	    end
	 []H|T then
	    {Append " local A" {Append  {Int.toString H} {Append " in " {Append {CreateLocal T 0} " end "}}}}
	 end
      end
   in
      Rarg = {List.nth @(Main.testInput) ExerciseNr}
      Ar = {Record.arity Rarg} 
      {CreateLocal Ar 0}
   end


   /*
   * Function who parses a list of tokens
   */
   fun{ParserList Lex Sol RFalse}
      fun{Loop Lex SolTemp RFalseT}
	 case Lex of nil then Sol = SolTemp RFalse = RFalseT  true
	 else B2 C2 RFalse2 in
	    B2 = {Parser.parser Lex C2 RFalse2}
	    {Wait B2}
	    if {Value.isFree C2} then
	       if B2 then
		  {And B2 {Loop nil SolTemp RFalseT}}
	       else
		  {And B2 {Loop nil SolTemp {Append RFalseT [RFalse2.1]}}}
	       end
	    else
	       if B2 then
		  {And B2 {Loop C2.2 {Append SolTemp [C2.1]} RFalseT}}
	       else
		  {And B2 {Loop C2.2 {Append SolTemp [C2.1]} {Append RFalseT [RFalse2.1]}}}
	       end
	    end
	 end
      end
   in
      {Loop Lex nil nil}
   end


   /* Return the ID corresponding to IndexVar in the environment */
   fun{GetIdFromIndex IndexVar Env}
      case Env of nil then nil
      []H#A|T then
	 if A == IndexVar then H
	 else {GetIdFromIndex IndexVar T}
	 end
      end
   end


   /* Insert recursively a record */
   proc{InsertRecurRecord L State Pstack Index}
      case L of nil then skip
      []I#V|T then R in
	 {Send Pstack index(V R)}
	 {List.nth State Index}.I = {List.nth State R}
	 {InsertRecurRecord T State Pstack Index}
      end
   end


   /* Return a list of index in the environment corresponding to list L of variable*/
   fun{FindAllIndexFreeVars L Pstack Prob}
      case L of nil then Prob=false nil
      []H|T then X End in
	 if {Not {List.member H Interpreter.fctImpl}} then
	    {Send Pstack indexWithEnd(H X End)}
	    {Wait End}
	    if {Value.isFree X} then
	       Prob = true nil
	    else
	       H#X|{FindAllIndexFreeVars T Pstack Prob}
	    end
	 else
	    {FindAllIndexFreeVars T Pstack Prob}
	 end
      end
   end


   
   fun{CheckArity Elem Ok Arity Ind State}
      case Arity of H|T then
	 if {System.eq Elem {List.nth State Ind}.H} then
	    Ok = true
	    H
	 else {CheckArity Elem Ok T Ind State}
	 end
      []nil then Ok = false nil
      end
   end

   
   fun{CheckStore Arity State Ind Rec}
      fun{Check2 I}
	 if I > Length then nil
	 else Ok R in
	    R = {CheckArity {List.nth State I} Ok Arity Ind State}
	    if Ok then Rec.R#I|{Check2 I+1}
	    else {Check2 I+1}
	    end
	 end
      end
      Length
   in
      Length = {List.length State}
      {Check2 1}
   end


   /* Search index in environment corresponding to ID1 and ID2*/
   proc{SearchIndex L Id1 Id2 I1 I2}
      proc{Search L Found}
	 if Found < 2 then
	    case L of nil then skip
	    []H|T then
	       if H.1 == Id1 then
		  I1 = H.2
		  {Search T Found+1}
	       elseif H.1 == Id2 then
		  I2 = H.2
		  {Search T Found+1}
	       else
		  {Search T Found}
	       end
	    end
	 else skip
	 end
      end
   in
      {Search L 0}
      if {Value.isFree I1} then
	 {Main.g printMessagePorI('Binding Analysis error')}
	 {Main.g printMessagePorI('Variable'#Id1#'Not introduced')}
      else
	 if {Value.isFree I2} then
	    {Main.g printMessagePorI('Binding Analysis error')}
	    {Main.g printMessagePorI('Variable'#Id2#'Not introduced')}
	 else
	    skip
	 end
      end
   end


   /* Search index in environment corresponding to ID*/
   proc{SearchOneIndex L Id I}
      proc{Search L}
	 case L of nil then skip
	 []H|T then
	    if H.1 == Id then
	       I = H.2
	    else
	       {Search T}
	    end
	 end
      end
   in
      {Search L}
      if {Value.isFree I} then
	 {Main.g printMessagePorI('Binding Analysis error')}
	 {Main.g printMessagePorI('Variable'#Id#'Not introduced')}
      else
	 skip
      end
   end


   /* Return a list with ID of Formal parameter with index of actual parameter */
   fun{FindIndexActualP L FormalParameter ActualParameter}
      Length
      fun{Loop L1 L2 Pos Length2}
	 if Length2 > Length then nil
	 else
	    case L1 of nil then nil
	    []H#P|T then
	       if {List.member H L2} then
		  case L2 of nil then {Loop T ActualParameter 1 Length2}
		  []H2|T2 then
		     if H2 == H then
			{List.nth FormalParameter Pos}#P|{Loop T ActualParameter 1 Length2+1}
		     else
			{Loop L1 T2 Pos+1 Length2}
		     end
		  end
	       else
		  {Loop T ActualParameter 1 Length2}
	       end
	    end
	 end
      end
   in
      Length = {List.length FormalParameter}
      {Loop L ActualParameter 1 1}
   end


   /* Function to avoid duplicates on the environment */
   fun{CleanEnv EnvToAdd EnvInit}
      fun{Loop L}
	 case L of nil then nil
	 []H|T then
	    if {List.member H EnvInit} then
	       {Loop T}
	    else H|{Loop T}
	    end
	 end
      end
   in
      {Loop EnvToAdd}
   end


   /* Procedure used to determine if a function is recursive
				     If yes, determine is the function is also tail recursive */
   proc{CheckRecursifTerm IndEnvExt NameFct Pstore Psmart}
      fun{CheckRecursif EnvExt Proc}
	 case EnvExt of nil then false
	 []H#P|T then
	    if H == NameFct then X in
	       {Send Pstore elem(P X)}
	       {Wait X}
	       Proc = X
	       true
	    else
	       {CheckRecursif T Proc}
	    end
	 end
      end
      fun{CheckTerminal Proc}
	 case Proc of keyAnd(S1 S2) then T in
	    T = {CheckTerminal S1}
	    if T == notfound then
	       {CheckTerminal S2}
	    else
	       {And {Not T} {CheckTerminal S2}}
	    end
	 []keyLocal(id(_ pos:_) pos:_ s:S) then T in
	    T = {CheckTerminal S}
	    if T == notfound then
	       false
	    else
	       T
	    end
	 []keyIf(id(_ pos:_) pos:_ S1 S2) then T in
	    T = {CheckTerminal S1}
	    if T == notfound then
	       {CheckTerminal S2}
	    else
	       {And T {CheckTerminal S2}}
	    end
	 []keyCase(_ _ S1 S2 pos:_) then T in
	    T = {CheckTerminal S1}
	    if T == notfound then
	       {CheckTerminal S2}
	    else
	       {And T {CheckTerminal S2}}
	    end
	 []keyApply(NameFct2 _ pos:_) then
	    NameFct2 == NameFct
	 else notfound
	 end
      end
      Proc
      EnvExt
   in
      {Send Pstore elem(IndEnvExt EnvExt)}
      if EnvExt == nil then skip
      else
	 if {CheckRecursif EnvExt.2 Proc} then
	    {Send Psmart addFct(NameFct)}
	    if {CheckTerminal Proc.1.2} then
	       {Main.g printMessagePorI({VirtualString.toAtom "Procedure: "#NameFct#" recursive terminal"})}
	    else
	       {Main.g printMessagePorI({VirtualString.toAtom "Warning procedure: "#NameFct#" not recursive terminal"})}
	    end
	 else
	    skip
	 end
      end
   end


   /* Prepare a stack with a new environment for each element of Program*/
   fun{PrepareStack Program}
      case Program of nil then nil
      []H|T then
	 semstack(stat:H env:nil)|{PrepareStack T}
      end
   end


   /* Analyse if a recursive function loop infinitely */
   fun{FctSmart Msg State}
      fun{FindIndex L X Pos}
	 case L of nil then ~1
	 []H|T then
	    if H == X then Pos
	    else {FindIndex T X Pos +1}
	    end
	 end
      end
      fun{AnalyseStack2 Stack Found}
	 case Stack of nil then Found
	 []H|T|P then
	    if {List.sub T H} then
	       {AnalyseStack2 T|P Found+1}
	    else {AnalyseStack2 T|P Found}
	    end
	 []_|T then {AnalyseStack2 T Found}
	 end
      end
      proc{AnalyseStack Stack Name}
	 if {List.length Stack} ==1 orelse {List.length Stack} == 2 then
	    {Main.g printMessagePorI({VirtualString.toAtom 'Program paused because function '#Name#' seems to infinite loop'})}
	    {Main.g pauseError}
	 else Found in
	    Found = {AnalyseStack2 Stack 0}
	    if Found > 16 then
	       {Main.g printMessagePorI({VirtualString.toAtom 'Program paused because function '#Name#' seems to infinite loop'})}
	       {Main.g pauseError}
	    end
	 end
      end
      fun{NewState2 Index State2 Pos ToAdd}
	 if Pos == Index then
	    if State2.1.2+1 == 50 then
	       {AnalyseStack State2.1.3 State.2.1.1}
	    end
	    if {List.member ToAdd State2.1.3} then
	       State2.1.1#State2.1.2+1#State2.1.3|State.2.2
	    else
	       State2.1.1#State2.1.2+1#{Append [ToAdd] State2.1.3}|State.2.2
	    end
	 else
	    State2.1|{NewState2 Index State2.2 Pos+1 ToAdd}
	 end
      end
   in
      case Msg
      of addStack(X) then Index in
	 Index = {FindIndex State.1 X.1.stat.1 1}
	 if Index == ~1 then State
	 else
	    State.1#{NewState2 Index State.2 1 X.2}
	 end
      [] addFct(X) then
	 {Append [X] State.1}#{Append [X#0#nil] State.2}
      []terminate then {Thread.terminate {Thread.this}} State
      end
   end
   
end