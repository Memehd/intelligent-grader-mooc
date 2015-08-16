functor
import
   Main
   Utils
export
   Interpret
   FctImpl
   NameProcExo
   OutputExo
define

   /* List of OZ function implemented here */
   FctImpl = ['Browse']
   
   /* Nbr thread uses for now */
   NbrThread = {NewCell 1}

   /* Define time for timed out */
   TimedOut = 30000


   /* Name of procedure and argument if an exercise has been selected */
   NameProcExo = {NewCell _}

   PosArgExo = {NewCell _}

   OutputExo = {NewCell _}


/* Handling message for assignment store port  */
fun{FctStore Msg State}
   case Msg of lengthStore(X End) then Temp in X = {List.length State}+1 Temp={Append State [_]} End = 1 Temp
   [] terminate then {Thread.terminate {Thread.this}} State
   [] print(X) then X=State State
   [] elem(Ind E) then E = {List.nth State Ind} State
   [] varvar(Id I1 I2 Prob) then Ok in
      if {Value.isFree I1} orelse {Value.isFree I2} then
	 Ok = false
	 Prob = true
      else
	 try
	    {List.nth State I1} = {List.nth State I2} Ok = true Prob = false
	 catch
	    failure(...)
	 then
	    {Main.g printMessageAnswer(Id#' is already assigned with'#{List.nth State I1})}
	    Ok = false
	    Prob = true
	 end
	 if Ok then
	    State
	 else
	    nil
	 end end
   [] varval(I Id Val Prob Pstack Pstore Psmart) then Ok in
      if {Value.isFree I} then
	 Ok = false
	 Prob = true
      else
	 try
	    /* Case of Val is a record */
	    if {Record.is Val} then La in
	       La = {Label Val}
	       if La == rec then Val2 ListI in
		  Val2 = Val.1
		  {List.nth State I} = {Record.clone Val2}
		  ListI = {Record.toListInd Val2}
		  {Utils.insertRecurRecord ListI State Pstack I}
		  Ok = true
	       elseif La == kProc then Lindex Prob2 in
		  Lindex = {Utils.findAllIndexFreeVars Val.3 Pstack Prob2}
		  {Wait Lindex}
		  if Prob2 then
		     Ok = false
		  else
		     thread {Utils.checkRecursifTerm I Id Pstore Psmart} end
		     {List.nth State I} = ('proc'(Val.1 Val.2)#Lindex)
		     Ok = true
		  end
	       else
		  {List.nth State I} = Val
		  Ok = true
	       end
	    else
	       /* Case of Val is other than a record */
	       try
		  {List.nth State I} = Val Ok = true
	       catch failure(...)
	       then {Main.g printMessageAnswer(Id#' is already assigned with'#{List.nth State I})} Ok = false
	       end
	    end
	 catch failure(...)
	 then Ok = false
	    {Main.g printMessageAnswer(Id#' is already assigned with'#{List.nth State I})}
	 end
	 if Ok then Prob = false State
	 else Prob = true nil
	 end
      end
   [] varOp1(Id I1 I2 Op Prob) then Ok in
      if {Value.isFree I1} orelse {Value.isFree I2} then
	 Ok = false
	 Prob = true
      else
	 try
	    if Op == '@' then
	       {List.nth State I1} = @{List.nth State I2} 
	    elseif Op == '~' then
	       {List.nth State I1} = ~({List.nth State I2})
	    end
	    Ok = true Prob = false
	 catch failure(...)
	 then
	    {Main.g printMessageAnswer(Id#' is already assigned with'#{List.nth State I1})}
	    Ok = false
	    Prob = true
	 end
	 if Ok then State
	 else nil
	 end
      end
   [] varOp2(Id Is I2 I3 Ob Prob) then Ok in
      if {Value.isFree Is} orelse {Value.isFree I2} orelse {Value.isFree I3} then
	 Ok = false
	 Prob = true
      else
	 try
	    if Ob == '>' orelse Ob == '>=' orelse Ob == '<' orelse Ob == '=<'
	       orelse Ob == '==' orelse Ob == '\\=' then
	       {List.nth State Is} = {Value.Ob {List.nth State I2} {List.nth State I3}} Ok = true
	    else
	       case Ob of '+' then {List.nth State Is} = {List.nth State I2} + {List.nth State I3} Ok = true
	       [] '-' then {List.nth State Is} = {List.nth State I2} - {List.nth State I3} Ok = true
	       [] '*' then {List.nth State Is} = {List.nth State I2} * {List.nth State I3} Ok = true
	       [] '/' then {List.nth State Is} = {List.nth State I2} / {List.nth State I3} Ok = true
	       [] 'div' then {List.nth State Is} = {List.nth State I2} div {List.nth State I3} Ok = true
	       [] 'mod' then {List.nth State Is} = {List.nth State I2} mod {List.nth State I3} Ok = true
	       [] '.' then {List.nth State Is} = {List.nth State I2}.{List.nth State I3} Ok = true %marche ?
	       end
	    end
	 catch failure(...)
	 then
	    {Main.g printMessageAnswer(Id#' is already assigned with'#{List.nth State Is})}
	    Ok = false
	    Prob = true
	 end
	 if Ok then Prob = false State
	 else Prob = true nil
	 end
      end
   [] ifstate(Ind R2 R3 SolToPush Ok Id) then X Alarm in
      X = {List.nth State Ind}
      Alarm = {Time.alarm TimedOut}
      {WaitOr X Alarm}
      if {Value.isDet Alarm} then
	 {Main.g printMessageAnswer({VirtualString.toAtom "Timed Out : variable "#Id#" Not bound"})}
	 Ok = false
      else
	 Ok = true
	 if X then
	    SolToPush = R2
	    State
	 else
	    SolToPush = R3
	    State
	 end
      end
   [] caseState(Ind Ok S1 Id Ok2 End) then Vstore Alarm in
      Vstore = {List.nth State Ind}
      Alarm = {Time.alarm TimedOut}
      {WaitOr Alarm Vstore}
      if {Value.isDet Alarm} then
	 {Main.g printMessageAnswer({VirtualString.toAtom "Timed Out : variable "#Id#" Not bound"})}
	 Ok2 = false
	 End = true
      elseif {Record.is Vstore} then S2 in
	 S2 = S1
	 case Vstore of _ then
	    if {Record.label Vstore} == {Record.label S2} then
	       if {Record.arity Vstore} == {Record.arity S2} then
		  Ok = true
	       else Ok = false
	       end
	    else Ok = false
	    end
	 else  Ok = false
	 end
	 End = true
	 State
      end
   [] prepareEnv(Env Ind Rec) then Arity L in
      Arity = {Record.arity Rec}
      L = {Utils.checkStore Arity State Ind Rec}
      Env = L
      State
   end
end


/* Handling message for semantic stack port  */
fun{FctStack Msg State}
   case Msg of info(X) then X = State State
   []addSeq(X) then {Append X State.2}
   []terminate then {Thread.terminate {Thread.this}} State
   []removeFirst then State.2
   []caselocal(Id S Lstore) then L in L={Record.label State.1} L(stat:S env:(Id#Lstore)|State.1.env)|State.2
   []print(X) then X=State State
   []removeFirstandindex(Id1 Id2 I1 I2) then {Utils.searchIndex State.1.env Id1 Id2 I1 I2}
      State.2
   []removeFirstandindex(Id I) then {Utils.searchOneIndex State.1.env Id I} State.2
   []index(Id R) then {Utils.searchOneIndex State.1.env Id R} State
   []push(SolToPush) then L in L={Record.label State.1} L(stat:SolToPush env:State.1.env)|State.2
   []caseok(S Env) then  L in L={Record.label State.1} L(stat:S env:{Append Env State.1.env})|State.2
   []caseko(S) then  L in L={Record.label State.1} L(stat:S env:State.1.env)|State.2
   []indexMultiple(FormalParam ActualParam Statem) then T L in
      T = {Utils.findIndexActualP State.1.env FormalParam ActualParam}
      L = {Record.label State.1}
      L(stat:Statem env:T)|State.2
   []indexWithEnd(Id R End) then {Utils.searchOneIndex State.1.env Id R} End = true State
   []addtoEnv(E) then  L in L={Record.label State.1} L(stat:State.1.stat env:{Append {Utils.cleanEnv E State.1.env} State.1.env})|State.2
   []getEnv(E) then E = State.1.env State
   end
end

 fun{Iterate DelayTime Pstack Pstore Psmart}
      Answer Label
   in
      local X Y in
	 {Send Pstack print(X)}
	 {Send Pstore print(Y)}
	 {Wait X}
	 {Wait Y}
	 {Main.g printStack(X)}
	 {Main.g printStore(Y)}
      end
      {Send Pstack info(Answer)}
      {Wait {Main.g getPause($)}}
      if {Not Answer == nil} then
	 Label = {Record.label Answer.1}
      end
      case Answer of nil then
	 {Cell.assign NbrThread @NbrThread-1}
	 true
      [] Label(stat:S env:E)|_ then
	 {Delay DelayTime}
	 case S
	 of keySkip(pos:_) then {Send Pstack removeFirst} {Iterate DelayTime Pstack Pstore Psmart}
	 [] keyAnd(R1 R2) then {Send Pstack addSeq([Label(stat:R1 env:E) Label(stat:R2 env:E)])} {Iterate DelayTime Pstack Pstore Psmart}
	 [] keyLocal(id(I pos:_) pos:_ s:R2) then End Index in
	    {Send Pstack caselocal(I R2 Index)}
	    {Send Pstore lengthStore(Index End)}
	    {Wait End}
	    {Iterate DelayTime Pstack Pstore Psmart}
	 [] kVarVar(Id1 Id2) then I1 I2 Prob End1 End2 in
	    {Send Pstack indexWithEnd(Id1 I1 End1)}
	    {Send Pstack indexWithEnd(Id2 I2 End2)}
	    {Wait End1}
	    {Wait End2}
	    {Send Pstore varvar(Id1 I1 I2 Prob)}
	    if Prob then error(S)
	    else 	    {Send Pstack removeFirst}
	       {Iterate DelayTime Pstack Pstore Psmart}
	    end
	 [] kVarVal(Id Val) then I Prob End in
	    {Send Pstack indexWithEnd(Id I End)}
	    {Wait End}
	    {Send Pstore varval(I Id Val Prob Pstack Pstore Psmart)}
	    {Wait Prob}
	    {Send Pstack removeFirst}
	    if Prob then error(S)
	    else {Iterate DelayTime Pstack Pstore Psmart}
	    end
	 [] kVarOp1(Id1 O Id2) then I1 I2 Prob End1 End2 in
	    {Send Pstack indexWithEnd(Id2 I2 End1)}
	    {Send Pstack indexWithEnd(Id1 I1 End2)}
	    {Wait End1}
	    {Wait End2}
	  %  {Send Pstack removeFirstandindex(Id1 Id2 I1 I2)}
	    {Send Pstore varOp1(Id1 I1 I2 O Prob)}
	    if Prob then error(S)
	    else {Send Pstack removeFirst} {Iterate DelayTime Pstack Pstore Psmart}
	    end
	 [] kVarOp2(S Ob Id2 Id3) then Is I2 I3 Prob End1 End2 in
	    {Send Pstack index(S Is)}
	    {Send Pstack indexWithEnd(Id2 I2 End1)}
	    {Send Pstack indexWithEnd(Id3 I3 End2)}
	    {Wait End1}
	    {Wait End2}

	    
	   % {Send Pstack removeFirstandindex(Id2 Id3 I2 I3)}
	    {Send Pstore varOp2(S Is I2 I3 Ob Prob)}
	    if Prob then error(S)
	    else {Send Pstack removeFirst} {Iterate DelayTime Pstack Pstore Psmart}
	    end
	 [] keyIf(id(I pos:_) pos:_ R2 R3) then Ind SolToPush Ok in
	    {Send Pstack index(I Ind)}
	    {Send Pstore ifstate(Ind R2 R3 SolToPush Ok I)}
	    if Ok then 
	       {Send Pstack push(SolToPush)}
	       {Iterate DelayTime Pstack Pstore Psmart}
	    else error(S)
	    end
	 [] keyCase(Id Rec S Selse pos:_) then Ind Ok Ok2 Env End in
	    {Send Pstack index(Id Ind)}
	    {Send Pstore caseState(Ind Ok Rec.1 Id Ok2 End)}
	    {Wait End}
	    if {Value.isDet Ok2} andthen Ok2 == false then
	       error(S)
	    else
	       if Ok then
		  {Send Pstore prepareEnv(Env Ind Rec.1)}
		  {Send Pstack caseok(S Env)}
		  {Iterate DelayTime Pstack Pstore Psmart}
	       else
		  {Send Pstack caseko(Selse)}
		  {Iterate DelayTime Pstack Pstore Psmart}
	       end
	    end
	 []keyApply(NameFct ActualParam pos:Pap) then End Ind in
	    if {List.member NameFct FctImpl} then
	       case NameFct of 'Browse' then Ind2 E in
		  {Send Pstack index(ActualParam.1 Ind2)}
		  {Send Pstore elem(Ind2 E)}
		  thread 
		     {Wait E}
		  /* Browse */
		     {Main.g printMessageAnswer(E)}
		  end
		  {Send Pstack removeFirst}
		  {Iterate DelayTime Pstack Pstore Psmart}
	       else 
		  {Main.g printMessagePorI('Fct Oz pas encore impl'#NameFct#'pos: '#Pap)}
		  error(S)
	       end
	    else
	       {Send Pstack indexWithEnd(NameFct Ind End)}
	       if End andthen {Value.isFree Ind} then
		  {Main.g printMessagePorI('Variable'#NameFct#'not introduced'#'pos :'#Pap)}
		  error(S)
	       else E FormalParam Alarm in
	       % Fct define in the code
		  {Send Pstore elem(Ind E)}
		  Alarm =  {Time.alarm TimedOut}
		  {WaitOr Alarm E}
		  if {Value.isDet Alarm} then
		     {Main.g printMessageAnswer({VirtualString.toAtom "Timed Out : variable "#NameFct#" Not bound"})}
		     error(S)
		  else
		     if {Record.is E} andthen {Record.is E.1} andthen {Record.label E.1} == 'proc' then
			if {List.length E.1.1} == {List.length ActualParam}  then
			   if {Value.isDet @NameProcExo} andthen NameFct == {String.toAtom @NameProcExo} then End T Id in
			      Id = {List.nth ActualParam {List.length ActualParam}}
			      {Send Pstack indexWithEnd(Id T End)}
			      {Wait End}
			      {Cell.assign PosArgExo T}
			   end
			   {Send Psmart addStack({Send Pstack print($)})}
			   FormalParam = E.1.1
			   {Send Pstack indexMultiple(E.1.1 ActualParam  E.1.2)}
			   if E.2 == nil then
			      skip
			   else
			      {Send Pstack addtoEnv(E.2)}
			   end
			   {Iterate DelayTime Pstack Pstore Psmart}
			else
			   {Main.g printMessagePorI('illegal arity in application fct :'#NameFct#'pos: '#Pap)}
			   error(s)
			end
		     else
			{Main.g printMessageAnswer({VirtualString.toAtom NameFct#" is not a procedure"})}
			error(s)
		     end
		  end
	       end
	    end
	 []keyThread(s:S pos:_) then L EnvNew X in
	    {Cell.assign NbrThread @NbrThread + 1}
	    L = {VirtualString.toAtom "semstackthread"#@NbrThread}
	    {Send Pstack getEnv(EnvNew)}
	    {Wait EnvNew}
	    X = thread {InterpretThread [L(stat:S env:EnvNew)] DelayTime Pstore Psmart} end
	    {Send Pstack removeFirst}
	    {And {Iterate DelayTime Pstack Pstore Psmart} X}

	    /**********************************************************/
	    /* Insert your code here with
	 []keyWordFromParserToInterpret then ...
	    */
	    /**********************************************************/
	 else
	    error(s)
	 end
      end
 end


/* Function who interpret a source code */
fun{Interpret Program}
   DelayTime
   Pstack
   Pstore
   Psmart
   B
in
   /* Initialization of semantick stack and asignment store */
   Pstack = {Utils.newPortObject {Utils.prepareStack Program} FctStack}
   Pstore = {Utils.newPortObject nil FctStore}
   Psmart = {Utils.newPortObject nil#nil Utils.fctSmart}
   DelayTime = {Main.g getDelay($)}*1000
   B = {Iterate DelayTime Pstack Pstore Psmart}
   {Wait B}
   if {Value.isDet @PosArgExo} then P in
      {Send Pstore elem(@PosArgExo P)}
      {Wait P}
      if P == @OutputExo then
	 {Main.g printMessageAnswer('Solution found by your code correspond to expected solution, good work =) !')}
      else
	 {Main.g printMessageAnswer('Solution found by your code doesn\'t correspond to expected solution, try again !')}
      end
   end
   {Send Pstore terminate}
   {Send Pstack terminate}
   {Send Psmart terminate}
   {Main.g printStack('----------------------------')}
   {Main.g printStore('******************************')}
   B
end




/***** Function Interpret for thread *****/
fun{InterpretThread InitPstack DelayTime Pstore Psmart}
   Pstack
   B
in
   /* Initialization of a new stack. Assignment store is the same for all thread */
   Pstack = {Utils.newPortObject InitPstack  FctStack}
   B = {Iterate DelayTime Pstack Pstore Psmart}
   {Send Pstack terminate}
   B
end
end
