%Author: Mehdi Dumoulin, EPL, UCL.
functor
import
   Main
export
   Parser
define
   
   /***************************** Parser *****************************/

   /* Output of parser :
		
		   keySkip(pos:P)
   keyRaise(pos:P id(I pos:Pid))
   keyAnd(R1.1 R2.1)
   keyLocal(id(I pos:Pid) pos:Plocal s:R2.1)
   keyIf(id(I pos:Pid) pos:Pif R2.1 R3.1)
   
   kVarVal(I X)
   kVarVal(I kProc(Idbrace T2.1))
   R = kVarOp1(I1 O I2)#T true
   R = kVarOp3(I1 '.:=' I2 I3 I4)#T true
   R = kVarOp2(I1 Ob I2 I3)#T true
   R = kVarVar(I1 I2)#T true
   
   */

   /* Parser */
   fun{Parser Text R RFalse}
      if {ParseSkip Text R} then true
      elseif {ParseRaise Text R} then true
      elseif {ParseLocal Text R RFalse} then true
      elseif {ParseIf Text R RFalse} then true
      elseif {ParseCase Text R RFalse} then true
      elseif {ParseThread Text R RFalse} then true
      elseif {ParseTry Text R RFalse} then true
      elseif {ParseApply Text R} then true
      elseif {ParseEq Text R RFalse} then true
      else if {Value.isFree RFalse} then
	      RFalse = Text
	   end
	 false
      end
   end
   
/* Case of skip to parse */
fun{ParseSkip Text R}
   case Text of keySkip(pos:P)|T then R = keySkip(pos:P)#T true
   else false
   end
end

/* Case of raise to parse */
fun{ParseRaise Text R}
   case Text of keyRaise(pos:Pr)|id(I pos:Pi)|keyEnd(pos:_)|T then R = keyRaise(pos:Pr id(I pos:Pi))#T true
   [] keyRaise(pos:Pr)|_|keyEnd(pos:_)|T then {Main.g printMessagePorI('Parse Error: id expected after raise'#Pr)} {Main.probDetect} R = T true
   [] keyRaise(pos:Pr)|keyEnd(pos:_)|T then {Main.g printMessagePorI('Parse Error: id expected after raise'#Pr)} {Main.probDetect} R = T true
   [] keyRaise(pos:Pr)|id(_ pos:_)|T then {Main.g printMessagePorI('Parse Error: end not found after raise'#Pr)} R = T {Main.probDetect} false
   else false
   end
end

/* Case of multiple statements to parse */
fun{ParseMultState Text R RFalse} R1 R2 in
   if {Parser Text R1 RFalse} then
      if {ParseMultState R1.2 R2 RFalse} then R=keyAnd(R1.1 R2.1)#R2.2 true
      else R = R1 true
      end
   else false
   end
end

/* Case of thread to parse */
fun{ParseThread Text R RFalse}
   case Text
   of keyThread(pos:P)|T then R2 in
      if {ParseMultState T R2 RFalse} then
	 case R2.2 of keyEnd(pos:_)|T then
	    R = keyThread(pos:P s:R2.1)#T true
	 else false
	 end
      else false
      end
   else false
   end
end

/* case of local to parse */
fun{ParseLocal Text R RFalse}
   case Text
   of keyLocal(pos:P)|id(1:I pos:Pi)|keyIn(pos:_)|T then R2 in
      if {ParseMultState T R2 RFalse} then
	 case R2.2 of keyEnd(pos:_)|T then
	    R = keyLocal(id(I pos:Pi) pos:P s:R2.1)#T true
	 else false
	 end
      else false
      end
   [] keyLocal(pos:P)|id(_ pos:_)|id(_ pos:_)|T then
      {Main.g printMessagePorI('Parse Error: only one id at time'#P)} {Main.probDetect} R=T false
   [] keyLocal(pos:_)|id(_ pos:Pi)|T then
      {Main.g printMessagePorI('Parse Error: in not found after id'#Pi)} {Main.probDetect} R=T false
   else false
   end
end

/* case of if to parse */
fun{ParseIf Text R RFalse}
   case Text
   of keyIf(pos:Pif)|id(I pos:Pid)|keyThen(pos:_)|T then R2 in
      if {ParseMultState T R2 RFalse} then
	 case R2.2
	 of keyElse(pos:_)|T then R3 in
	    if {ParseMultState T R3 RFalse} then
	       case R3.2
	       of keyEnd(pos:_)|T then
		  R=keyIf(id(I pos:Pid) pos:Pif R2.1 R3.1)#T true
	       else
		  {Main.g printMessagePorI('Parse Error: end expected'#Pif)} {Main.probDetect} R=T 
		 false
	       end
	    else false
	    end
	 else
	    {Main.g printMessagePorI('Parse Error: else expected'#Pif)} {Main.probDetect} R=T 
	    false
	 end
      else
	 false
      end
   [] keyIf(pos:Pif)|id(_ pos:_)|id(_ pos:_)|T then
      {Main.g printMessagePorI('Parse Error: if accept only one Id'#Pif)} {Main.probDetect} R=T false
   [] keyIf(pos:_)|id(_ pos:Pid)|T then
      {Main.g printMessagePorI('Parse Error: then not found after id'#Pid)} {Main.probDetect} R=T false
   else false
   end
end

/* Parse record and return rec(.....)#Next */
fun{ParseRecord Text R Line Col}
   Ident2
   Value2
   fun{Loop T Ident Value NT}
      case T
      of atom(A pos:_)|colon(pos:_)|id(I pos:_)|T then
	 {Loop T {Append Ident [A]} {Append Value [A#I]} NT}
      [] int(J pos:_)|colon(pos:_)|id(I pos:_)|T then
	 {Loop T {Append Ident [J]} {Append Value [J#I]} NT}
      [] rightPar(pos:_)|T then
	 Ident2 = Ident
	 Value2 = Value
	 NT = T
	 true
      [] _|colon(pos:_)|id(I pos:Pid)|T then
	 {Main.g printMessagePorI('Parse Error: features of '#I#'must be an atom or integer'#Pid)} {Main.probDetect} R=T false
      [] atom(I pos:_)|colon(pos:Pid)|_|T then {Main.g printMessagePorI('Parse Error: field of '#I#'must be an ID'#Pid)} {Main.probDetect} R=T false
      [] int(I pos:_)|colon(pos:Pid)|_|T then {Main.g printMessagePorI('Parse Error: field of '#I#'must be an ID'#Pid)} {Main.probDetect} R=T false
      else false
      end
   end
in
   case Text
   of label(L pos:_)|leftPar(pos:_)|T then NT in
      if {Loop T nil nil NT} then
	 R = rec({AdjoinList {MakeRecord L Ident2} Value2} pos:Line#Col)#NT
	 true
      else false
      end
   else false
   end
end

/* case of case to parse */
fun{ParseCase Text R RFalse}
   case Text
   of keyCase(pos:Pc)|id(I pos:_)|keyOf(pos:Pof)|T then T2 in
      if {ParseRecord T T2 Pof.1 Pof.2+3} then
	 case T2.2
	 of keyThen(pos:_)|T then T3 in
	    if {ParseMultState T T3 RFalse} then
	       case T3.2
	       of keyElse(pos:_)|T then T4 in
		  if {ParseMultState T T4 RFalse} then
		     case T4.2
		     of keyEnd(pos:_)|T then
			R = keyCase(I T2.1 T3.1 T4.1 pos:Pc)#T true
		     else
			 false
		     end
		  else
		     false
		  end
	       else {Main.g printMessagePorI('Parse Error: else statement missing'#Pof)} {Main.probDetect} R=T false
	       end
	    else false
	    end
	 []_|T then {Main.g printMessagePorI('Parse Error: fail to parse then'#Pof)} {Main.probDetect} R=T false
	 else
	    false
	 end
      else  false
      end
   [] keyCase(pos:Pc)|_|keyOf(pos:_)|T then
      {Main.g printMessagePorI('Parse Error: field to check with case must be an ID'#Pc)} {Main.probDetect} R=T false
   else
      false
   end
end

/* case of try to parse */
fun{ParseTry Text R RFalse}
   case Text
   of keyTry(pos:Pt)|T then T2 in
      if {ParseMultState T T2 RFalse} then
	 case T2.2
	 of keyCatch(pos:Pcatch)|id(I pos:_)|keyThen(pos:_)|T then T3 in
	    if {ParseMultState T T3 RFalse} then
	       case T3.2 of keyEnd(pos:_)|T then
		  R = keyTry(T2.1 I T3.1 pos:Pt)#T true
	       else  false
	       end
	    else
	       {Main.g printMessagePorI('Parse Error: end not found'#Pcatch)} {Main.probDetect} R=T 
	      false
	    end
	 []keyCatch(pos:Pcatch)|_|keyThen(pos:_)|T then
	    {Main.g printMessagePorI('Parse Error: field after catch must be an id'#Pcatch)} {Main.probDetect} R=T false
	 else false
	 end
      else  false
      end
   else false
   end
end

/* Collect ID between brace */
fun{CollIdBrace T TT L L2}
   case T of id(I pos:_)|T2 then {CollIdBrace T2 TT {Append L [I]} L2}
   []rightBrace(pos:_)|T2 then TT = T2 L2 = L true
   else false
   end
end

/* Case of left brace encounter */
fun{ParseApply Text R}
   case Text of leftBrace(pos:Pbrace)|id(I pos:_)|T then TT L2 in
      if {CollIdBrace T TT nil L2} then
	 R = keyApply(I L2 pos:Pbrace)#TT true
      else
	 false
      end
   else
      false
   end
end

/* Case of eq to parse */
fun{ParseEq Text R RFalse}
		 
   /* List variable uses */
   fun{FreeVars X}
      case X
      of keySkip(pos:_) then nil
      [] keyRaise(pos:_ id(I pos:_)) then [I]
      [] keyAnd(S1 S2) then {Append {FreeVars S1} {FreeVars S2}}
      [] keyLocal(id(I pos:_) pos:_ s:S) then {Filter {FreeVars S} fun{$ X}X\=I end}
      [] keyIf(id(I pos:_) pos:_ S1 S2) then I|{Append {FreeVars S1} {FreeVars S2}}
      [] keyCase(Id P S1 S2 pos:_) then A={Record.toList P} in Id|{Append {Filter {FreeVars S1} fun{$X}{Not{Member X A}}end}{FreeVars S2}}
      [] keyTry(S1 Id S2 pos:_) then {Append {FreeVars S1} {Filter {FreeVars S2} fun{$X}X\=Id end}}
      [] keyApply(Id Ids pos:_) then Id|Ids
      [] kVarVar(I J) then [I J]
      [] kVarOp1(I _ J) then [I J]
      [] kVarOp2(I _ J K) then [I J K]
      [] kVarOp3(I _ J K L) then [I J K L]
      [] kVarVal(I kProc(_ _ FVs)) then I|FVs
      [] kVarVal(I V) andthen {IsRecord V} then
	 I|{Record.toList V}
      [] kVarVal(I _) then [I]
      [] keyThread(pos:_ s:S) then {FreeVars S}
      end
   end
in
   case Text
   of id(I pos:_)|eq(pos:_)|int(X pos:_)|T then
      R = kVarVal(I X)#T true
   [] id(I pos:_)|eq(pos:_)|atom(A pos:_)|T then
      R = kVarVal(I A)#T true
   [] id(I pos:_)|eq(pos:_)|float(F pos:_)|T then
      R = kVarVal(I F)#T true
   [] id(I pos:_)|eq(pos:_)|keyProc(pos:_)|leftBrace(pos:_)|dollar(pos:_)|T then TT Idbrace in
      if {CollIdBrace T TT nil Idbrace} then T2 in
	 if {ParseMultState TT T2 RFalse} then
	    case T2.2 of keyEnd(pos:_)|T then
	       R = kVarVal(I kProc(Idbrace T2.1 {Filter {FreeVars T2.1} fun{$ X} {Not {Member X Idbrace}} end}))#T true
	    else  false
	    end
	 else false
	 end
      else
	 false
      end
   [] id(I1 pos:_)|eq(pos:_)|opUn(O pos:_)|id(I2 pos:_)|T then
      R = kVarOp1(I1 O I2)#T true
   [] id(I1 pos:_)|eq(pos:_)|id(I2 pos:_)|opBin(Ob pos:_)|id(I3 pos:_)|T then
      R = kVarOp2(I1 Ob I2 I3)#T true
   [] id(I1 pos:_)|eq(pos:_)|id(I2 pos:_)|T then
      R = kVarVar(I1 I2)#T true
   [] id(I1 pos:_)|eq(pos:_)|T then T2 in
      if {ParseRecord T T2 0 0} then
	 R = kVarVal(I1 {Record.subtract T2.1 pos})#T2.2 true
      else
	  false
      end
   else false
   end
end
end
