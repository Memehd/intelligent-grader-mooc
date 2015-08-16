functor
import
   Main
export
   Lexeme
define
   
   /***************************** Lexical Analyzer *****************************/

   /* Output of scanner :
   leftBrace(pos:Line#Col)
   rightBrace(pos:Line#Col)
   leftPar(pos:Line#Col)
   rightPar(pos:Line#Col)

   opBin('+' pos:Line#Col) (or -, *, /, div, mod, '.', :=, ==, \\=, =<, >=, <, >)
   opUn('@' pos:Line#Col) (or '~')
   eq(pos:Line#Col)
   colon(pos:Line#Col)
   dollar(pos:Line#Col)
	 
   keyThread(pos:Line#Col)
   keySkip(pos:Line#Col)
   keyRaise(pos:Line#Col)
   keyEnd(pos:Line#Col)
   keyLocal(pos:Line#Col)
   keyIn(pos:Line#Col)
   keyIf(pos:Line#Col)
   keyThen(pos:Line#Col)
   keyElse(pos:Line#Col)
   keyCase(pos:Line#Col)
   keyOf(pos:Line#Col)
   keyTry(pos:Line#Col)
   keyCatch(pos:Line#Col)
   keyProc(pos:Line#Col)
   label(true pos:Line#Col)
   atom(true pos:Line#Col)
   label(false pos:Line#Col)
   atom(false pos:Line#Col)
   label(unit pos:Line#Col)
   atom(unit pos:Line#Col)
   */

/* Check if the atom is ending */
fun{EndOfAtom X}
   {Not {Char.isAlNum X} orelse X==&_}
end


/* Collect digit */
fun{ColInt T TT L C Pos F Sup Float}
   fun{ColInt2 T P}
      case T of nil then Float = 0 TT = nil Pos = P + Sup nil
      []H|T andthen {F H} then H|{ColInt2 T P+1}
      []&.|_ then Float = 1 nil
      else
	 Float = 0 TT = T Pos = P + Sup nil 
      end
   end
in
   {ColInt2 T 0}
end


/* Collect float and int */
fun{LexNum T TT Line Col Pos}
   case T
   of &~|&0|A|T1 andthen A==&x orelse A==&X then X in
      X= {ColInt T1 TT Line Col Pos fun{$ H} {Char.isXDigit H} end 3 _}
      int({StringToInt &~|&0|A|X} pos:Line#Col)
   [] &0|A|T1 andthen A==&b orelse A==&B then X in 
      X= {ColInt T1 TT Line Col Pos fun{$ H} H == &1 orelse H == &0 end 2 _}
      int({StringToInt &0|A|X} pos:Line#Col)
   [] &~|&0|A|T1 andthen A==&b orelse A==&B then X in
      X={ColInt T1 TT Line Col Pos fun{$ H} H == &1 orelse H == &0 end 3 _}
      int({StringToInt &~|&0|A|X} pos:Line#Col)
   [] &~|&0|T1 then X F in
      case T1.1
      of &. then X = {ColInt T1 TT Line Col Pos fun{$ H} {Char.isDigit H} orelse {Member H ".eE~"} end 2 F}
	 float({String.toFloat &~|&0|X} pos:Line#Col)
      [] &8 then X = {ColInt T1 TT Line Col Pos fun{$ H} {Char.isDigit H} orelse {Member H ".eE~"} end 2 F}
	 	 float({String.toFloat &~|&0|X} pos:Line#Col)
      [] &9 then X = {ColInt T1 TT Line Col Pos fun{$ H} {Char.isDigit H} orelse {Member H ".eE~"} end 2 F}
	 	 float({String.toFloat &~|&0|X} pos:Line#Col)
      else X = {ColInt T1 TT Line Col Pos fun{$ H} {Char.isDigit H} end 2 F} int({StringToInt &~|&0|X} pos:Line#Col+Pos)
      end
   [] &0|T1 then X F in
      case T1.1
      of &. then X = {ColInt T1 TT Line Col Pos fun{$ H} {Char.isDigit H} orelse {Member H ".eE~"} end 1 F}
	 float({String.toFloat &0|X} pos:Line#Col)
      [] &8 then X = {ColInt T1 TT Line Col Pos fun{$ H} {Char.isDigit H} orelse {Member H ".eE~"} end 1 F}
	 	 float({String.toFloat &0|X} pos:Line#Col)
      [] &9 then X = {ColInt T1 TT Line Col Pos fun{$ H} {Char.isDigit H} orelse {Member H ".eE~"} end 1 F}
	 	 float({String.toFloat &0|X} pos:Line#Col)
      else X = {ColInt T1 TT Line Col Pos fun{$ H} {Char.isDigit H} end 1 F}
	 if F == 1 then X in
	    X = {ColInt T1 TT Line Col Pos fun{$ H} {Char.isDigit H} orelse {Member H ".eE~"} end 1 _}
	    float({String.toFloat &0|X} pos:Line#Col)
	 else
	    int({StringToInt &0|X} pos:Line#Col)
	 end
      end
   [] &~|T1 then X F in
      case T1.1
      of &. then X = {ColInt T1 TT Line Col Pos fun{$ H} {Char.isDigit H} orelse {Member H ".eE~"} end 1 F}
	 float({String.toFloat &~|X} pos:Line#Col)
      else X = {ColInt T1 TT Line Col Pos fun{$ H} {Char.isDigit H} end 1 F}
	 if F == 1 then X in
	    X = {ColInt T1 TT Line Col Pos fun{$ H} {Char.isDigit H} orelse {Member H ".eE~"} end 1 _}
	    float({String.toFloat &~|X} pos:Line#Col)
	 else
	    int({StringToInt &~|X} pos:Line#Col)
	 end
      end
   [] T1 then X F in
      case T1.1
      of &. then X = {ColInt T1 TT Line Col Pos fun{$ H} {Char.isDigit H} orelse {Member H ".eE~"} end 0 F}
	 float({String.toFloat X} pos:Line#Col)
      else X = {ColInt T1 TT Line Col Pos fun{$ H} {Char.isDigit H} end 0 F}
	 if F == 1 then X in
	    X = {ColInt T1 TT Line Col Pos fun{$ H} {Char.isDigit H} orelse {Member H ".eE~"} end 0 _}
	    float({String.toFloat X} pos:Line#Col)
	 else
	    int({StringToInt X} pos:Line#Col)
	 end
      end
   end
end


/* Determine if X is a Hex digit or a Octal digit */
fun{HexVal X}
   {List.member X [&0 &1 &2 &3 &4 &5 &6 &7 &8 &9 &a &b &c &d &e &f &A &B &C &D &E &F]}
end
fun{IsOct X}
   {List.member X [&0 &1 &2 &3 &4 &5 &6 &7]}
end


/* Collect leter and digit  */
fun{ColId T TT L C Pos}
   fun{ColId2 T P}
      case T of nil then TT = nil Pos = P nil
      []H|T andthen {Char.isAlNum H} then H|{ColId2 T P+1}
      else TT = T Pos = P nil
      end
   end
in
   id({String.toAtom {ColId2 T 0}} pos:L#C)
end

fun{LexDelId T TT Line Col Pos}
   fun{Loop L I}
      case L
      of &`|T then Pos = I+1 TT=T [&`]
      [] &\\|&a|T then &\a|{Loop T I+2}
      [] &\\|&b|T then &\b|{Loop T I+2}
      [] &\\|&f|T then &\f|{Loop T I+2}
      [] &\\|&n|T then &\n|{Loop T I+2}
      [] &\\|&r|T then &\r|{Loop T I+2}
      [] &\\|&t|T then &\t|{Loop T I+2}
      [] &\\|&v|T then &\v|{Loop T I+2}
      [] &\\|&\\|T then &\\|{Loop T I+2}
      [] &\\|&'|T then &'|{Loop T I+2}
      [] &\\|&"|T then &"|{Loop T I+2}
      [] &\\|&`|T then &`|{Loop T I+2}
      [] &\\|&&|T then &&|{Loop T I+2}
      [] &\\|A|B|C|T andthen {IsOct A} andthen {IsOct B} andthen {IsOct C} then
	 ((A-&0)*64+(B-&0)*8+(C-&0))|{Loop T I+4}
      [] &\\|&x|A|B|T andthen {Char.isXDigit A} andthen {Char.isXDigit B} then
	 ({HexVal A}*16+{HexVal B})|{Loop T I+4}
      [] &\\|&X|A|B|T andthen {Char.isXDigit A} andthen {Char.isXDigit B} then
	 ({HexVal A}*16+{HexVal B})|{Loop T I+4}
      [] H|T then H|{Loop T I+1}
      end
   end
in
   id({String.toAtom &`|{Loop T 0}} pos:Line#Col)
end
fun{LexDelAtom T TT Line Col Pos}
   K
   fun{Loop L I}
      case L
      of &'|&(|T then Pos = I + 1 K=label TT=&(|T nil
      [] &'|T then Pos = I +1 K=atom TT=T nil
      [] &\\|&a|T then &\a|{Loop T I+2}
      [] &\\|&b|T then &\b|{Loop T I+2}
      [] &\\|&f|T then &\f|{Loop T I+2}
      [] &\\|&n|T then &\n|{Loop T I+2}
      [] &\\|&r|T then &\r|{Loop T I+2}
      [] &\\|&t|T then &\t|{Loop T I+2}
      [] &\\|&v|T then &\v|{Loop T I+2}
      [] &\\|&\\|T then &\\|{Loop T I+2}
      [] &\\|&'|T then &'|{Loop T I+1}
      [] &\\|&"|T then &"|{Loop T I+1}
      [] &\\|&`|T then &`|{Loop T I+1}
      [] &\\|&&|T then &&|{Loop T I+1}
      [] &\\|A|B|C|T andthen {IsOct A} andthen {IsOct B} andthen {IsOct C} then
	 ((A-&0)*64+(B-&0)*8+(C-&0))|{Loop T I+4}
      [] &\\|&x|A|B|T andthen {Char.isXDigit A} andthen {Char.isXDigit B} then
	 ({HexVal A}*16+{HexVal B})|{Loop T I+4}
      [] &\\|&X|A|B|T andthen {Char.isXDigit A} andthen {Char.isXDigit B} then
	 ({HexVal A}*16+{HexVal B})|{Loop T I+4}
      [] H|T then H|{Loop T I+1}
      end
   end
   A={String.toAtom {Loop T 0}}
in
   K(A pos:Line#Col)
end


/* Tokenization with position in the file */
/* format output : token(_ pos(L C)) */
fun{Lexeme Text}
   fun{Lex Text Line Col}
      case Text
	 /* Parenthesis + brace + space */
      of &{|T then leftBrace(pos:Line#Col)|{Lex T Line Col+1}
      [] &}|T then rightBrace(pos:Line#Col)|{Lex T Line Col+1}
      [] &(|T then leftPar(pos:Line#Col)|{Lex T Line Col+1}
      [] &)|T then rightPar(pos:Line#Col)|{Lex T Line Col+1}
      [] H|T andthen {Char.isSpace H} then
	 if H == &\r orelse H == &\n  then
	    {Lex T Line+1 0}
	 elseif H == &\t then
	    {Lex T Line Col+8} %nbre space for tab
	 else
	    {Lex T Line Col+1}
	 end
	 
	 /* unary/binary operator */	 
      [] &+|T then opBin('+' pos:Line#Col)|{Lex T Line Col+1}
      [] &-|T then opBin('-' pos:Line#Col)|{Lex T Line Col+1}
      [] &*|T then opBin('*' pos:Line#Col)|{Lex T Line Col+1}
      [] &/|T then opBin('/' pos:Line#Col)|{Lex T Line Col+1}
      [] &d|&i|&v|A|T andthen {EndOfAtom A} then opBin('div' pos:Line#Col)|{Lex A|T Line Col+3}
      [] &m|&o|&d|A|T andthen {EndOfAtom A} then opBin('mod' pos:Line#Col)|{Lex A|T Line Col+3}
      [] &.|T then opBin('.' pos:Line#Col)|{Lex T Line Col+1}
      [] &:|&=|T then opBin(':=' pos:Line#Col)|{Lex T Line Col+2}
      [] &@|T then opUn('@' pos:Line#Col)|{Lex T Line Col+1}
      [] &=|&=|T then opBin('=='  pos:Line#Col)|{Lex T Line Col+2}
      [] &\\|&=|T then opBin('\\=' pos:Line#Col)|{Lex T Line Col+2}
      [] &=|&<|T then opBin('=<' pos:Line#Col)|{Lex T Line Col+2}
      [] &>|&=|T then opBin('>=' pos:Line#Col)|{Lex T Line Col+2}
      [] &<|T then opBin('<' pos:Line#Col)|{Lex T Line Col+1}
      [] &>|T then opBin('>' pos:Line#Col)|{Lex T Line Col+1}
      [] &=|T then eq(pos:Line#Col)|{Lex T Line Col+1}
      [] &:|T then colon(pos:Line#Col)|{Lex T Line Col+1}
      [] &$|T then dollar(pos:Line#Col)|{Lex T Line Col+1}
	 
	 /* Keywords */
      [] &t|&h|&r|&e|&a|&d|A|T andthen {EndOfAtom A} then keyThread(pos:Line#Col)|{Lex A|T Line Col+6}
      [] &s|&k|&i|&p|A|T andthen {EndOfAtom A} then keySkip(pos:Line#Col)|{Lex A|T Line Col+4} 
      [] &r|&a|&i|&s|&e|A|T andthen {EndOfAtom A} then keyRaise(pos:Line#Col)|{Lex A|T Line Col+5} 
      [] &e|&n|&d|A|T andthen {EndOfAtom A} then keyEnd(pos:Line#Col)|{Lex A|T Line Col+3}
      [] &l|&o|&c|&a|&l|A|T andthen {EndOfAtom A} then keyLocal(pos:Line#Col)|{Lex A|T Line Col+5}
      [] &i|&n|A|T andthen {EndOfAtom A} then keyIn(pos:Line#Col)|{Lex A|T Line Col+2}
      [] &i|&f|A|T andthen {EndOfAtom A} then keyIf(pos:Line#Col)|{Lex A|T Line Col+2}
      [] &t|&h|&e|&n|A|T andthen {EndOfAtom A} then keyThen(pos:Line#Col)|{Lex A|T Line Col+4}
      [] &e|&l|&s|&e|A|T andthen {EndOfAtom A} then keyElse(pos:Line#Col)|{Lex A|T Line Col+4}
      [] &c|&a|&s|&e|A|T andthen {EndOfAtom A} then keyCase(pos:Line#Col)|{Lex A|T Line Col+4}
      [] &o|&f|A|T andthen {EndOfAtom A} then keyOf(pos:Line#Col)|{Lex A|T Line Col+2}
      [] &t|&r|&y|A|T andthen {EndOfAtom A} then keyTry(pos:Line#Col)|{Lex A|T Line Col+4}
      [] &c|&a|&t|&c|&h|A|T andthen {EndOfAtom A} then keyCatch(pos:Line#Col)|{Lex A|T Line Col+5}
      [] &p|&r|&o|&c|A|T andthen {EndOfAtom A} then keyProc(pos:Line#Col)|{Lex A|T Line Col+4}
      [] &t|&r|&u|&e|&(|T then label(true pos:Line#Col)|leftPar(pos:Line#Col+4)|{Lex T Line Col+5} 
      [] &t|&r|&u|&e|A|T andthen {EndOfAtom A} then atom(true pos:Line#Col)|{Lex A|T Line Col+4} 
      [] &f|&a|&l|&s|&e|&(|T then label(false pos:Line#Col)|leftPar(pos:Line#Col+5)|{Lex T Line Col+6} 
      [] &f|&a|&l|&s|&e|A|T andthen {EndOfAtom A} then atom(false pos:Line#Col)|{Lex A|T Line Col+5} 
      [] &u|&n|&i|&t|&(|T then label(unit pos:Line#Col)|leftPar(pos:Line#Col+4)|{Lex T Line Col+5}
      [] &u|&n|&i|&t|A|T andthen {EndOfAtom A} then atom(unit pos:Line#Col)|{Lex A|T Line Col+4}
	 
      [] &'|T then TT Pos in {LexDelAtom T TT Line Col Pos}|{Lex TT Line Col+Pos+1}
      [] &`|T then TT Pos in {LexDelId T TT Line Col Pos}|{Lex TT Line Col+Pos+1}
	 
	 /* Variables + Number */
      [] H|T andthen {Char.isUpper H} then TT Pos in {ColId H|T TT Line Col Pos}|{Lex TT Line Col+Pos}
      [] H|T andthen {Char.isDigit H} then TT Pos in {LexNum H|T TT Line Col Pos}|{Lex TT Line Col+Pos}
      [] &~|H|T andthen {Char.isDigit H} then TT Pos in {LexNum H|T TT Line Col Pos}|{Lex TT Line Col+Pos}
      [] &~|T then opUn('~' pos:Line#Col)|{Lex T Line Col+1}
      [] nil then nil

	 /* Message d'erreur */
      else {Main.g printMessagePorI({VirtualString.toAtom "syntax error: expression at statement position at Line: "#Line#" Column: "#Col})} error|nil

      end
   end
in
   {Lex Text 1 1}
end

end