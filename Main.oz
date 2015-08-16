%Author: Mehdi Dumoulin, EPL, UCL.
functor
import
   Gui	
   Interpreter
   Lexer
   Utils
   Open
export
   Compile
   ScannerMain
   Execute
   G
   ProbDetect
   EnonceExercise
   NameProcEx
   TestInput
   TestOutput
   ListOfThreadInProcess
define
   G

   /* Variable used to stock the exercises */
   EnonceExercise={NewCell _}
   NameProcEx={NewCell _}
   TestInput={NewCell _}
   TestOutput={NewCell _}

   /*  Enter your statement here */
   EnonceExercise := ["Do a procedure with name Fact who take's two parameter and put in the second parameter the factorial of the first one (Do not declare the variable Fact)"
		      "Do a procedure with name Sum who take's two parameter and put in the second parameter the square of sum of n first number begining with 1 (Do not declare the variable Fact)"
		     ]
   /* Enter the name of expected procedure */
   NameProcEx := ["Fact" "Sum"]
   /* Enter your argument for testing in a record with form : 
							  arg(1:first_argument 2:second_argument ...) */
   TestInput := [arg(1:4) arg(1:6)]
   /* Enter expected output here corresponding to the argument enter above  */
   TestOutput := [24 91]

   
   OkParse = {NewCell true}

   ListOfThreadInProcess = {NewCell nil}
   

   /*
   * Procedure who execute the code enter by the user.
   * Procedure called by clickink on the button execute
   */
   proc{Execute Text End}
      A B C D RFalse in
      A = {Lexer.lexeme Text}
      if {List.nth A {List.length A}} == error then
	 {G printMessagePorI('Problem with lexical analizer')}
	 End = true
      else
	    B =  {Utils.parserList A C RFalse}
	 if B andthen @OkParse then
	    {G printMessagePorI('Parsing success')}
	    thread
	       D = {Interpreter.interpret C}
	       {Wait D}
	       End = true
	    if D == true then
	       {G printMessagePorI('Execution success')}
	       {G printMessagePorI('*****************')}
	       {G printMessageAnswer('*****************')}
	    else
	       {G printMessageAnswer(D)}
	       {G printMessagePorI('Execution problem see AST above')}
	       {G printMessagePorI('*****************')}
	       {G printMessageAnswer('*****************')}
	    end end
	 else
	    {G printMessagePorI('Problem with parsing')}
	    if @OkParse then
	       {G printMessagePorI('Error with statement'#RFalse.1)}
	    else
	       skip
	    end
	    {G printMessagePorI('*****************')}
	    OkParse := true
	    End = true
	 end
      end
   end


   /*
   * Procedure who compile the code enter by the user and print the parse tree.
   * Procedure called by clickink on the button compile.
   */
   proc{Compile Text End}
      A B C RFalse F in
      A = {Lexer.lexeme Text}
      if A == error then
	 {G printMessagePorI('Problem with lexical analizer')}
      else
	 B =  {Utils.parserList A C RFalse}
	 F={New Open.file init(name:text2 flags:[write create])}
	 {F write(vs:{Value.toVirtualString C 1000 1000})}
	 {F close}
	 if B andthen @OkParse then
	    {G printMessagePorI('Parsing success')}
	    {G printMessageAnswer(C)}
	    {G printMessageAnswer('AST :')}
	 else
	    {G printMessagePorI('Problem with parsing')}
	    if @OkParse then
	       {G printMessagePorI('Error with statement'#RFalse.1)}
	    else
	       skip
	    end
	    OkParse := true
	    {G printMessagePorI('*****************')}
	 end
	 {G printMessagePorI('*****************')}
	 {G printMessageAnswer('*****************')}
      end
      End = true
    end


   /*
   * Procedure who tokenize the code enter by the user and print the token.
   * Procedure called by clickink on the button scanner.
   */
    proc{ScannerMain Text End}
       A F in
       A = {Lexer.lexeme Text}
       F={New Open.file init(name:text flags:[write create])}
       {F write(vs:{Value.toVirtualString A 1000 1000})}
       {F close}
       if A == error then
	  {G printMessagePorI('Problem with lexical analizer')}
	  End = true
       else
	  {G printMessageAnswer(A)}
	  {G printMessageAnswer('Tokens : ')}
	  {G printMessagePorI('Token success')}
	  {G printMessagePorI('*****************')}
	  {G printMessageAnswer('*****************')}
	  End = true
       end
    end
    
    proc{ProbDetect}
       OkParse := false
    end


    /* Initialization of graphical interface */
    G = {Utils.newActive Gui.gui init}
   
end