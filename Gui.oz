%Author: Mehdi Dumoulin, EPL, UCL.
functor
import
   Main
   QTk at 'x-oz://system/wp/QTk.ozf'
   Utils
   Interpreter
   Open
export 
   Gui
define
   

   
   class Gui
      
      attr
	 textStack textStore delay textAnswer textInterParser pause
	 buttonExecute buttonScanner  buttonCompile buttonAbort
	 buttonPause exercise
	 /* -------- */


      meth init()
	 Window ButtonTD
	 TextCode ButtonQuit ButtonReset
	 HandleTx HandleBC HandleP HandleTA HandleSta HandleStore HandleE
	 DelayChoice D M LabelExplication HandleTI Desc Desc2 Menu Desc3
	 HandlePause HandleAbort ExerciseChoice DropExercise HandleExercise
	 EnonceExo HandleEnonceExo
      in	 
	 delay := 3

	 exercise := 0

	 pause:=[_]

	 Menu = menu(command(text:"New Exercise"
			     action:proc{$} 
				       NameExW NameExHandle EnonceHandle EnonceW NameProcW NameProcHandle InputHandle InputW OutputHandle OutputW ButtonSave ButtonSaveHandle Window2
				       NameExW=text(init:"Enter name of exercise"
						      width:40
						      height:1
						      handle:NameExHandle)
				       EnonceW=text(tdscrollbar:true 
						    lrscrollbar:true 
						    init:"Enter your statement here"
						    width:40
						    height:7
						    handle:EnonceHandle)
				       NameProcW=text(init:"Enter name of procedure to obtain"
						      width:40
						      height:1
						      handle:NameProcHandle)
				       InputW=text(tdscrollbar:true 
						 lrscrollbar:true 
						 init:"Enter input for testing \nSeparate with comma"
						 width:40
						 height:7
						 handle:InputHandle)
				       OutputW=text(tdscrollbar:true 
						    lrscrollbar:true 
						    init:"Enter output for testing"
						    width:40
						    height:7
						    handle:OutputHandle)
				       
				       ButtonSave = button(text:"Save"
							   handle:ButtonSaveHandle
							   action:toplevel#close)
				      
				    in
				       Window2 = {QTk.build td(NameExW EnonceW NameProcW InputW OutputW ButtonSave)}

				       {Window2 show}
				       {Window2 set(title:"Create a new exercise")}
				       
				       
				       {NameExHandle bind(event:"<1>"
							  action:proc{$}
								    if {NameExHandle get($)}== "Enter name of exercise" then {NameExHandle set("")}
								    else skip end
								 end)}
				       {EnonceHandle bind(event:"<1>"
							  action:proc{$}
								    if {EnonceHandle get($)}== "Enter your statement here" then {EnonceHandle set("")}
								    else skip end
								 end)}
				       {NameProcHandle bind(event:"<1>"
							    action:proc{$}
								    if {NameProcHandle get($)}== "Enter name of procedure to obtain" then {NameProcHandle set("")}
								    else skip end
								 end)}
				       {InputHandle bind(event:"<1>"
							 action:proc{$}
								    if {InputHandle get($)}== "Enter input for testing \nSeparate with comma" then {InputHandle set("")}
								    else skip end
								 end)}
				       {OutputHandle bind(event:"<1>"
							  action:proc{$}
								    if {OutputHandle get($)}== "Enter output for testing" then {OutputHandle set("")}
								    else skip end
								 end)}

				       {ButtonSaveHandle bind(event:"<1>"
							      action:proc{$}
									fun{CheckToSpace L R}
									   case L of nil then R = nil nil
									   []H|T then
									      if H == 44 then R = T nil
									      elseif H == 10 then R = H|T nil
									      else H|{CheckToSpace T R}
									      end
									   end
									end
									fun{CheckToNewLine L Pos R2}
									   case L of nil then R2 = nil nil
									   []H|T then R in
									      if H == 10 then
										 R2 = T nil
									      else
										 Pos#{CheckToSpace H|T R}|{CheckToNewLine R Pos+1 R2}
									      end
									   end
									end
									fun{RunToList L}
									   case L of nil then nil
									   []H|T then R2 in
									      {CheckToNewLine H|T 1 R2}|{RunToList R2}
									   end
									end

									proc{AppendArg L C}
									   case L of nil then skip
									   []H|T then
									      {Cell.assign  C {Append @C [{Record.adjoinList arg() H}]}}
									      {AppendArg T C}
									   end
									end
									LInput LOutput
								     in
									LInput = {RunToList {InputHandle get($)}}
									{AppendArg LInput Main.testInput}
									LOutput = {RunToList {OutputHandle get($)}}
									{AppendArg LOutput Main.testOutput}
									{DropExercise insert('end' [{NameExHandle get($)}])}
									{Cell.assign Main.enonceExercise {Append @(Main.enonceExercise) [{EnonceHandle get($)}] }}
									{Cell.assign Main.nameProcEx {Append @(Main.nameProcEx) [{NameProcHandle get($)}]}}
								     end
							      append:true)}
				    end)
		     separator
		     command(text:"Save my code"
			     action:proc{$}
				       Result T in
				       Result = {QTk.dialogbox save(defaultextension:".oz"
								    initialdir:"."
								    initialfile:"my_exercise"
								    title:"Choice your location"
								    $ )}
				       if {Not Result == nil} then
					  T = {HandleTx get($)}
					  if T == "Enter your source code here" then
					     {self nosourcecode}
					  else F in
					     F={New Open.file init(name:Result flags:[write create])}
					     {F write(vs:T)}
					     {F close}
					  end
				       else
					  skip
				       end
				    end)

		     command(text:"Load file"
			     action:proc{$}
				       Result F ListS in
				       Result = {QTk.dialogbox load(initialdir:"."
								    title:"Choice your file"
								    $ )}
				       if {Not Result == nil} then 
					  F={New Open.file init(name:Result flags:[read])}
					  {F read(list: ListS
						  size:all
						 )}
					  {HandleTx set(ListS)}
					  {F close}
				       else
					  skip
				       end
				    end)
		     separator
		     command(text:"Help"
			     action:proc{$}
				       Desc=message(aspect:500
						    init:"How use this grader without exercises:
1. Write your code in the text area. Beware that your code must be in the OZ kernel language.
2. Choose a delay if you want to apply a delay between each statement to execute. Otherwise choose zero second.
3. Click on Scanner, Compile or Execute Button :
				If you click on scanner button your source code is converted to a list of tokens.
				If you click on compile button your source code is compiled if it has no error and the corresponding parse tree is displayed on the output area. It is has error(s) the area where the error is displayed.
				If you click on execute button your source code is compiled.
						If this step was successful a message is displayed and the source code is interpreted (with or without a delay).
						If error is detected at the compilation the area where the error is displayed.
											       
The semantic stack and the assignment store are displayed as the execution progress in the source code. You can pause or cancel the execution of your source code. If an infinite loop is detected the execution is paused and a message appears in a pop-up to alert the user.
 If the execution was successful a message is displayed. A message is also displayed if the source code contains a recursive procedure to inform whether the procedure is tail recursive or not.


To use it with exercise, first choose an exercise in the list and then you can use this grader as explain above."
						   )
				       Wind
				    in 
				       Wind = {QTk.build td(Desc)}
				       {Wind show}
				       {Wind set(title:"Manual")}
				    end)
		     command(text:"Quit"
			     action:toplevel#close))

	 Desc3 = td(menubutton(glue:nw
			       text:"Menu"
			       menu:Menu))
	 
	 TextCode = text(tdscrollbar:true 
			 lrscrollbar:true 
			 init:"Enter your source code here"
			 handle:HandleTx
			 width:70)
	 
	 buttonCompile := button(text:"Compile"
				 handle:HandleBC
				 width:20)

	 buttonScanner := button(text:"Scanner"
				 handle:HandleP
				 width:20)

	 buttonExecute := button(text:"Execute"
				 handle:HandleE
				 width:20)

	 buttonPause := button(text:"Pause"
			      handle:HandlePause
			      state:disabled
			      width:20)

	 buttonAbort := button(text:"Abort"
			       handle:HandleAbort
			       state:disabled
			      width:20)
	 
	 DelayChoice = lr(td(label(init:"Choice your delay")
			     label(init:"Actualy :3sec"
				   handle:M))
			  dropdownlistbox(init:['1sec' '2sec' '3sec' '4sec' '5sec' '6sec' '7sec' '8sec' '9sec' '10sec' '0sec']
					  handle:D
					  action:
					     proc{$}
						delay:=  {D get(firstselection:$)}
						{M set('Actualy :'#{List.nth
								    {D get($)}
								    {D get(firstselection:$)
								    }})} end))

	 ExerciseChoice = lr(td(label(init:"Choice your exercise")
				label(init:"Actualy :free mode"
				   handle:HandleExercise))
			     dropdownlistbox(init:['exercise 1' 'exercise 2']
					     handle:DropExercise
					     action:
						proc{$} 
						   exercise := {DropExercise get(firstselection:$)}
						   {HandleExercise set('Actualy :'#{List.nth
										    {DropExercise get($)}
										    {DropExercise get(firstselection:$)
										    }})}
						  % {System.show Main.enonceExercise.@exercise}
						   {HandleEnonceExo set(state:normal)}
						   {HandleEnonceExo set({List.nth @(Main.enonceExercise) @exercise})}
						   {HandleEnonceExo set(state:disabled)}
						end))

	 EnonceExo = text(tdscrollbar:true 
			  lrscrollbar:true 
			  init:"No chosen exercise"
			  handle:HandleEnonceExo
			  width:40
			  height:7
			  state:disabled)
	 
	 
	 ButtonReset = button(text:"Reset"
			      width:20
			      action:proc{$}
					{HandleTx set("Enter your source code here")}
					{HandleTA set("Output of your code")}
					{HandleSta set(state:normal)}
					{HandleSta set("Semantic stack")}
					{HandleSta set(state:disabled)}
					{HandleStore set(state:normal)}
					{HandleStore set("Assignment store")}
					{HandleStore set(state:disabled)}
					{HandleTI set("Output of Parser/Interpreter")}
				     end)
	 
	 ButtonQuit =  button(text:"Quit"
			      action:toplevel#close
			      width:20)

	 textAnswer := message(aspect:500
			       init:"Output of your code"
			       handle:HandleTA
			      )

	 textInterParser := message(aspect:500
				    init:"Output of Parser/Interpreter"
				    handle:HandleTI
				   )

	 textStack := text(tdscrollbar:true
			   lrscrollbar:true 
			   init:"Semantic stack" 
			   handle:HandleSta
			   state:disabled
			  )
	 
	 textStore := text(tdscrollbar:true 
			   lrscrollbar:true 
			   init:"Assignment store" 
			   handle:HandleStore
			   state:disabled)
	 
	 Desc=scrollframe(glue:se
			  @textAnswer
			  width:300
			  height:150
			  tdscrollbar:true 
			  lrscrollbar:true)

	 Desc2=scrollframe(glue:se
			  @textInterParser
			  width:300
			  height:150
			  tdscrollbar:true 
			  lrscrollbar:true)

	 
	 LabelExplication = "<-------- \nStack with "#
	 "environment has a structure \n like [X#2 Y#3 ...] \n where X/Y represent "#
	 "the variable and\n 2/3 the position in the store list"#
	 "\n\nCorresponding "#
	 "store where\n the element correspond to index\n from environment\n-------->"

	 /* Placement des élements sur l'interface */
	 ButtonTD = td(@buttonScanner @buttonCompile @buttonExecute newline  @buttonPause @buttonAbort ButtonReset )
	 
	 Window = {QTk.build td(Desc3
				lr(label(init:"Source code") empty label(init:"Output")
				newline
				TextCode td(td(ExerciseChoice EnonceExo) td(ButtonTD DelayChoice ButtonQuit)) td(Desc empty Desc2)
				newline
				label(init:"Semantic stack with environment") empty
				label(init:"Assignment Store")
				newline
				   @textStack label(init:LabelExplication) @textStore))}

	 {Window set(title:"Intelligent grading of OZ programming exercises")}
	 {Window show}
	 
	 /************ Action effecter si on clique sur un element***************/
	 
	 {HandleTx bind(event:"<1>"
			action:proc{$} if {HandleTx get($)} == "Enter your source code here" then {HandleTx set("")} else skip end end)}

	 {HandleBC bind(event:"<1>"
			action:proc{$} End in
				  {self blockButton(HandleBC "Compiling")}
				  {Main.compile
				   {Append {HandleTx get($)} " "} End}
				  {Wait End}
				  {self unblockButton(HandleBC "Compile")}
			       end)
	 }

	 {HandleP bind(event:"<1>"
			action:proc{$} End in
				  {self blockButton(HandleP "Scanning")}
				  {Main.scannerMain
				   {Append {HandleTx get($)} " "} End}
				  {Wait End}
				  {self unblockButton(HandleP "Scanner")}
			       end)
	 }

	 {HandleE bind(event:"<1>"
		       action: proc{$} End in
				  thread
				     {self setPause(true)}
				     {@buttonAbort.handle set(state:normal)}
				     {self blockButton(HandleE "Process")}
				     if @exercise == 0 then
					%Mode free
					{Main.execute {Append {HandleTx get($)} " "} End}
				     else Temp in
					%Mode Exo
					Temp = {Append "local "{Append
								{List.nth @(Main.nameProcEx) @exercise} {Append
												      " in " {Append
													      {HandleTx get($)} {Append {Utils.prepareArgProc @exercise} " end "}}}}}
					{Cell.assign Interpreter.nameProcExo {List.nth @(Main.nameProcEx) @exercise}}
					{Cell.assign Interpreter.outputExo {List.nth @(Main.testOutput) @exercise}}
					{Main.execute Temp End}
				     end
				     {Wait End}
				     {Cell.assign (Main.listOfThreadInProcess) nil}
				     {self unblockButton(HandleE "Execute")}
				     {@buttonAbort.handle set(state:disabled)}
				  end
			       end)
	 }
	 

	 {HandlePause bind(event:"<1>"
			   action:proc{$}
				     if {Value.isFree @pause.1} then
					{self setPause(true)}
					{HandlePause set(text:"Pause")}
				     else {self resetPause} {HandlePause set(text:"Resume")}
				     end
				  end)}

	 {HandleAbort bind(event:"<1>"
			   action:proc{$}
				     proc{Loop L}
					case L of nil then skip
					[]H|T then
					   {Thread.terminate H} {Loop T}
					end
				     end
				  in
				     {Loop @(Main.listOfThreadInProcess)}
				     {self unblockButton(HandleE "Execute")}
				     {@buttonAbort.handle set(state:disabled)}
				     {Main.g printStack('----------------------------')}
				     {Main.g printStore('******************************')}
				     {Main.g printMessagePorI('Execution aborted')}
				     {Main.g printMessagePorI('*****************')}
				     {Main.g printMessageAnswer('*****************')}
				  end
			   )}

	 
      end

      meth pause
	 if {Value.isFree @pause.1} then
	    {self setPause(true)}
	    {@buttonPause.handle set(text:"Pause")}
	 else
	    {self resetPause}
	    {@buttonPause.handle set(text:"Resume")}
	 end
      end

      meth nosourcecode
	 local 
	    Desc=message(aspect:10000
			 init:"No source code to save"
			)
	    
	    Desc2=lr(button(text:"Ok" 
			    action:toplevel#close))
	 in 
	    {{QTk.build td(Desc Desc2)} show}
	 end
      end

      meth pauseError
	 local 
	    Desc=message(aspect:10000
			 init:"Execution paused because loop infinite suspected \n Click on resume for continued"
			)

	    Desc2=lr(button(text:"Ok" 
			    action:toplevel#close))
	 in 
	    {{QTk.build td(Desc Desc2)} show}
	 end
	 {self pause}
      end

      meth printStack(X) Prev F in
	 {@textStack.handle set(state:normal)}
	 {@textStack.handle get(Prev)}
	 F={New Open.file init(name:text flags:[write append])}
	 {F write(vs:{Value.toVirtualString X 1000 1000}#"\n\n")}
	 {F close}
	 if Prev == "Semantic stack" then
	    {@textStack.handle set({Value.toVirtualString X 1000 1000}#"\n\n")}
	 else
	    {@textStack.handle insert(coord(1 1) {Value.toVirtualString X 1000 1000}#"\n\n")}
	 end
	 {@textStack.handle set(state:disabled)}
      end
      
      meth printStore(X) Prev in
	 {@textStore.handle set(state:normal)}
	 {@textStore.handle get(Prev)}
	 if Prev == "Assignment store" then
	    {@textStore.handle set({Value.toVirtualString X 1000 1000}#"\n\n")}
	 else
	    {@textStore.handle insert(coord(1 1) {Value.toVirtualString X 1000 1000}#"\n\n")}
	 end
	 {@textStore.handle set(state:disabled)}
      end

      meth getDelay(X)
	 if @delay == 11 then X = 0
	 else X = @delay
	 end
      end

      meth printMessagePorI(X) Prev in
	 {@textInterParser.handle get(Prev)}
	 if Prev == "Output of Parser/Interpreter" then
	    {@textInterParser.handle set({Value.toVirtualString X 1000 1000}#"\n")}
	 else
	    {@textInterParser.handle set({Value.toVirtualString X 1000 1000}#"\n"#Prev)}
	 end
      end

      meth printMessageAnswer(X) Prev in
	 {@textAnswer.handle get(Prev)}
	 if Prev == "Output of your code" then
	    {@textAnswer.handle set({Value.toVirtualString X 1000 1000}#"\n")}
	 else
	    {@textAnswer.handle set({Value.toVirtualString X 1000 1000}#"\n"#Prev)}
	 end
      end

      meth getPause(X)
	 X = @pause.1
      end

      meth setPause(X)
	 @pause.1=X
      end

      meth resetPause
	 pause := [_]
      end

      meth blockButton(Button Name)
	 {@buttonPause.handle set(state:normal)}
	 {@buttonScanner.handle set(state:disabled)}
	 {@buttonExecute.handle set(state:disabled)}
	 {@buttonCompile.handle set(state:disabled)}
	 {Button set(text:Name)}
      end

      meth unblockButton(Button Name)
	 {@buttonPause.handle set(state:disabled)}
	 {@buttonScanner.handle set(state:normal)}
	 {@buttonExecute.handle set(state:normal)}
	 {@buttonCompile.handle set(state:normal)}
	 {Button set(text:Name)}
      end
   end
end