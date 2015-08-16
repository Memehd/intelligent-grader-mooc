/* Exo 1*/

local Fact in


Fact = proc {$ N R}
	  local FactAux in
	     FactAux = proc {$ N Acc R}
			  local T in
			     local E in
				E = 1
				T = N =< E
			     end
			     if T then R=Acc
			     else local P in
				     local I in
					local E in
					   E = 1
					   I = N-E
					end
					P = Acc*N
					{FactAux I P R}
				     end
				  end
			     end
			  end
		       end
	     local O in
		O = 1
		{FactAux N O R}
	     end
	  end
       end

local M in
   {Fact 4 M}
   {Browse M}
end

end

/* Exo 2 */

local N in
   N = 6
   {Browse (N*(N+1)*((2*N)+1) div 6)}
end
declare
Sum = proc{$ N R}
	 local Loop in
	    Loop = proc{$ N Acc}
		      local Zero in
			 Zero = 0
			 local C in
			    C = N == Zero
			    if C then
			       R = Acc
			    else
			       local N2 in
				  local Een in
				     Een = 1
				     N2 = N-Een
				  end
				  local Acc2 in
				     Acc2 = N*N
				     local Acc3 in
					Acc3 = Acc2+Acc
					{Loop N2 Acc3}
				     end
				  end
			       end
			    end
			 end
		      end
		   end
	    local Zero in
	       Zero = 0
	       {Loop N Zero}
	    end
	 end
      end


{Browse {Sum 6}}

/* Manual */
local Assign in
   Assign = proc{$ A R}
	       R = A
	    end
   local Two in
      local R in
	 Two = 2
	 {Assign Two R}
	 {Browse R}
      end
   end
end