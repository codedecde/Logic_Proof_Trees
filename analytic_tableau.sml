Control.Print.printDepth := 100;
datatype Prop =  ATOM of string | NOT of Prop | AND of Prop * Prop | OR of Prop * Prop | IMP of Prop * Prop

fun analytic_tableau (gamma, phi) = 
	let 
		fun search(x, []) = false
		   |search(x,y::ys) = if(x = y) then true else search(x,ys)
		
		fun reorderSet(x : Prop list): Prop list =
			let 
				fun reorder_helper ([]) = ([],[])
					|reorder_helper (ATOM(x)::xs ) = 
						let val (v1,v2) = reorder_helper(xs) in (ATOM(x)::v1,v2) end
					|reorder_helper (NOT(ATOM(x))::xs) = 
						let val (v1,v2) = reorder_helper(xs) in (NOT(ATOM(x))::v1 , v2) end
					|reorder_helper (AND(x,y)::xs) =
						let val (v1,v2) = reorder_helper(xs) in (AND(x,y)::v1 ,v2) end
					|reorder_helper (OR(x,y) :: xs) = 
						let val (v1,v2) = reorder_helper (xs) in (v1, OR(x,y)::v2) end
					|reorder_helper (IMP(x,y) :: xs) = 				  
						let val (v1,v2) = reorder_helper (xs) in (v1, IMP(x,y)::v2) end
					|reorder_helper (NOT(AND(x,y))::xs) = 
						let val (v1,v2) = reorder_helper (xs) in (v1, NOT(AND(x,y))::v2) end
					|reorder_helper (NOT(OR(x,y))::xs) = 		
						let val (v1,v2) = reorder_helper(xs) in (NOT(OR(x,y))::v1 ,v2) end
					|reorder_helper (NOT(IMP(x,y)) :: xs) = 
						let val (v1,v2) = reorder_helper(xs) in (NOT(IMP(x,y))::v1 ,v2) end
					|reorder_helper (NOT(NOT(x))::xs ) = 
						let val (v1,v2) = reorder_helper(xs) in (NOT(NOT(x))::v1 ,v2) end
					val (v1,v2) = reorder_helper(x)	
			in
				v1@v2
			end

		fun reorder(ATOM(x), xs) = ATOM(x)::xs
			|reorder(NOT(ATOM(x)), xs) = NOT(ATOM(x))::xs
			|reorder(NOT(NOT(x)) ,xs) = NOT(NOT(x))::xs
			|reorder(AND(x,y), xs) = AND(x,y)::xs
			|reorder(NOT(OR(x,y)), xs) = NOT(OR(x,y))::xs
			|reorder(NOT(IMP(x,y)), xs) = NOT(IMP(x,y))::xs
			|reorder(OR(x,y), xs) = xs@[OR(x,y)]
			|reorder(NOT(AND(x,y)), xs) = xs@[NOT(AND(x,y))]
			|reorder(IMP(x,y), xs) = xs@[IMP(x,y)]
		
		fun analytic_tableau_helper ([],atom_list) = atom_list
		   |analytic_tableau_helper (AND(x,y)::xs, atom_list) = 
			let
				val temp = analytic_tableau_helper(reorder(x,reorder(y,xs)),atom_list)
			in
				if temp = [] then [] else AND(x,y)::temp
			end
		   |analytic_tableau_helper (NOT(NOT(x))::xs, atom_list) = analytic_tableau_helper(reorder(x,xs), atom_list)
		   |analytic_tableau_helper (NOT(OR(x,y))::xs, atom_list)  = 
			let
				val temp = analytic_tableau_helper(reorder( NOT(x), reorder( NOT(y), xs) ) , atom_list)
			in
				if (temp = []) then [] else NOT(OR(x,y))::temp
			end
		   |analytic_tableau_helper (NOT(IMP(x,y))::xs, atom_list) = 
			let
				val temp = analytic_tableau_helper(reorder(NOT(y),reorder(x,xs)), atom_list) 
			in 
				if (temp = []) then [] else NOT(IMP(x,y))::temp
			end
		   |analytic_tableau_helper (OR(x,y) :: xs, atom_list) = 
			let 
				val left = analytic_tableau_helper(reorder(x,xs), atom_list)
			in 
				if (left = []) then 
					let
						val right = analytic_tableau_helper(reorder(y,xs), atom_list)
					in
						if (right = []) then [] else OR(x,y)::right 
					end
				else OR(x,y)::left
			end   
		   |analytic_tableau_helper (NOT(AND(x,y)) :: xs, atom_list) = 
			let
				val left = analytic_tableau_helper(reorder(NOT(x),xs) , atom_list)
			in
				if (left = []) then
					let 
						val right = analytic_tableau_helper( reorder(NOT(y),xs), atom_list)
					in
						if (right = []) then [] else NOT(AND(x,y))::right
					end
				else NOT(AND(x,y)) :: left
			end
		  |analytic_tableau_helper (IMP(x,y) :: xs, atom_list) = 
			let
				val left = analytic_tableau_helper(reorder(NOT(x), xs), atom_list)
			in
				if (left = []) then
					let
						val right = analytic_tableau_helper(reorder(y, xs), atom_list)
					in
						if (right = []) then [] else IMP(x,y)::right
					end
				else IMP(x,y)::left
			end
		 |analytic_tableau_helper (ATOM(x)::xs, atom_list) = 
			if (search(NOT(ATOM(x)) , atom_list)) then [] else analytic_tableau_helper(xs, ATOM(x)::atom_list)
		 |analytic_tableau_helper (NOT(ATOM(x)) :: xs, atom_list) = 
			if (search (ATOM(x) , atom_list)) then [] else analytic_tableau_helper(xs, NOT(ATOM(x))::atom_list)
	in
		analytic_tableau_helper(reorderSet(NOT(phi)::gamma) , [])
	end
		

