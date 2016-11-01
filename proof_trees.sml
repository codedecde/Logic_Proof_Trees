Control.Print.printDepth := 100;
use "analytic_tableau.sml";
use "permutations.sml";
type Sequent = Prop list * Prop;
datatype ProofRule = AxiomR of Sequent | UnaryInfR of Sequent * Sequent | BinaryInfR of Sequent * Sequent * Sequent;

fun isProofRuleListSound(lst) = 	
	let		
		fun convertList2Prop(x::nil) = x
		| convertList2Prop(x::xs) = AND(x, convertList2Prop(xs))
		| convertList2Prop([]) = ATOM("T") (* This will never happen, but is here for completeness sake*)
		
		fun convertProofRule2Formula(AxiomR([],x)) = x
		|convertProofRule2Formula(AxiomR(xs,x)) = IMP(convertList2Prop(xs), x)
		|convertProofRule2Formula(UnaryInfR((xs,x), (ys,y)) ) = IMP( convertProofRule2Formula(AxiomR(xs,x) ) ,  convertProofRule2Formula(AxiomR(ys,y) ) )
		|convertProofRule2Formula(BinaryInfR((xs,x), (ys,y), (zs,z))) = IMP( AND( convertProofRule2Formula(AxiomR(xs,x) ) , convertProofRule2Formula( AxiomR(ys,y) ) ) , convertProofRule2Formula( AxiomR(zs,z) ) );
	
		fun isProofRuleSound(rule) = if analytic_tableau([],convertProofRule2Formula(rule)) = nil then true else false;
		
		fun isProofRuleListSoundHelper([]) = true
			|isProofRuleListSoundHelper(x::xs) = isProofRuleSound(x) andalso isProofRuleListSoundHelper(xs);
	in 
		isProofRuleListSoundHelper(lst)
	end

(* Part 2 *)
datatype Proof = Axiom of Sequent | UnaryInf of Proof * Sequent | BinaryInf of Proof * Proof * Sequent;

local 
	fun validSubst((a,b))([]) = true
		|validSubst((a,b))((x,y)::xs) = if a = x then b = y else validSubst((a,b))(xs);
in
	fun validSubstList([]) = true
		|validSubstList(x::xs) = if validSubst(x)(xs) andalso validSubstList(xs) then true else false;
end

fun removeDuplicateSubstitutions(nil) = nil
	|removeDuplicateSubstitutions(x::xs) = x:: removeDuplicateSubstitutions( List.filter (fn y => y <> x) (xs));

fun unifyProp(NOT(x), NOT(y)) = unifyProp(x,y)
	|unifyProp(AND(x,y), AND(a,b)) = let
		val lhs = unifyProp(x,a);
		val rhs = unifyProp(y,b);
		val comb = getOpt(lhs,nil) @ getOpt(rhs,nil);
	in
		if isSome(lhs) andalso isSome(rhs) andalso validSubstList(comb) then SOME(removeDuplicateSubstitutions(comb)) else NONE
	end
	|unifyProp(OR(x,y), OR(a,b)) = let
		val lhs = unifyProp(x,a);
		val rhs = unifyProp(y,b);
		val comb = getOpt(lhs,nil) @ getOpt(rhs,nil);
	in
		if isSome(lhs) andalso isSome(rhs) andalso validSubstList(comb) then SOME(removeDuplicateSubstitutions(comb)) else NONE
	end
	|unifyProp(IMP(x,y), IMP(a,b)) = let
		val lhs = unifyProp(x,a);
		val rhs = unifyProp(y,b);
		val comb = getOpt(lhs,nil) @ getOpt(rhs,nil);
	in
		if isSome(lhs) andalso isSome(rhs) andalso validSubstList(comb) then SOME(removeDuplicateSubstitutions(comb)) else NONE
	end
	|unifyProp(x, ATOM(y)) = SOME([(ATOM(y), x)])
	|unifyProp(_,_) = NONE;


local
	fun combine(NONE,_) = NONE
		|combine(_,NONE) = NONE
		|combine(SOME(x), SOME(y)) = SOME(x@y);
	
	fun unifyPropListHelper(nil , nil ) = SOME(nil)
		|unifyPropListHelper(x, nil) = SOME(nil)
		|unifyPropListHelper(nil, y) = NONE
		|unifyPropListHelper(x::xs, y::ys) = combine(unifyProp(x,y), unifyPropListHelper(xs,ys));
in
	fun unifyPropList(x,y) = 
		let 
			val t = unifyPropListHelper(x,y); 
		in 
			if isSome(t) andalso validSubstList(getOpt(t, nil)) then SOME(removeDuplicateSubstitutions(getOpt(t, nil))) else NONE
		end
end

local
	fun combine(NONE, _) = NONE
		|combine(_, NONE) = NONE
		|combine(SOME(x), SOME(y)) = if validSubstList( x@y ) then SOME(removeDuplicateSubstitutions(x @ y) ) else NONE;
in
	fun unifySequent((x,a), (y,b)) = 
		let 
			val rhs = unifyProp(a,b);
		in 
			List.filter (fn x => isSome(x) ) (List.map (fn x => combine( unifyPropList(x, y), rhs) ) (permute(x)) )			
		end	
end

fun unifyAxiom(x : Sequent, y : Sequent ) = let 
												val t = unifySequent(x,y); 
											in  
												if t = [] then NONE else SOME(t)
											end

local
	fun combineSingle(x)(nil) = nil
		|combineSingle(x)(y::ys) = if isSome(y) andalso isSome(x) andalso validSubstList(getOpt(x,nil)@ getOpt(y,nil)) then SOME( removeDuplicateSubstitutions( getOpt(x,nil)@ getOpt(y,nil) ) )::combineSingle(x)(ys) else combineSingle(x)(ys)
in	
	fun combineSubList(x)(nil) = nil
		|combineSubList(x)(y::ys) = combineSingle(y)(x) @ combineSubList(x)(ys)
end

fun unifyUnary((x,y) : Sequent * Sequent, (a,b) : Sequent * Sequent) = let
	val above = unifySequent(x,a);
	val below = unifySequent(y,b);
	val t = combineSubList(above)(below);
in
	if t = [] then NONE else SOME(t)
end

fun unifyBinary((x,y,z) : Sequent * Sequent * Sequent, (a,b,c) : Sequent * Sequent * Sequent) = let
	val a1 = unifySequent(x,a);
	val a2 = unifySequent(y,b);
	val b1 = unifySequent(z,c);
	val t = combineSubList(combineSubList(a1)(a2))(b1);
in
	if t = [] then NONE else SOME(t)
end

fun getSequent(Axiom(x)) = x
	|getSequent(UnaryInf(y,x)) = x
	|getSequent(BinaryInf(z,y,x)) = x;

fun unifyProofRule( AxiomR(x), []) = NONE
	|unifyProofRule(AxiomR(x), AxiomR(y)::xs) = let
													val t =  unifyAxiom(x,y);
												in 
													if isSome(t) then t else unifyProofRule(AxiomR(x), xs)
												end
	|unifyProofRule(AxiomR(x), y::xs) = unifyProofRule(AxiomR(x), xs)
	|unifyProofRule(UnaryInfR(x), []) = NONE
	|unifyProofRule(UnaryInfR(x), UnaryInfR(z)::xs) = let
														val t = unifyUnary(x,z);
													  in 
													  	if isSome(t) then t else unifyProofRule(UnaryInfR(x), xs)
													  end
	|unifyProofRule(UnaryInfR(x), y::xs) = unifyProofRule(UnaryInfR(x), xs)
	|unifyProofRule(BinaryInfR(x), []) = NONE
	|unifyProofRule(BinaryInfR(x), BinaryInfR(z)::xs) = let 
															val t = unifyBinary(x,z); 
														in 
															if isSome(t) then t else unifyProofRule(BinaryInfR(x), xs)
														end
	|unifyProofRule(BinaryInfR(x), y::xs) = unifyProofRule(BinaryInfR(x), xs)


local
	fun firstNotNone(x,y) = if isSome(x) then x else y;

	(* The root matching is at the top of the return list*)	
	fun isValidProofTreeHelper(Axiom(x) , proofRuleList ) =  let 
			val t = unifyProofRule( AxiomR(x), proofRuleList)
		in 
			if isSome(t) then SOME([getOpt(t,nil)]) else NONE
		end
		|isValidProofTreeHelper(UnaryInf((x,y)), proofRuleList) = let 
			val below = unifyProofRule( UnaryInfR((getSequent(x), y)), proofRuleList);
			val above = isValidProofTreeHelper(x, proofRuleList);
		in 
			if isSome(above) andalso isSome(below) then  SOME( getOpt(below,nil)::getOpt(above,nil) ) else NONE
		end
		|isValidProofTreeHelper(BinaryInf((x,y,z)), proofRuleList) = let 
			val above1 = isValidProofTreeHelper(x, proofRuleList);
			val above2 = isValidProofTreeHelper(y, proofRuleList);
			val below1 = unifyProofRule( BinaryInfR( (getSequent(x), getSequent(y), z) ), proofRuleList );
			val below2 = unifyProofRule( BinaryInfR( (getSequent(y), getSequent(x), z) ), proofRuleList );			
		in
			if isSome(above1) andalso isSome(above2) andalso ( isSome(below1) orelse isSome(below2) ) then SOME(getOpt(firstNotNone(below1, below2), nil) :: getOpt(above1,nil) @ getOpt(above2,nil))  else NONE
		end
 in
	fun isValidProofTree(x, proofRuleList) = isSome(isValidProofTreeHelper(x,proofRuleList) )
end
(* Test cases *)
