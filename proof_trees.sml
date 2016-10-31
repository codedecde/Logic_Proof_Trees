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

fun unifyAxiom(x : Sequent, y : Sequent ) = if unifySequent(x,y) = [] then false else true;

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
in
	if combineSubList(above)(below) = [] then false else true
end

fun unifyBinary((x,y,z) : Sequent * Sequent * Sequent, (a,b,c) : Sequent * Sequent * Sequent) = let
	val a1 = unifySequent(x,a);
	val a2 = unifySequent(y,b);
	val b1 = unifySequent(z,c);
in
	if combineSubList(combineSubList(a1)(a2))(b1) = [] then false else true
end

fun getSequent(Axiom(x)) = x
	|getSequent(UnaryInf(y,x)) = x
	|getSequent(BinaryInf(z,y,x)) = x;

fun unifyProofRule( AxiomR(x), []) = false
	|unifyProofRule(AxiomR(x), AxiomR(y)::xs) = if unifyAxiom(x,y) then true else unifyProofRule(AxiomR(x), xs)
	|unifyProofRule(AxiomR(x), y::xs) = unifyProofRule(AxiomR(x), xs)
	|unifyProofRule(UnaryInfR(x), []) = false
	|unifyProofRule(UnaryInfR(x), UnaryInfR(z)::xs) = if unifyUnary(x,z) then true else unifyProofRule(UnaryInfR(x), xs)
	|unifyProofRule(UnaryInfR(x), y::xs) = unifyProofRule(UnaryInfR(x), xs)
	|unifyProofRule(BinaryInfR(x), []) = false
	|unifyProofRule(BinaryInfR(x), BinaryInfR(z)::xs) = if unifyBinary(x,z) then true else unifyProofRule(BinaryInfR(x), xs)
	|unifyProofRule(BinaryInfR(x), y::xs) = unifyProofRule(BinaryInfR(x), xs)


fun isValidProofTree(Axiom(x) , proofRuleList ) = if unifyProofRule( AxiomR(x), proofRuleList) then true else false
	|isValidProofTree(UnaryInf((x,y)), proofRuleList) = if unifyProofRule( UnaryInfR((getSequent(x), y)), proofRuleList) andalso isValidProofTree(x, proofRuleList) then true else false
	|isValidProofTree(BinaryInf((x,y,z)), proofRuleList) = if (unifyProofRule( BinaryInfR( (getSequent(x), getSequent(y), z) ), proofRuleList ) orelse unifyProofRule( BinaryInfR( (getSequent(y), getSequent(x), z) ), proofRuleList ) ) andalso isValidProofTree(x, proofRuleList) andalso isValidProofTree(y, proofRuleList) then true else false;

(* Test cases *)
