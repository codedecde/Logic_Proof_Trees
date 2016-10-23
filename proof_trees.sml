Control.Print.printDepth := 100;
use "analytic_tableau.sml";
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

datatype Proof = Axiom of Sequent | UnaryInf of Proof * Sequent | BinaryInf of Proof * Proof * Sequent;

fun isValidProof( Axiom(x) , rules) = if unify(x, rules) = nil then false else true
	|isValidProof( UnaryInf(xs, x), rules) = 




