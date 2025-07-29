namespace Isabelle

open ProofAST

module Generator2 =
    
    let negation = "n'" 

    let preamble = """
theorem empty_mgu: 
    assumes "unifier⇩l⇩s ε L"
    shows "mgu⇩l⇩s ε L"
using assms unfolding unifier⇩l⇩s_def mgu⇩l⇩s_def apply auto
apply (rule_tac x=u in exI)
using empty_comp1 empty_comp2 apply auto
done

theorem unifier_single: "unifier⇩l⇩s σ {l}" 
unfolding unifier⇩l⇩s_def by auto

theorem resolution_rule':
    assumes "C⇩1 ∈ Cs"
    assumes "C⇩2 ∈ Cs"
    assumes "applicable C⇩1 C⇩2 L⇩1 L⇩2 σ"
    assumes "C = {resolution C⇩1 C⇩2 L⇩1 L⇩2 σ}"
    shows "resolution_step Cs (Cs ∪ C)"
    using assms resolution_rule by auto


"""

    let rec findLiterals (proof:Proof):Literal List = 

        let rec assembleLiteralsSets(clauseList: Clause List, literalSet: Literal Set):Literal Set =
            match clauseList with
            | clause::tail -> assembleLiteralsSets(tail, (Set.union clause literalSet))
            | [] -> literalSet
        let findLiterals = function
            | Copy(literals) -> literals
            | Resolve(_,_,literals,_) -> literals
            | Rename(_,literals,_,_) -> literals
        Set.toList <| assembleLiteralsSets(List.map findLiterals proof, Set.empty)

    let rec findUnifiers (proof:Proof):Unifier List =
        match proof with 
        | Resolve(_,_,_,unifier)::tail -> unifier:: findUnifiers tail
        | _::tail -> findUnifiers tail
        | [] -> []

    let initializeProof (proof:Proof):IsabelleProof = (findLiterals proof, findUnifiers proof, proof)

    let literalIdentifier((ident, args, sign):Literal):string =
        let rec genArguments(args:Argument List) = 
            match args with 
            | [] -> ""
            | arg::tail -> (
                (
                match arg with
                | Var(x) -> "_" + x
                | Fun(x,y) -> "__" + x + genArguments y
                ) +
                genArguments tail
            )
        (if sign then "" else negation) + ident + genArguments args
        
    let rec defineLiterals(literals:Literal List):string = 
        let rec defineArgument = function 
            | Var(x) -> "Var ''" + x + "''"
            | Fun(x,y) -> "Fun ''" + x + "'' [" + defineArguments y + "]" 
        and defineArguments = function 
            | [] -> ""
            | arg::[] -> defineArgument arg
            | arg::tail -> defineArgument arg + ", " + defineArguments tail

        let defineLiteral((ident, args, sign):Literal):string = 
            let fullIdent = literalIdentifier (ident, args, sign)
            "definition " + fullIdent + " :: ‹fterm literal› where\n" +
            "  ‹" + fullIdent + " = " + (if sign then "Pos" else "Neg") +
            " ''" + ident + "'' [" + defineArguments args + "]›\n\n"

        match literals with
        | literal::tail -> defineLiteral literal + defineLiterals tail
        | [] -> ""

    let writeProof(proof:Proof):string =

        let writeApplications(apps:Application List):string = ""

        let (literals, unifiers, proof) = initializeProof proof
        preamble +
        defineLiterals literals +
        writeApplications proof
        



