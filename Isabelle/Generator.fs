namespace Isabelle

open ProofAST

module Generator =
       
    let negation = "n'" 

    let emptyMgu = """
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
     
    let genLiteral (li : Literal) = 
        let rec genArgList = function
            | Fun(i,[])::[] -> i  
            | Fun(i,al)::[] -> i + "_" + genArgList al
            | Fun(i,[])::xs -> i + "_" + genArgList xs
            | Fun(i,al)::xs -> i + "_" + genArgList al + "_" + genArgList xs 
            | Var(i)::[] -> i 
            | Var(i)::xs -> i + "_" + genArgList xs
            | [] -> ""
        match li with (i, al, b) ->
        (if b then "" else negation) + i + (if al = [] then "" else "_") + genArgList al

//    let genArgumentExplicit (arg : Argument) =
//        let rec genArgList = function
//            | Fun(i,[])::[] -> i  
//            | Fun(i,al)::[] -> i + "_" + genArgList al
//            | Fun(i,[])::xs -> i + "_" + genArgList xs
//            | Fun(i,al)::xs -> i + "_" + genArgList al + "_" + genArgList xs 
//            | Var(i)::[] -> i 
//            | Var(i)::xs -> i + "_" + genArgList xs
//            | [] -> ""
//        match li with (i, al, b) ->
//        (if b then "" else negation) + i + (if al = [] then "" else "_") + genArgList al

//    // Generate the proof for an MGU
//    let mostGeneralUnifier (literals : Literal Set) (substitions : Substitution Set):string = 
//        let rec substitution (arg : Substitution List)= 
//            match arg with
//            | (Var v,f)::ss -> 
//                """if x = ''""" + v + """'' then """ + 
//                match f with
//                    | Var ff -> " Var ''" + ff + """'' else """ 
//                    | Fun (ff,args) -> " Fun ''" + ff + """'' """ + genArgList args + """ else """
//                + substitution ss 
//            | [] -> ""
//            | _ -> failwith "Wrong types in susbtitution (was not Var -> Fun or Var -> Var)"
//        let uuu ls = 
//            let uuu 
//            let uuuSingle v f n = "sub" + string n + ": ‹u " + v + " = " + 
//                match f with 
//                | Var ff -> 
//                | Fun ff args -> 
//                + "› "
//            let rec uuu' n = function
//                | (v,f)::[] -> uuuSingle v f n 
//                | (v,f)::ss -> uuuSingle v f n + "and " + uuu' (n+1) ss
//                | [] -> ""
//            "then have " + uuu' 1 ls + ""
//        let cases ls = 
//            let length = List.length ls 
//            let keys = String.concat " ∧ " <| List.map (fun (x,_) -> "x≠"+x) ls 
//            let us =
//                let rec us' = function
//                    | 0 -> ""
//                    | n -> "sub" + string n + " " + us' (n-1)
//                us' length
//            let case v f = """
//            assume ‹x=""" + v + """›
//            moreover
//            have ‹(?σ ⋅ u) """ + v + """ =  """ + f + """ › unfolding composition_def by auto
//            ultimately have ‹(?σ ⋅ u) x = u x› using """ + us + """ by auto"""
//            let rec cases' = function
//                | (v,f)::xs -> case v f + "\n          }\n          moreover\n          {" + cases' xs
//                | [] -> """
//            assume ‹""" + keys + """›
//            then have ‹(?σ ⋅ u) x = (ε x) ⋅⇩t u› unfolding composition_def by auto
//            then have ‹(?σ ⋅ u) x = u x› by auto
//          }
//          ultimately show ‹(?σ ⋅ u) x = u x› by auto"""
//            """
//          fix x
//          {     """ + cases' ls           
//        ("""
//definition mgu_""" + a + """_""" + b + """ :: substitution where
//  ‹mgu_""" + a + """_""" + b + """ = (λx. """ + substitution ls + """Var x)›

//lemma mgu_""" + a + """_""" + b + """_mgu: ‹mgu⇩l⇩s mgu_""" + a + """_""" + b + """ {""" + a + """,""" + b + """}›
//proof -
//  let ?σ = ‹λx. """ + substitution ls + """Var x›
//  have a: ‹unifier⇩l⇩s ?σ {""" + a + """,""" + b + """}› unfolding """ + b + """_def """ + a + """_def unifier⇩l⇩s_def by auto
//  have b: ‹∀u. unifier⇩l⇩s u {""" + a + """,""" + b + """} ⟶ (∃i. u = ?σ ⋅ i)›
//    proof (rule;rule)
//      fix u
//      assume ‹unifier⇩l⇩s u {""" + a + """,""" + b + """}›
//      """ + uuu ls + """unfolding unifier⇩l⇩s_def """ + b + """_def """ + a + """_def by auto
//      have ‹?σ ⋅ u = u›
//        proof""" + cases ls + """
//        qed
//      then have ‹∃i. ?σ ⋅ i = u› by auto
//      then show ‹∃i. u = ?σ ⋅ i› by auto
//    qed
//  from a b show ?thesis unfolding mgu⇩l⇩s_def unfolding mgu_""" + a + """_""" + b + """_def by auto
//qed""")


    let rec defineLiterals (al:Literal list):string =
        let rec defineArgs (al':Argument list) =
            match al' with
            | x::xs -> 
                (match x with 
                | Fun(i,al'') -> "Fun ''" + i + "'' [" + defineArgs al'' + "]"
                | Var(i) -> "Var ''" + i + "''") +
                (match xs with
                | [] -> ""
                | _ -> ", " + defineArgs xs)
            | [] -> ""
        let defineLiteral (i, al', b) = 
            "definition " + genLiteral (i, al', b) + " :: ‹fterm literal› where \n  ‹" + 
            genLiteral (i, al', b) + " = " + 
            (match b with 
            | true ->  "Pos" 
            | false -> "Neg") + 
            " ''" + i + "'' [" + defineArgs al' + "]›" 
        match al with 
        | [] -> ""
        | (i, al', b)::xs -> 
            "\n\n" + defineLiteral (i, al', b) + defineLiterals xs

    let rec allClauses = function 
        | Copy(x)::xs -> x::allClauses xs
        | Resolve(_,_,x,_)::xs -> x::allClauses xs
        | Rename(_,x,_,_)::xs -> x::allClauses xs
        | [] -> []

    let rec originalClauses = function 
        | Copy(x)::xs -> x::originalClauses xs
        | _::xs -> originalClauses xs
        | [] -> [] 

    //let genDerivation (p:Proof):string = 
    //    "\n‹resolution_deriv " + (p |> originalClauses |> genFormula) + 
    //    "\n                  " + (p |> allClauses |> genFormula) + "›"

    let rec findClause ref (steps:Application list) =
        match steps[ref-1] with 
        | Copy(x) -> x 
        | Resolve(_,_,x,_) -> x 
        | Rename(_,x,_,_) -> x
        
//    let unify (a1:Atom) (a2:Atom):unifier =
//        let filter = function
//            | (Var(_),Fun(_,_)) -> true
//            | _ -> false
//        let checkSame l =
//            let rec makeMap' map = function 
//                | (a1,a2)::xs -> 
//                    if Map.containsKey a1 map then
//                        if Some(a2) = map.TryFind(a1)
//                        then makeMap' map xs
//                        else failwith "Resolution failure: Not all instances of a variable was replaced with the same functions"
//                    else makeMap' (Map.add a1 a2 map) xs
//                | [] -> map
//            Map.toList <| Map.filter (fun (key) (value) -> filter(key,value)) (makeMap' Map.empty l)
//        let rec argLists al1 al2 = 
//            match al1,al2 with
//            | Var(x)::xs, Var(y)::ys -> 
//                if not (x = y) 
//                then (Var(x),Var(y))::argLists xs ys 
//                else failwith "Resolution failure: Variables the same after substitution"
//            | Var(x)::xs, Fun(y,yss)::ys -> (Var(x), Fun(y,yss)) :: argLists xs ys
//            | Fun(y,yss)::ys, Var(x)::xs -> (Var(x), Fun(y,yss)) :: argLists xs ys
//            | Fun(x,xss)::xs, Fun(y,yss)::ys -> 
//                if x = y 
//                then argLists xss yss @ argLists xs ys 
//                else failwith "Resolution failure: Functions changed"
//            | [], [] -> []
//            | _, _ -> failwith "Resolution failure: argument list length differs"
//        match a1, a2 with 
//        | (i1, al1, b1), (i2, al2, b2) -> 
//            if i1 = i2 && b1 = not b2
//            then 
//                let unifiers = Set.ofList <| checkSame (argLists al1 al2)
//                if Set.isEmpty unifiers 
//                then E 
//                // SWITCH BOOLEANS FOR UNIFICATION
//                else U((i2, al2, b1), (i1, al1, b1), unifiers)
//            else failwith "Resolution failure: atoms cannot be unified"

//    let rec makeResolution ((f,steps):Proof) =
//        let rec remove (c:Clause) (a:Atom) = 
//            match c with
//            | x::xs when x=a -> remove xs a
//            | x::xs -> x::(remove xs a)
//            | [] -> []
//        // Generate the application of resolution_rule
//        let makeStep (proof:Proof) o (r1:clauseRef) (r2:clauseRef) (c:Clause) (a1:Atom) (a2:Atom) =
//            let orig = genFormula o in 
//            let c1 = findClause r1 proof in
//            let c2 = findClause r2 proof in
//            let allAtoms = c @ c1 @ c2 |> clash |> Set.ofList |> Set.toList in 
//            let mguArgument = unify a1 a2 in
//            let strMguArg = genUnifierRef mguArgument in
//            (mguArgument,
//            "\n  have ‹resolution_step " + orig +
//            "\n                       (" + orig + " ∪ " + genFormula [c] + ")›" +
//            "\n    apply (rule resolution_rule'[of ‹{" + genClause (a1::remove c1 a1) + "}› _ ‹{" + genClause (a2::remove c2 a2) + "}› ‹{" + 
//            genAtom a1 + "}› ‹{" + genAtom a2 + "}› " + strMguArg + "])" +
//            "\n    using " + 
//            (match mguArgument with
//                | E -> "unifier_single empty_mgu" 
//                | U(_,_,_) -> strMguArg + "_mgu") + " unfolding applicable_def vars⇩l⇩s_def vars⇩l_def" + 
//            "\n      " + (String.concat " " <| List.map (fun x -> genAtom x + "_def") allAtoms) + 
//            (match mguArgument with
//                | E -> "" 
//                | U(_,_,_) -> " " + strMguArg + "_def") + " resolution_def" + 
//            "\n    apply auto" + 
//            "\n    done" + 
//            "\n  then have ‹resolution_step " + orig +
//            "\n                            (" + genFormula (o @ [c]) + ")›" + 
//            "\n    by (simp add: insert_commute)",
//            (o @ [c]))
//        let rec applicator proof formula = function 
//            | Copy(_)::xs -> applicator proof formula xs
//            | Resolve(a,b,c,d,e)::xs -> 
//                let (mgu,step,f) = makeStep proof formula a b c d e 
//                (mgu,step)::applicator proof f xs
//            | Rename(a,b,c,d)::xs -> failwith "Not implemented"
//            | [] -> []
//        (applicator (f,steps)) f steps 

//    let generate (proof:Proof) =
//        let rec indent (s:string) = 
//            let rec indent' = function 
//                | '\n'::xs -> "\n  " + indent' xs 
//                | x::xs -> string x + indent' xs 
//                | [] -> ""
//            indent' <| Seq.toList s
//        let derivation = genDerivation proof
//        let start = "\n" + derivation + "\nproof -" in
//        let finish = indent ("ultimately show ?thesis unfolding resolution_deriv_def by auto") + "\nqed"
//        let atoms = proof |> findAtoms |> Set.toList
//        let rec addIsaConnectives = function 
//            | x::[] -> x + "\n  " 
//            | x::xs -> x + "\n  moreover" + addIsaConnectives xs
//            | [] -> ""
//        let result = makeResolution proof
//        let steps = result |> List.map snd |> addIsaConnectives 
//        let mgus = result |> List.map fst
//        (atoms, mgus, start + steps + finish)

//    // Generate MGU proofs
//    let rec mguProofs u =
//        let genArg arg = 
//            let rec genArgList = function
//                | Var(i)::xs -> "u ''"+i+"'' "+ genArgList xs
//                | Fun(i,al)::xs -> "Fun ''"+i+"'' ["+genArgList al+"]" + genArgList xs 
//                | [] -> ""
//            match arg with
//            | Var(x) -> "''"+x+"''"
//            | Fun(x,ls) -> genArgList [Fun(x,ls)]
//        match u with 
//        | [] -> []
//        | E::xs -> mguProofs xs  
//        | U(a,b,c)::xs -> 
//            let mgus = Set.toList <| Set.map (fun (x,y) -> (genArg x,genArg y)) c
//            mostGeneralUnifier (genAtom a) (genAtom b) mgus :: mguProofs xs 
        
//    let generateSingle (proof:Proof) =
//        let (atoms, mgus, text) = generate proof 
//        emptyMgu + defineAtoms atoms + (mgus |> mguProofs |> String.concat "\n\n") + "\nlemma Proof_1:" + text

//    let generateMultiple (ps:Proof list):string =
//        let genned = List.map generate ps  
//        let atoms = List.map (fun (x,_,_) -> x) genned |> List.collect id |> Set.ofList |> Set.toList  
//        let mgus = List.map (fun (_,x,_) -> x) genned |> List.collect id |> Set.ofList |> Set.toList 
//        let rec naming n = function
//            | x::xs -> "\nlemma Proof_" + string n + ":" + x + "\n" + naming (n+1) xs
//            | [] -> ""
//        let text = List.map (fun (_,_,x) -> x) genned |> naming 1
//        emptyMgu + defineAtoms atoms + "\n\n" + (if List.contains E mgus then emptyMgu else "") + (mgus |> mguProofs |> String.concat "\n") + "\n" + text 

        



