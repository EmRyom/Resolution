namespace Isabelle

open Resolution
open AST

// This module converts the proofs from the Proof.cs type to AST.fs type
module Compiler =
    
    let t = ClausalForm in

    let list (l:System.Collections.Generic.List<'a>):'a list = List.ofSeq(l)

    let rec compileFunction (f:ClausalForm.Function):argument =
        Fun(f.identifier.Replace("'","_m"), f.args |> list |> List.map compileArg)

    and compileArg (a:ClausalForm.IArgument):argument = 
        match string <| a.GetType() with
        | "Resolution.ClausalForm+Variable" -> 
            let ar = a :?> ClausalForm.Variable in
            Var(ar.identifier)
        | "Resolution.ClausalForm+Function" -> 
            let ar = a :?> ClausalForm.Function in
            compileFunction ar
        | b -> failwith  <| "Type was " + b

    let compileAtom (a:ClausalForm.Literal):Atom = 
        let args = List.map compileArg <| list a.Args
        (a.Identifier, args, a.Value)

    let compileClause (c:ClausalForm.Clause):Clause =
        c.Literals |> list |> List.map compileAtom
        
    let compileFormula (f:ClausalForm.ClausalFormula):ClausalFormula =
        f.Clauses |> list |> List.map compileClause


    
    let compileApplication (a:IApplication):Application =
        match string <| a.GetType() with
        | "Resolution.Copy" -> 
            let ar = a :?> Copy in
            Copy(ar.FormulaRef)
        | "Resolution.Resolve" -> 
            let ar = a :?> Resolve
            let clause = compileClause(ar.Resolvent)
            let f1 = compileAtom(ar.FirstLiteral)
            let f2 = compileAtom(ar.SecondLiteral)
            Resolve(ar.FirstClause, ar.SecondClause, clause, f1, f2)
        | "Resolution.Rename" ->
            let ar = a:?> Rename
            Rename(ar.origin, compileClause ar.clause, ar.GetOldName(), ar.GetNewName())
        | b -> failwith  <| "Type was " + b

    let compileProof (f:Resolution.Proof):Proof =
        let formula = compileFormula f.Formula
        (formula, f.Applications |> list |> List.map compileApplication)




