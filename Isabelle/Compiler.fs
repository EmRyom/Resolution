namespace Isabelle

open Resolution
open AST

// This module converts the proofs from the Proof.cs type to AST.fs type
module Compiler =
    
    let rec compileFunction (f:ClausalForm.Function):Argument =
        Fun(f.identifier.Replace("'","_m"), f.arguments |> List.ofSeq |> List.map compileArg)

    and compileArg (a:ClausalForm.IArgument):Argument = 
        match string <| a.GetType() with
        | "Resolution.ClausalForm+Variable" -> 
            let ar = a :?> ClausalForm.Variable in
            Var(ar.identifier)
        | "Resolution.ClausalForm+Function" -> 
            let ar = a :?> ClausalForm.Function in
            compileFunction ar
        | b -> failwith  <| "Type was " + b

    let compileLiteral (a:ClausalForm.Literal):Literal= 
        let args = List.map compileArg <| List.ofSeq a.Arguments
        (a.Identifier, args, a.Sign)

    let compileClause (c:ClausalForm.Clause):Clause =
        c.Literals |> List.ofSeq |> List.map compileLiteral |> Set.ofList
        
    let compileApplication (a:IApplication):Application =
        match string <| a.GetType() with
        | "Resolution.Copy" -> 
            let ar = a :?> Copy in
            Copy(compileClause ar.Clause)
        | "Resolution.Resolve" -> 
            let ar = a :?> Resolve 
            let clause = compileClause ar.Resolvent 
            let compileLiterals x = List.map compileLiteral (List.ofSeq <| x) |> Set.ofList
            let rec convertDict = function
                | x::xs -> (Var(x), compileArg ar.Substitutions[x])::convertDict xs
                | [] -> []
            Resolve(ar.FirstClause, ar.SecondClause, clause, 
                (compileLiterals (ar.GetFirstLiterals()),
                 compileLiterals (ar.GetSecondLiterals()),
                 Set.ofList <| convertDict (List.ofSeq(ar.Substitutions.Keys))
                )
            )
        | "Resolution.Rename" ->
            let ar = a :?> Rename
            Rename(ar.origin, compileClause ar.Clause, ar.originalName, ar.newName)
        | b -> failwith  <| "Type was " + b

    let compileProof (f:Resolution.Proof):Proof =
        (f.Applications |> List.ofSeq |> List.map compileApplication)




