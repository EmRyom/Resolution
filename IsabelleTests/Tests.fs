namespace Tests

open System
open Isabelle.Generator
open Isabelle.AST
open Isabelle
open Microsoft.VisualStudio.TestTools.UnitTesting

[<TestClass>]
type TestClass () =

    let atom:AST.Atom = ("p",[],false)

    [<TestMethod>]
    member this.GenAtom () =
        printfn "%s" (genAtom atom)
        Assert.IsTrue(true);

    [<TestMethod>]
    member this.GenFormula () =
        printfn "%s" (genFormula Example.fProSmall)
        printfn "%s" (genFormula [])
        Assert.IsTrue(true);

    [<TestMethod>]
    member this.GenDefinition () =
        printfn "%s" (defineAtoms 
            <| (Set.toList <| findAtoms 
             Example.proSmall))
        printfn "%s" (defineAtoms 
            <| [("p",[(Fun("a",[]))],true)])
        Assert.IsTrue(true);

    [<TestMethod>]
    member this.GenDerivation () =
        printfn "%s" <| genDerivation 
                     Example.proSmall
    
    [<TestMethod>]
    member this.findClauses () =
        printfn "%s" <| genClause
                       (findClause 1 Example.proSmall)


    [<TestMethod>]
    member this.lazyGen () =
        printfn "%s" (defineAtoms 
            <| [("a",[Var("z");Var("y")],false);
                ("a",[Var("z");Var("y")],true);
                ("b",[Var("y")],false);
                ("b",[Var("y")],true);
                ("a",[Var("z");Fun("e",[])],false);
                ("a",[Var("z");Fun("e",[])],true);
                ("a",[Fun("c",[]);Fun("e",[])],false);
                ("a",[Fun("c",[]);Fun("e",[])],true);
                ("b",[Fun("c",[])],false);
                ("b",[Fun("c",[])],true);])

    [<TestMethod>]
    member this.severalProofs () =
        let result = (emptyMgu + generateMultiple 
            [
                Example.proSmall
                Example.FolSmall2; 
                Example.conceptIdea;
                Example.imageTest;
                Example.imageTest2;
                Example.multipleMGU;
                Example.double;
                Example.double2;
                Example.moti1;
            ]
        )
        Connector.write result "" 

    [<TestMethod>]
    member this.debugging () =
        let result = (emptyMgu + generateMultiple 
            [
                Example.quadMGU;
            ]
        )
        Connector.write result 

    [<TestMethod>]
    member this.findClause () =
        printfn "%s" (genClause <| findClause 1 Example.proSmall)
        
        
    [<TestMethod>]
    member this.doubleXtras () =
        printfn "%s" (emptyMgu)
        printfn "%s" (Example.double |> findAtoms |> Set.toList |> Generator.defineAtoms)
        //printfn "%s" (Isabelle.Generator.mostGeneralUnifier "aby" "axy" "''x''" "Fun ''b'' []")
        //printfn "%s" (Isabelle.Generator.mostGeneralUnifier "abc" "axy" "''x''" "Fun ''b'' [] ")


    [<TestMethod>]
    member this.types () = 
        let x = Resolution.ClausalForm.Variable("x").GetType();
        let y = Resolution.ClausalForm.Function("y", new Collections.Generic.List<Resolution.ClausalForm.IArgument>()).GetType();
        printfn "%s" (string x)
        printfn "%s" (string y)

        printfn "%s" (string <| Resolution.GeneralForm.Variable("x").GetType());
        printfn "%s" (string <| Resolution.Example.formula1.GetType())
        printfn "%s" (string <| Resolution.Example.formula2.GetType())
        printfn "%s" (string <| Resolution.Example.formula3.GetType())
        printfn "%s" (string <| Resolution.Example.formula4.GetType())
        printfn "%s" (string <| Resolution.Example.formula5.GetType())
        ()

    //[<TestMethod>]
    //member this.endToEndClauses () =
    //    let parser = Isabelle.Parser
    //    let x = Isabelle.ClauseConverter.compile()