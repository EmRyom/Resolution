namespace Isabelle

open Isabelle.AST

// Unit tests that test the generator and the prover integrated in the generator
module Example =
    let fProSmall:ClausalFormula =
        [
         [("p",[],false)];
         [("q",[],false)];
         [("p",[],true)];
         [("q",[],true)]
        ]

    let sProSmall = 
        [
         Copy(1);
         Copy(3);
         Resolve(1,2,[],("p",[],false),("p",[],true))
        ]

    let proSmall:Proof = (fProSmall, sProSmall)

    let fFolSmall2 = 
        [
            [("b",[],false);("a",[],false)];
            [("a",[Var("x")],true)];
            [("a",[],true)];
            [("a",[],false);("b",[],true);("a",[Fun("a",[])],false)]
        ]

    let sFolSmall2 =
        [
          Copy(4);
          Copy(2);
          Resolve(2,1,[("a",[],false);("b",[],true)],("a",[Var("x")],true),("a",[Fun("a",[])],false));
          Copy(3);
          Resolve(4,3,[("b",[],true)],("a",[],true),("a",[],false));
          Copy(1);
          Resolve(5,6,[("a",[],false)],("b",[],true),("b",[],false))
          Resolve(7,4,[],("a",[],false),("a",[],true))
        ]

    let FolSmall2 = (fFolSmall2, sFolSmall2)


    let multipleMGU:Proof =
        (
            [
                [("a",[Var("x");Var("y")],true)]
                [("a",[Fun("b",[]);Fun("c",[])],false)]
            ]
        ,
            [
                Copy(1)
                Copy(2)
                Resolve(1,2,[],("a",[Var("x");Var("y")],true),("a",[Fun("b",[]);Fun("c",[])],false))
            ]
        )

    let fooimageTest:ClausalFormula = 
        [
            [("c",[],true)
             ("a",[Fun("a",[])],true)]
            [
             ("b",[],true)
             ("a",[Var("x")],false)
            ]
            [("b",[],false)
             ("c",[],false)]
        ]
    let barimageTest = 
        [
            Copy(1);
            Copy(2);
            Resolve(2,1,[("b",[],true);("c",[],true)],("a",[Var("x")],false),("a",[Fun("a",[])],true))
            Copy(3);
            Resolve(3,4,[("c",[],true);("c",[],false)],("b",[],true),("b",[],false))
        ]

    let imageTest = (fooimageTest,barimageTest)

    let fooimageTest2:ClausalFormula = 
        [
            [("c",[],true)
             ("a",[Fun("a",[])],true)]
            [
             ("b",[],true)
             ("a",[Var("x")],false)
            ]
            [("b",[],false)
             ("c",[],false)]
        ]
    let barimageTest2 = 
        [
            Copy(1);
            Copy(2);
            Resolve(2,1,[("b",[],true);("c",[],true)],("a",[Var("x")],false),("a",[Fun("a",[])],true))
            Copy(3);
            Resolve(3,4,[],("b",[],true),("b",[],false))
        ] 

    let imageTest2 = ([
            [("a",[],true)]
            [("b",[],true)
             ("a",[],false)]
            [("b",[],false)]
        ]
    ,
        [
            Copy(1)
            Copy(2)
            Resolve(1,2,[("b",[],true)],("a",[],true),("a",[],false))
            Copy(3)
            Resolve(3,4,[],("b",[],true),("b",[],false))
        ] 
        )


    let conceptIdea = (
        [
            [
                ("a",[],true)
                ("b",[],true)    
            ]
            [
                ("a",[],false)
                ("b",[],false)    
            ]
        ],
        [
            Copy(1)
            Copy(2)
            Resolve(1,2,
                [ ("a",[],true); ("a",[],false) ], 
                ("b",[],true), 
                ("b",[],false))
        ]
        )

    let double:Proof = (
        [
            [("a",[Var("x");Var("y")],true)]
            [("a",[Fun("b",[]);Fun("c",[])],false)]
        ]
        ,
        [
            Copy(1)
            Copy(2)
            Resolve(1,2,[],("a",[Var("x");Var("y")],true),("a",[Fun("b",[]);Fun("c",[])],false))
        ]
    )


    let double2:Proof = (
        [
            [("a",[Var("x");Var("y")],true)]
            [("a",[Fun("b",[]);Var("y")],false)]
        ]
        ,
        [
            Copy(1)
            Copy(2)
            Resolve(1,2,[("a",[Fun("b",[]);Var("y")],true)],("a",[Var("x");Var("y")],true),("a",[Fun("b",[]);Var("y")],false))
        ]
    )

    let double3:Proof = (
        [
            [("a",[Var("x");Var("y")],true)]
            [("a",[Fun("b",[]);Var("y")],false)]
        ]
        ,
        [
            Copy(1)
            Copy(2)
            Resolve(1,2,[("a",[Fun("b",[]);Fun("c",[])],true)],("a",[Var("x");Var("y")],true),("a",[Fun("b",[]);Var("y")],false))
        ]
    )

    let moti1:Proof = (
        [
            [("p",[Var("x")],false);("q",[Var("x")],true);("r",[Var("x");Fun("f",[Var("x")])],true)]
            [("p",[Var("x")],false);("q",[Var("x")],true);("rm",[Fun("f",[Var("x")])],true)]
            [("pm",[Fun("a",[])],true)]
            [("p",[Fun("a",[])],true)]
            [("r",[Fun("a",[]);Var("y")],false);("pm",[Var("y")],true)]
            [("pm",[Var("x")],false);("q",[Var("x")],false)]
            [("pm",[Var("x")],false);("rm",[Var("x")],false)]
        ]
        ,
        [
            Copy(1)
            Copy(2)
            Copy(3)
            Copy(4)
            Copy(5)
            Copy(6)
            Copy(7)
            Resolve(6,3,[("q",[Fun("a",[])],false)],("pm",[Var("x")],false),("pm",[Fun("a",[])],true))
            Resolve(2,4,[("q",[Fun("a",[])],true);("rm",[Fun("f",[Fun("a",[])])],true)],("p",[Var("x")],false),("p",[Fun("a",[])],true))
            Resolve(8,9,[("rm",[Fun("f",[Fun("a",[])])],true)],("q",[Fun("a",[])],false),("q",[Fun("a",[])],true))
            Resolve(1,4,[("q",[Fun("a",[])],true);("r",[Fun("a",[]);Fun("f",[Fun("a",[])])],true)],("p",[Var("x")],false),("p",[Fun("a",[])],true))
            Resolve(8,11,[("r",[Fun("a",[]);Fun("f",[Fun("a",[])])],true)],("q",[Fun("a",[])],false),("q",[Fun("a",[])],true))
            Resolve(5,12,[("pm",[Fun("f",[Fun("a",[])])],true)],("r",[Fun("a",[]);Var("y")],false),("r",[Fun("a",[]);Fun("f",[Fun("a",[])])],true))
            Resolve(7,13,[("rm",[Fun("f",[Fun("a",[])])],false)],("pm",[Var("x")],false),("pm",[Fun("f",[Fun("a",[])])],true))
            Resolve(10,14,[],("rm",[Fun("f",[Fun("a",[])])],true),("rm",[Fun("f",[Fun("a",[])])],false))
        ]
    )

    let moti2:Proof = (
        [
            [("p",[Var("x");Var("y")],false);("p",[Var("y");Var("x")],true)]
            [("p",[Var("x");Var("y")],false);("p",[Var("x");Var("y")],false);("p",[Var("x");Var("z")],true)]
            [("p",[Var("x");Fun("f",[Var("x")])],true)]
            [("p",[Var("x");Var("x")],false)]
        ]
        ,
        [
            Copy(1)
            Copy(3)
            Resolve(1,2,[("p",[Fun("f",[Var("x")]);Var("x")],true)],("p",[Var("x");Var("y")],false),("p",[Var("x");Fun("f",[Var("x")])],true))
        ]
    )

    let quadMGU:Proof = (
        [
            [("p",[Fun("a",[]);Fun("b",[]);Fun("c",[]);Fun("d",[])],true)]
            [("p",[Var("x");Var("y");Var("z");Var("m")],false)]
        ]
        ,
        [
            Copy(1)
            Copy(2)
            Resolve(2,1,[],("p",[Var("x");Var("y");Var("z");Var("m")],false),("p",[Fun("a",[]);Fun("b",[]);Fun("c",[]);Fun("d",[])],true))
        ]
    
    )

