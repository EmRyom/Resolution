namespace Isabelle 

module AST =

    type ident = string
    and oldname = ident
    and newname = ident

    type Argument = 
        | Fun of ident * (Argument list)
        | Var of ident

    type Literal = ident * (Argument list) * bool         

    type Clause = Literal Set

    type ClausalFormula = Clause Set
    
    type Unifier = Literal Set * Literal Set * (Argument * Argument) Set

    type Proof = ClausalFormula * Application list 

    and formulaRef = int
    and clauseRef = int

    and Application =
        | Copy    of Clause
        | Resolve of clauseRef * clauseRef * Clause * Unifier 
        | Rename  of clauseRef * Clause * oldname * newname 

    type ProofConnector = { x: Proof }
