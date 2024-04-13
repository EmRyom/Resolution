namespace Isabelle 

module AST =

    type ident = string
    and oldname = ident
    and newname = ident

    type Argument = 
        | Fun of ident * (Argument list)
        | Var of ident

    type Literal = ident * (Argument list) * bool         
    
    type Substitution = Argument * Argument

    type Unifier = Literal Set * Literal Set * Substitution Set

    type Clause = Literal Set
    and clauseRef = int

    type Application =
        | Copy    of Clause
        | Resolve of clauseRef * clauseRef * Clause * Unifier 
        | Rename  of clauseRef * Clause * oldname * newname 

    type Proof = Application list 

    type Connector = { x: Proof }
