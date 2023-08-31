namespace Isabelle

open System.IO

// Test streamlining, write .thy files directly, making them accesible from Isabelle
module Connector =
    
    let write text filename = 
        
        let theoryName = if filename = "" then "Proof" else filename 

        // Switch to any other path
        let dir = "C:\Users\emman\Desktop\\" + theoryName + ".thy"

        let header = "theory " + theoryName + " imports Resolution begin\n"

        let footer = "\nend\n"

        File.WriteAllLines(dir,[header + text + footer])

    
        

    

