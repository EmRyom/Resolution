using Isabelle;
using Resolution;

namespace CTests
{
    [TestClass]
    public class ConnectorTest
    {
        [TestMethod]
        public void Simple()
        {
            Parser parser = new Parser(false);
            ClauseConverter clauseConverter = new(false);
            ProofTools proofTools = new ProofTools(false);


            string formulaStr = "Imp (Uni x. (Imp p[x] q[x])) (Imp (Exi x. p[x]) (Exi x. q[x]))";
            var formula = clauseConverter.Compile(parser.Parse(formulaStr));
            Proof proof = new(formula);

            proof.Applications.Add(proofTools.Resolve(1,2,proof.FindClause(1),proof.FindClause(2)).AsLeft);
            proof.Applications.Add(proofTools.Resolve(3,4,proof.FindClause(3),proof.FindClause(4)).AsLeft);
            
            AST.ProofConnector c = new(Compiler.compileProof(proof));

            var text = Generator.generateSingle(c.x.Item1, c.x.Item2);
            Console.WriteLine(text);
            
            Connector.write(text, "Automated");
        }

        [TestMethod]
        public void Crossing()
        {
            Parser parser = new Parser(false);
            ClauseConverter clauseConverter = new(false);
            ProofTools proofTools = new ProofTools(false);


            string formulaStr = "Exi x. Exi y. Dis p[x,B] Neg Dis Dis q[x,y] p[A,y] q[x,y]";
            var formula = clauseConverter.Compile(parser.Parse(formulaStr));
            Proof proof = new(formula);

            proof.Applications.Add(proofTools.Resolve(1, 2, proof.FindClause(1), proof.FindClause(2)).AsLeft);

            AST.ProofConnector c = new(Compiler.compileProof(proof));

            var text = Generator.generateSingle(c.x.Item1, c.x.Item2);
            Console.WriteLine(text);

            Connector.write(text, "Automated");
        }
    }
}

