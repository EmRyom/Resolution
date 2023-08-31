using Resolution;

namespace CTests
{
    [TestClass]
    public class ProofToolsTest
    {
        [TestMethod]
        public void SimpleResolve()
        {
            Parser parser = new Parser(false);
            ClauseConverter clauseConverter = new ClauseConverter(false);
            ProofTools proofTools = new ProofTools(true);

            var formula = parser.Parse("Dis Con a b Neg b");
            var cnf = clauseConverter.Compile(formula);
            var clauses = cnf.Clauses;
            var resolvent = proofTools.Resolve(0,0,clauses[0], clauses[1]);

            formula = parser.Parse("Dis Con Neg b Neg a Dis Uni x. a[x] Dis a Con Con Neg a b Neg a[A]");
            cnf = clauseConverter.Compile(formula);
            clauses = cnf.Clauses;
            Console.WriteLine(cnf.Print());
            var resolvent1 = proofTools.Resolve(0, 0, clauses[0], clauses[2]);
            resolvent = proofTools.Resolve(0, 0, resolvent.AsLeft.Resolvent, clauses[3]);
            resolvent = proofTools.Resolve(0, 0, resolvent.AsLeft.Resolvent, clauses[1]);
            resolvent = proofTools.Resolve(0, 0, resolvent1.AsLeft.Resolvent, resolvent.AsLeft.Resolvent);
        }

        [TestMethod]
        public void ResolveCrossing()
        {
            Parser parser = new Parser(false);
            ClauseConverter clauseConverter = new ClauseConverter(false);
            ProofTools proofTools = new ProofTools(true);

            var formula = parser.Parse("Exi x. Dis Neg a[x,B] a[B,x]"); //Criss cross substitution
            var cnf = clauseConverter.Compile(formula);
            var clauses = cnf.Clauses;
            Console.WriteLine(cnf.Print());
            var resolvent = proofTools.Resolve(0, 0, clauses[0], clauses[1]);


            formula = parser.Parse("Exi x. Exi y. Dis Neg a[x,C] Con a[B,y] c");
            cnf = clauseConverter.Compile(formula);
            clauses = cnf.Clauses;
            Console.WriteLine(cnf.Print());
            resolvent = proofTools.Resolve(0, 0, clauses[0], clauses[1]);

        }

        [TestMethod]
        public void Failing()
        {
            Parser parser = new Parser(false);
            ClauseConverter clauseConverter = new ClauseConverter(false);
            ProofTools proofTools = new ProofTools(true);

            var formula = parser.Parse("Exi x. Dis Neg a[x,x,B] a[B,C,x]"); //Criss cross substitution
            var cnf = clauseConverter.Compile(formula);
            var clauses = cnf.Clauses;
            Console.WriteLine(cnf.Print());
            var resolvent = proofTools.Resolve(0, 0, clauses[0], clauses[1]);
            Console.WriteLine(resolvent.AsRight.Print());
        }

        [TestMethod]
        public void KeepsVars()
        {
            Parser parser = new Parser(false);
            ClauseConverter clauseConverter = new ClauseConverter(false);
            ProofTools proofTools = new ProofTools(true);

            var formula = parser.Parse("Exi y. Exi x. Dis Neg a[x,y] a[x,B]"); 
            var cnf = clauseConverter.Compile(formula);
            var clauses = cnf.Clauses;
            Console.WriteLine(cnf.Print());
            var resolvent = proofTools.Resolve(0,0,clauses[0], clauses[1]);
            Console.WriteLine(resolvent.AsLeft.Resolvent.Print());
        }

        [TestMethod]
        public void Factoring()
        {
            Parser parser = new Parser(false);
            ClauseConverter clauseConverter = new ClauseConverter(false);
            ProofTools proofTools = new ProofTools(true);

            var formula = parser.Parse("Exi y. Exi x. Dis Con Neg a[y] Neg a[x] a[B]");
            var cnf = clauseConverter.Compile(formula);
            var clauses = cnf.Clauses;
            Console.WriteLine(cnf.Print());
            var resolvent = proofTools.Resolve(0,0,clauses[0], clauses[1]);
            Console.WriteLine(resolvent.AsLeft.Resolvent.Print());
        }

        [TestMethod]
        public void EdgeCases()
        {
            Parser parser = new Parser(false);
            ClauseConverter clauseConverter = new ClauseConverter(false);
            ProofTools proofTools = new ProofTools(true);

            // This should be accepted, as a reasonable unifier being possible to find
            // B <- x, z <- x, B <- z
            var formula = parser.Parse("Exi x. Dis p[x,x,B] Neg Uni z. p[B,z,z]");

            var cnf = clauseConverter.Compile(formula);
            var clauses = cnf.Clauses;
            Console.WriteLine(cnf.Print());
            var resolvent = proofTools.Resolve(0, 0, clauses[0], clauses[1]);

            Assert.IsTrue(resolvent.IsLeft);

            // This should not be accepted, as a A <- x and z <- x and B <- z
            formula = parser.Parse("Exi x. Dis p[x,x,B] Neg Uni z. p[A,z,z]");

            cnf = clauseConverter.Compile(formula);
            clauses = cnf.Clauses;
            Console.WriteLine(cnf.Print());
            resolvent = proofTools.Resolve(0, 0, clauses[0], clauses[1]);

            Assert.IsTrue(resolvent.IsRight);

            formula = parser.Parse("Dis Exi x.Exi y. Con p[x, y] Neg p[y, x] Dis Exi x.Exi y. Exi z. Con p[x, y] Con p[y, z] Neg p[x, z] Dis Exi x.Neg p[x, F[x]] Exi x. p[x, x]");

            cnf = clauseConverter.Compile(formula);
            clauses = cnf.Clauses;
            Console.WriteLine(cnf.Print());
            resolvent = proofTools.Resolve(0, 0, clauses[0], clauses[1]);

            Assert.IsTrue(resolvent.IsRight);

        }

    }
}
