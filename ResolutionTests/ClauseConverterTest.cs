using Resolution;

namespace CTests
{
    [TestClass]
    public class ClauseConverterTest
    {
        [TestMethod]
        public void RemoveConnectives()
        {
            Parser parser = new Parser(false);
            ClauseConverter clauseConverter = new ClauseConverter(true);
            var formula5 = parser.Parse("Biimp(Uni x. Exi y. (Con p q[x,B[C[D]]]))(Con q p[A[C[D,x,y]],y])");
            Console.WriteLine(formula5.Print());
            formula5 = clauseConverter.RemoveBiimp(formula5);
            Console.WriteLine(formula5.Print());
            formula5 = clauseConverter.RemoveImp(formula5);
            Console.WriteLine(formula5.Print());
        }

        [TestMethod]
        public void StraightConversion()
        {
            Parser parser = new(false);
            ClauseConverter clauseConverter = new(true);
            var formula1 = parser.Parse("Con Con a b Dis Dis Neg a Neg c b");
            Console.WriteLine(formula1.Print());
            var formula2 = clauseConverter.StraightConversion(formula1);
            Console.WriteLine(formula2.Print());

            formula1 = parser.Parse("Con Con Con a b Con a Dis Dis a Dis Neg a Neg c b d");
            Console.WriteLine(formula1.Print());
            formula2 = clauseConverter.StraightConversion(formula1);
            Console.WriteLine(formula2.Print());
        }

        [TestMethod]
        public void NegInwards()
        {
            Parser parser = new Parser(false);
            ClauseConverter clauseConverter = new ClauseConverter(true);
            var formula1 = parser.Parse("Neg Con Dis a b Dis a b");
            Console.WriteLine(formula1.Print());
            formula1 = clauseConverter.MoveNegInwards(formula1);
            Console.WriteLine(formula1.Print());
        }

        [TestMethod]
        public void Distribution()
        {
            Parser parser = new Parser(false);
            ClauseConverter clauseConverter = new ClauseConverter(false);

            var formula1 = parser.Parse("Dis Con a b Con c d");
            var formula2 = parser.Parse("Dis Dis a b Con c d");
            var formula3 = parser.Parse("Dis Con a b Dis c d");
            var formula4 = parser.Parse("Dis Con a b c");
            var formula5 = parser.Parse("Dis a Con b c");
            var formula6 = parser.Parse("Con Dis Con a b c d");
            
            Console.WriteLine(formula1.Print());
            formula1 = clauseConverter.Distribute(formula1);
            var formula1Cnf = clauseConverter.StraightConversion(formula1);
            Console.WriteLine(formula1Cnf.Print());
            
            Console.WriteLine(formula2.Print());
            formula2 = clauseConverter.Distribute(formula2);
            var formula2Cnf = clauseConverter.StraightConversion(formula2);
            Console.WriteLine(formula2Cnf.Print());
            
            Console.WriteLine(formula3.Print());
            formula3 = clauseConverter.Distribute(formula3);
            var formula3Cnf = clauseConverter.StraightConversion(formula3);
            Console.WriteLine(formula3Cnf.Print());
            
            Console.WriteLine(formula4.Print());
            formula4 = clauseConverter.Distribute(formula4);
            var formula4Cnf = clauseConverter.StraightConversion(formula4);
            Console.WriteLine(formula4Cnf.Print());
            
            Console.WriteLine(formula5.Print());
            formula5 = clauseConverter.Distribute(formula5);
            var formula5Cnf = clauseConverter.StraightConversion(formula5);
            Console.WriteLine(formula5Cnf.Print());

            Console.WriteLine(formula6.Print());
            formula6 = clauseConverter.Distribute(formula6);
            var formula6Cnf = clauseConverter.StraightConversion(formula6);
            Console.WriteLine(formula6Cnf.Print());
            
        }

        [TestMethod]
        public void RenamingDuplicates()
        {
            Parser parser = new Parser(false);
            ClauseConverter clauseConverter = new ClauseConverter(false);

            var formula1 = parser.Parse("Dis Exi x. p[x] Exi x. p[x]");
            var formula2 = parser.Parse("Dis Exi x. p[x] Uni y. Exi x. p[x,y]");
            var formula3 = parser.Parse("Imp Uni x. Imp p[x] q[x] Imp Neg Exi x. p[x] Neg Exi x. q[x]");

            Console.WriteLine(formula1.Print());
            formula1 = clauseConverter.UniquefyVariables(formula1);
            Console.WriteLine(formula1.Print());

            Console.WriteLine(formula2.Print());
            formula2 = clauseConverter.UniquefyVariables(formula2);
            Console.WriteLine(formula2.Print());

            Console.WriteLine(formula3.Print());
            formula3 = clauseConverter.UniquefyVariables(formula3);
            Console.WriteLine(formula3.Print());
        }

        [TestMethod]
        public void Skolemization()
        {
            Parser parser = new Parser(false);
            ClauseConverter clauseConverter = new ClauseConverter(true);


            var formula = parser.Parse("Imp Dis Uni x. a[x] Neg a[A] Neg Con b Dis c d");
            clauseConverter.Compile(formula);


            formula = parser.Parse("Imp (Uni x. (Imp p[x] q[x])) (Imp (Exi x. p[x]) (Exi x. q[x]))");
            clauseConverter.Compile(formula);

            formula = parser.Parse("Con Con Uni x. p[x] Uni x. p[x] Uni x. p[x]");
            clauseConverter.Compile(formula);
        }

        [TestMethod]
        public void SanityCheck()
        {
            Parser parser = new Parser(false);
            ClauseConverter clauseConverter = new ClauseConverter(true);

            var formula = parser.Parse("Exi x. Exi y. Dis a[x,y] Neg a[A,y]");
            clauseConverter.Compile(formula);

            formula = parser.Parse("Exi x. Dis q[x] Dis Neg q[A] r");
            clauseConverter.Compile(formula);

            formula = parser.Parse("Uni x. Uni y. Dis a[x,y] Neg a[A,y]");
            clauseConverter.Compile(formula);

            formula = parser.Parse("Uni x. Dis q[x] Dis Neg q[A] r");
            clauseConverter.Compile(formula);


            formula = parser.Parse("Dis Uni x. q[x] Uni x. p[x]");
            clauseConverter.Compile(formula);


            formula = parser.Parse("Imp Exi x. Uni y. p[x,y] Uni y. Exi x. p[x,y]");
            clauseConverter.Compile(formula);

            formula = parser.Parse("Imp Uni x. Imp p[x] Neg Exi y. q[y,x] Imp p[A] Neg q[A,A]");
            clauseConverter.Compile(formula);

            formula = parser.Parse("Imp Con Uni x. p[x] Uni x. q[x] Uni x. Con p[x] q[x]");
            clauseConverter.Compile(formula);

            formula = parser.Parse("Imp Uni x. Exi y. Con p[x] Neg p[y] Neg q[A]");
            clauseConverter.Compile(formula);

            formula = parser.Parse("Neg Uni x. Uni y. Con Dis p[x] p[y] Dis Neg p[x] Neg p[y]");
            clauseConverter.Compile(formula);

            formula = parser.Parse("Imp Uni x. Exi y. Con p[x] Neg p[y] Neg q[A]");
            clauseConverter.Compile(formula);
        }

        [TestMethod]
        public void Weirdness()
        {
            Parser parser = new Parser(true);
            ClauseConverter clauseConverter = new(true);

            var formula = parser.Parse("Exi x.Dis Neg a[x, B] a[B, x]");
            clauseConverter.Compile(formula);

        }
            
    }
}