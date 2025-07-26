using Resolution;

namespace CTests;

[TestClass]
public class ParserTest
{
    [TestMethod]
    public void TestParser()
    {
        var parser = new Parser(false);
        Console.WriteLine(parser.Parse("Dis Con Uni x. p[x] q r").Print());
        Console.WriteLine(parser.Parse("Dis p (Neg p)").Print());
        Console.WriteLine(parser.Parse("Imp(Uni x.(Con p q[x]))(Con q p[A])").Print());
        Console.WriteLine(parser.Parse("Biimp(Uni x.(Con p q[x]))(Con q p[A])").Print());
        Console.WriteLine(parser.Parse("Biimp(Uni x. Exi y. (Con p q[x,B[C[D]]]))(Con q p[A[C[D,x,y]],y])").Print());
    }
}