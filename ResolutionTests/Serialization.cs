using Resolution;
using Resolution.Utilities;

namespace CTests;

[TestClass]
public class Serialization
{
    [TestMethod]
    public void XmlTester()
    {
        var formula = "Imp (Uni x. (Imp p[x] q[x])) (Imp (Exi x. p[x]) (Exi x. q[x]))";
        var parser = new Parser(true);
        var converter = new ClauseConverter(true);

        var proof = new Proof(converter.Compile(parser.Parse(formula)));

        var serialized = Serializer.Export(proof);

        formula = "Dis Exi x.Exi y. Con p[x, y] Neg p[y, x] Dis Exi x.Exi y. Exi z. Con p[x, y] Con p[y, z] Neg p[x, z] Dis Exi x.Neg p[x, F[x]] Exi x. p[x, x]";

        serialized = Serializer.Export(new Proof(converter.Compile(parser.Parse(formula))));
    }
}
