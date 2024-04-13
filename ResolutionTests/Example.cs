namespace Resolution
{
    // Parser tests
    public static class Example
    {
        private static readonly Parser Parser = new Parser(true);
        public static GeneralForm.IFormula formula1 = Parser.Parse("Dis Con Uni x. p[x] q r");
        public static GeneralForm.IFormula formula2 = Parser.Parse("Dis p (Neg p)");
        public static GeneralForm.IFormula formula3 = Parser.Parse("Imp(Uni x.(Con p q[x]))(Con q p[A])");
        public static GeneralForm.IFormula formula4 = Parser.Parse("Biimp(Uni x.(Con p q[x]))(Con q p[A])");
        public static GeneralForm.IFormula formula5 = Parser.Parse("Biimp(Uni x. Exi y. (Con p q[x,B[C[D]]]))(Con q p[A[C[D,x,y]],y])");
    }
}
