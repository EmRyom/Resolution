using Resolution;
using Isabelle;

namespace ResolutionOnline.Data
{
    public class ResolutionFlow
    {

        /// <summary>
        /// Users text entry
        /// </summary>
        public string toParse = "Imp (Uni x. (Imp p[x] q[x])) (Imp (Exi x. p[x]) (Exi x. q[x]))";
        public GeneralForm.IFormula? toConvert;
        public Proof? proof;
        public string isabelleResult;

        public ResolutionFlow(Parser parser)
        {
            toConvert = parser.Parse(toParse);
        }

        public string PrintParsed(Parser parser, ClauseConverter clauseConverter)
        {
            try
            {
                toConvert = parser.Parse(toParse);
                clauseConverter.TypeCheck(new List<GeneralForm.Variable>(), toConvert);
                string s = toConvert.Print();
                if (s[0] == '(')
                {
                    s = s.Substring(1);
                    if (s[^1] == ')')
                    {
                        s = s.Substring(0, s.Length - 1);
                    }
                }

                return s;
            }
            catch (Exception ex)
            {
                return ex.Message;
            }
        }

        public void Convert(ClauseConverter clauseConverter)
        {
            var formula = new List<ClausalForm.Clause>();
            if (toConvert != null)
                foreach (var clause in clauseConverter.Compile(toConvert).Clauses)
                {
                    formula.Add(clause);
                }

            proof = new(new ClausalForm.ClausalFormula(formula));
        }
    }
}
