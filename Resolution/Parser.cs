
namespace Resolution;

public class Parser
{
    private readonly bool _debugMode = false;
    private string _current = ""; // This helps for returning helpful error messages
    private Parenthesis _p = new Parenthesis();

    public Parser(bool debugMode ) { _debugMode = debugMode; }

    private class Parenthesis
    {
        private int _parenthesisDepth = 0;
        public Parenthesis() { }

        public void Increase()
        {
            _parenthesisDepth++;
        }

        public void Decrease()
        {
            _parenthesisDepth--;
            if (_parenthesisDepth < 0)
            {
                throw new ParsingException("Parentheses do not match up");
            }
        }
    }

    public GeneralForm.IFormula Parse(string toParse)
    {
        _p = new Parenthesis();
        if (toParse.Contains("_") || toParse.Contains("'"))
        {
            throw new ParsingException("The formula may not contain underscores _ and apostrophes '");
        }
        try
        {
            var r = ParseFormula(toParse);
            var s = r.Item2;

            if (_debugMode)
            {
                Console.WriteLine("Tail " + s);
            }
            while (s != "")
            {
                if (s[0] == ')' || s[0] == ' ')
                {
                    s = s.Substring(1);
                }
                else
                {
                    throw new ParsingException("Tailing formula");
                }
            }
            return r.Item1;
        }
        catch (Exception e)
        {
            throw new ParsingException(e.Message + " at ⟶ " + _current);
        }
    }

    private (GeneralForm.IFormula, string) ParseFormula(string s)
    {
        _current = s;
        if (_debugMode)
        {
            Console.WriteLine("Formula ->" + s);
        }
        if (s[0] == '(')
        {
            _p.Increase();
            return ParseFormula(s.Substring(1));
        }
        if (s[0] == ')')
        {
            _p.Decrease();
            return ParseFormula(s.Substring(1));
        }
        if (s[0] == ' ')
        {
            return ParseFormula(s.Substring(1));
        }
        if (s.Length > 6)
        {
            switch (s.Substring(0,6))
            {
                case "Biimp ":
                    return Binary(GeneralForm.BinaryOperator.BiImplication, s.Substring(5));
            }
        }
        if (s.Length > 4)
        {
            switch (s.Substring(0, 4)) {
                case "Neg ":
                    return Neg(s.Substring(4));
                case "Imp ":
                    return Binary(GeneralForm.BinaryOperator.Implies, s.Substring(4));
                case "Con ":
                    return Binary(GeneralForm.BinaryOperator.And, s.Substring(4));
                case "Dis ":
                    return Binary(GeneralForm.BinaryOperator.Or, s.Substring(4));
                case "Exi ":
                    return Quantifier(GeneralForm.QuantifierOperator.Exists, s.Substring(4));
                case "Uni ":
                    return Quantifier(GeneralForm.QuantifierOperator.Forall, s.Substring(4));
            }
        }
        var r1 = ParseIdentifier(s);
        var r2 = ParseArgs(r1.Item2);
        
        return (new GeneralForm.Atom(r1.Item1, r2.Item1), r2.Item2);
    }

    private (string,string) ParseIdentifier(string s)
    {
        _current = s;
        if (_debugMode)
        {
            Console.WriteLine("Identifier ->" + s);
        }
        string r = string.Empty;
        int cutoff = 0;
        foreach (char c in s)
        {
            if (c == '[' | c == ' ' | c == ']' | c == ',' | c == '(' | c == ')')
            {
                return (r, s.Substring(cutoff));
            }
            r += c;
            cutoff++;
        }
        return (r, s.Substring(cutoff));
    }

    private (List<GeneralForm.IArgument>, string) ParseArgs(string s)
    {
        _current = s;
        if (_debugMode)
        {
            Console.WriteLine("Args ->" + s);
        }
        List<GeneralForm.IArgument> list = new List<GeneralForm.IArgument>();
        
        if (s == string.Empty || s[0] != '[')
        {
            return (list, s);
        }

        s = s.Substring(1);
        var r = ParseArg(s);
        list.Add(r.Item1);
        s = r.Item2;

        while (true)
        {
            if (s[0] == ']')
            {
                return (list, s.Substring(1));
            }
            while (s[0] == ' ' | s[0] == ',')
            {
                s = s.Substring(1);
            }
            r = ParseArg(s);
            list.Add(r.Item1);
            s = r.Item2;
        }
    }

    private (GeneralForm.IArgument, string) ParseArg(string s)
    { 
        _current = s;
        if (_debugMode)
        {
            Console.WriteLine("Arg ->" + s);
        }
        var r = ParseIdentifier(s);

        if (!char.IsUpper(r.Item1[0]))
        {
            return (new GeneralForm.Variable(r.Item1), r.Item2);
        } 
        else
        {
            var args = ParseArgs(r.Item2);
            return (new GeneralForm.Function(r.Item1, args.Item1), args.Item2);
        }
    }

    private (GeneralForm.IFormula, string) Binary(GeneralForm.BinaryOperator biop, string s)
    {
        _current = s;
        if (_debugMode)
        {
            Console.WriteLine("Binary (" + biop + ") ->" + s);
        }
        var r1 = ParseFormula(s);
        var r2 = ParseFormula(r1.Item2);

        return (new GeneralForm.Binary(biop, r1.Item1, r2.Item1), r2.Item2);
    }

    private (GeneralForm.IFormula, string) Neg(string s)
    {
        _current = s;
        if (_debugMode)
        {
            Console.WriteLine("Neg ->" + s);
        }
        var r = ParseFormula(s);
        return (new GeneralForm.Negation(r.Item1), r.Item2);
    }

    private (GeneralForm.IFormula, string) Quantifier(GeneralForm.QuantifierOperator quan, string s)
    {
        _current = s;
        if (_debugMode)
        {
            Console.WriteLine("Quantifier (" + quan + ") ->" + s);
        }
        string variable = string.Empty;

        int cutoff = 0;

        foreach(char c in s) {
            cutoff++;
            if (c == '.')
            {
                break;
            }
            if (c == ' ')
            {
                continue;
            }
            variable += c;
        }
        if (cutoff >= s.Length)
        {
            throw new ParsingException("Quantifier has no variable bound to it");
        }

        var r = ParseFormula(s.Substring(cutoff));

        return (new GeneralForm.Quantifier(quan, new GeneralForm.Variable(variable), r.Item1), r.Item2);
    }

    public class ParsingException : Exception
    {
        public ParsingException(string message) : base(message) { }
    }
}

