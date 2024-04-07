namespace Resolution;

public class ClausalForm
{
    public class ClausalFormula
    {
        public List<Clause> Clauses { get; set; }
        public ClausalFormula(List<Clause> clauses) => Clauses = clauses;

        public string Print()
        {
            switch (Clauses.Count)
            {
                case 0:
                    return "";
                case 1:
                    return Clauses[0].Print();
                default:
                    var s = "( " + Clauses[0].Print() + " )";
                    foreach (Clause clause in Clauses.Skip(1))
                    {
                        s += " ∧ ";
                        s += "( " + clause.Print() + " )";
                    }

                    return s;
            }
        }

        public ClausalFormula Clone()
        {
            var clauses = Clauses.Select(clause => clause.Clone()).ToList();
            return new ClausalFormula(clauses);
        }
    }

    public class Clause
    {
        public List<Literal> Literals { get; }
        public Clause(List<Literal> literals) => Literals = literals;

        public string Print()
        {
            switch (Literals.Count)
            {
                case 0:
                    return "{ }";
                case 1:
                    return Literals[0].Print();
                default:
                    var s = Literals[0].Print();
                    foreach (Literal atom in Literals.Skip(1))
                    {
                        s += " ∨ ";
                        s += atom.Print();
                    }
                    return s;
            }
        }

        public Clause Clone()
        {
            var atoms = Literals.Select(atom => atom.Clone()).ToList();
            return new Clause(atoms);
        }
    }

    public class Literal
    {
        public string Identifier { get; }
        public bool Sign { get; }
        public List<IArgument> Arguments { get; }

        public Literal(string identifier, bool sign, List<IArgument> arguments)
        {
            Identifier = identifier;
            Sign = sign;
            Arguments = arguments;
        }

        public string Print()
        {
            var s = (Sign ? "" : "¬ ") + Identifier;
            switch (Arguments.Count)
            {
                case 0:
                    return s;
                case 1:
                    s += "(" + Arguments.First().Print() + ")";
                    return s;
                default:
                    s += "(" + Arguments.First().Print();
                    foreach (IArgument arg in Arguments.Skip(1))
                    {
                        s += ", " + arg.Print();
                    }
                    s += ")";
                    return s;
            }
        }

        public Literal Clone()
        {
            var arguments = Arguments.Select(argument => argument.Clone()).ToList();
            return new Literal(Identifier, Sign, arguments);
        }
    }
    public interface IArgument
    {
        public string Print();
        public IArgument Clone();
    }

    public class Variable : IArgument
    {
        public string identifier;
        public Variable(string identifier)
        {
            this.identifier = char.IsLower(identifier[0])
                ? identifier
                : throw new ArgumentException($"Variable identifier must start with a lower case character");
        }
        public string Print() => "<font color=\"#f26c18\">" + identifier + "</font>";
        public IArgument Clone() => new Variable(identifier);
    }

    public class Function : IArgument
    {
        public string identifier;
        public List<IArgument> arguments;

        public Function(string identifier, List<IArgument> arguments)
        {
            this.identifier = identifier;
            this.arguments = arguments;
        }

        public string Print()
        {
            var s = identifier;
            switch (arguments.Count)
            {
                case 0:
                    return s;
                case 1:
                    s += "[" + arguments.First().Print() + "]";
                    return s;
                default:
                    s += "[" + arguments.First().Print();
                    foreach (IArgument arg in arguments.Skip(1))
                    {
                        s += ", " + arg.Print();
                    }
                    s += "]";
                    return s;
            }
        }

        public IArgument Clone()
        {
            var arguments = this.arguments.Select(arg => arg.Clone()).ToList();
            return new Function(identifier, arguments);
        }
    }
}