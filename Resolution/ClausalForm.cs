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
        public bool Value { get; }
        public List<IArgument> Args { get; }

        public Literal(string identifier, bool value, List<IArgument> args)
        {
            Identifier = identifier;
            Value = value;
            Args = args;
        }

        public string Print()
        {
            var s = (Value ? "" : "¬ ") + Identifier;
            switch (Args.Count)
            {
                case 0:
                    return s;
                case 1:
                    s += "(" + Args.First().Print() + ")";
                    return s;
                default:
                    s += "(" + Args.First().Print();
                    foreach (IArgument arg in Args.Skip(1))
                    {
                        s += ", " + arg.Print();
                    }
                    s += ")";
                    return s;
            }
        }

        public Literal Clone()
        {
            var arguments = Args.Select(argument => argument.Clone()).ToList();
            return new Literal(Identifier, Value, arguments);
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
        public List<IArgument> args;

        public Function(string identifier, List<IArgument> args)
        {
            this.identifier = identifier;
            this.args = args;
        }

        public string Print()
        {
            var s = identifier;
            switch (args.Count)
            {
                case 0:
                    return s;
                case 1:
                    s += "[" + args.First().Print() + "]";
                    return s;
                default:
                    s += "[" + args.First().Print();
                    foreach (IArgument arg in args.Skip(1))
                    {
                        s += ", " + arg.Print();
                    }
                    s += "]";
                    return s;
            }
        }

        public IArgument Clone()
        {
            var arguments = args.Select(arg => arg.Clone()).ToList();
            return new Function(identifier, arguments);
        }
    }
}