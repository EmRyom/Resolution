namespace Resolution
{
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


    public class GeneralForm
    {
        public interface IFormula
        {
            public string Print();
            public IFormula Clone();
        }

        public class Negation : IFormula
        {
            public IFormula argument;
            public Negation(IFormula argument) => this.argument = argument;

            public string Print() => "¬ " + argument.Print();

            public IFormula Clone() => new Negation(argument.Clone());
        }

        public enum QuantifierOperator
        {
            Exists,
            Forall
        }

        public class Quantifier : IFormula
        {
            public QuantifierOperator @operator;
            public Variable argument;
            public IFormula formula;

            public Quantifier(QuantifierOperator op, Variable argument, IFormula innerFormula)
            {
                @operator = op;
                this.argument = argument;
                formula = innerFormula;
            }

            public string Print()
            {
                var s = "";
                switch (@operator)
                {
                    case QuantifierOperator.Forall:
                        s += "∀";
                        break;
                    case QuantifierOperator.Exists:
                        s += "∃";
                        break;
                }

                s += argument.Print() + ". " + formula.Print();
                return s;
            }
            public IFormula Clone() => new Quantifier(@operator, (Variable)argument.Clone(), formula.Clone());
        }

        public enum BinaryOperator
        {
            Or,
            And,
            Implies,
            BiImplication
        }


        public class Binary : IFormula
        {
            public BinaryOperator @operator;
            public IFormula arg1;
            public IFormula arg2;

            public Binary(BinaryOperator op, IFormula arg1, IFormula arg2)
            {
                @operator = op;
                this.arg1 = arg1;
                this.arg2 = arg2;
            }

            public string Print()
            {
                var s = "( " + arg1.Print();

                switch (@operator)
                {
                    case BinaryOperator.Or:
                        s += " ∨ ";
                        break;
                    case BinaryOperator.And:
                        s += " ∧ ";
                        break;
                    case BinaryOperator.BiImplication:
                        s += " ⟷ ";
                        break;
                    case BinaryOperator.Implies:
                        s += " ⟶ ";
                        break;
                }

                return s + arg2.Print() + " )";
            }

            public IFormula Clone() => new Binary(@operator, arg1.Clone(), arg2.Clone());
        }

        public class Atom : IFormula
        {
            public string identifier;
            public List<IArgument> args;

            public Atom(string identifier, List<IArgument> args)
            {
                this.identifier = identifier;
                this.args = args;
            }

            public string Print()
            {
                var s = identifier;
                if (args.Count != 0)
                {
                    s += "(";
                    for (int i = 0; i < args.Count; i++)
                    {
                        s += args[i].Print();
                        if (i != args.Count - 1)
                        {
                            s += ", ";
                        }
                    }

                    s += ")";
                }

                return s;
            }

            public IFormula Clone()
            {
                var arguments = args.Select(argument => argument.Clone()).ToList();

                return new Atom(identifier, arguments);
            }
        }

        public interface IArgument
        {
            public string Print();
            public IArgument Clone();
            public bool Eq(IArgument other);

        }

        public class Variable : IArgument
        {
            public string identifier;

            public Variable(string identifier) => this.identifier = identifier;

            public string Print() => "<font color=\"#f26c18\">" + identifier + "</font>";

            public IArgument Clone() => new Variable(identifier);

            public bool Eq(IArgument other)
            {
                var typed = (Variable)other;
                return typed.identifier == identifier;
            }
        }

        public class Function : IArgument
        {
            public string identifier;
            public bool skolem = false;
            public List<IArgument> args;

            public Function(string identifier, List<IArgument> args)
            {
                this.identifier = identifier;
                this.args = args;
            }

            public string Print()
            {
                var s = identifier;
                if (args.Count != 0)
                {
                    s += "(";
                    for (int i = 0; i < args.Count; i++)
                    {
                        s += args[i].Print();
                        if (i != args.Count - 1)
                        {
                            s += ", ";
                        }
                    }

                    s += ")";
                }

                return s;
            }

            public IArgument Clone()
            {
                var arguments = new List<IArgument>();
                foreach (IArgument argument in args)
                {
                    arguments.Add(argument.Clone());
                }

                return new Function(identifier, arguments) { skolem = true };
            }

            public bool Eq(IArgument other)
            {
                var typed = (Function)other;
                var iterator = args.Zip(typed.args, (o, t) => new { Left = o, Right = t }).ToList();
                return identifier == typed.identifier && iterator.All(x => x.Left.Eq(x.Right));
            }
        }
    }
}