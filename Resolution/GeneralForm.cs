namespace Resolution;

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
    }

    public class Variable : IArgument
    {
        public string identifier;

        public Variable(string identifier) => this.identifier = identifier;

        public string Print() => "<font color=\"#f26c18\">" + identifier + "</font>";

        public IArgument Clone() => new Variable(identifier);
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
    }
}