namespace Resolution;
using static ClausalForm;

public class ProofTools
{
    private readonly bool _debugMode = false;

    public ProofTools(bool debugMode) => _debugMode = debugMode;

    public struct MultipleClashes { public MultipleClashes() { } }


    public Either<Resolve, ResolveError> Resolve(int n1, int n2, Clause c1, Clause c2,
        HashSet<Literal> l1, HashSet<Literal> l2)
    {
        List<Change>? changes;

        try
        {
            changes = Unify(l1, l2);
        }
        catch (UnificationException ue)
        {
            var err = new ResolveError($"Clauses {c1.Print()} and {c2.Print()} do not clash. {"(" + ue.Message + ")"}", Error.NoClashesError);
            if (_debugMode)
            {
                Console.WriteLine(err.Print());
            }
            return err;
        }

        // Start checking the substitutions
        // Keep track of the substitution types
        Dictionary<string, IArgument> functions = new Dictionary<string, IArgument>();
        Dictionary<string, string> variables = new Dictionary<string, string>();

        foreach (var change in changes)
        {
            switch (change.Left, change.Right)
            {
                case (Variable v, Function f):
                    var err = HandleChange(v, f, functions, variables);
                    if (err != null) return err;
                    break;
                case (Function f, Variable v):
                    err = HandleChange(v, f, functions, variables);
                    if (err != null) return err;
                    break;
                case (Variable v1, Variable v2):
                    err = HandleChange(v1, v2, functions, variables);
                    if (err != null) return err;
                    break;
            }
        }

        if (CheckForCircularSubstitutions(variables, functions))
        {
            return new ResolveError($"The unifier of these two clauses contains circular substitutions", Error.CircularSubstitution);
        }

        var allSubstitutions = new Dictionary<string, IArgument>();
        foreach (var key in variables.Keys) allSubstitutions[key] = new Variable(variables[key]);
        foreach (var key in functions.Keys) allSubstitutions[key] = functions[key];

        // Calculate new clause
        var c1Literals = c1.Literals.ToList();
        var c2Literals = c2.Literals.ToList();

        foreach (var literal in l1)
        {
            c1Literals.Remove(literal);
        }
        foreach (var literal in l2)
        {
            c2Literals.Remove(literal);
        }

        var newLiterals = ApplySubstitutions(c1Literals, allSubstitutions);
        newLiterals.AddRange(ApplySubstitutions(c2Literals, allSubstitutions));

        var resolvent = new Clause(newLiterals);
        if (_debugMode)
        {
            foreach (var literal in c1Literals)
            {
                Console.WriteLine($"Literals on the left side {literal.Print()}");
            }
            foreach (var literal in c2Literals)
            {
                Console.WriteLine($"Literals on the right side {literal.Print()}");
            }
            foreach (var literal in newLiterals)
            {
                Console.WriteLine($"Literals on the resolvent side {literal.Print()}");
            }
            Console.WriteLine("Resolvent: " + resolvent.Print());
        }


        // Make resolution step
        var resolution = new Resolve(n1, n2, resolvent, l1, l2, allSubstitutions);

        return resolution;
    }

    /// <summary>
    /// Handle normal change from variable to function 
    /// </summary>
    /// <param name="v"></param>
    /// <param name="f"></param>
    /// <param name="functions"></param>
    /// <param name="variables"></param>
    /// <returns></returns>
    private ResolveError? HandleChange(Variable v, Function f, Dictionary<string, IArgument> functions, Dictionary<string, string> variables)
    {
        if (VariableOccurs(v.identifier, f))
        {
            {
                return new ResolveError($"Circular substitution for variable {v.identifier}", Error.CircularSubstitution);
            }
        }

        if (functions.TryGetValue(v.identifier, out var compare))
        {
            if (Eq(compare, f) == false)
            {
                {
                    return new ResolveError($"Multiple different substitutions for variable {v.identifier}", Error.InconsistentSubstitutions);
                }
            }
        }

        // Check that the variables doesn't have a substitution for either of the variables, otherwise redirect the substitutions and remove the substitution from variables
        if (variables.TryGetValue(v.identifier, out var stringCompare))
        {
            functions[stringCompare] = f;
            variables.Remove(v.identifier);
        }

        var reverseVariablesKey = variables.FirstOrDefault(x => x.Value == v.identifier).Key;
        if (reverseVariablesKey != null)
        {
            functions[reverseVariablesKey] = f;
            variables.Remove(reverseVariablesKey);
        }

        // If all goes well, add the substitution
        functions[v.identifier] = f;
        return null;
    }

    /// <summary>
    /// Handle substitution from variable to variable
    /// </summary>
    /// <param name="v1"></param>
    /// <param name="v2"></param>
    /// <param name="functions"></param>
    /// <param name="variables"></param>
    /// <returns></returns>
    private ResolveError? HandleChange(Variable v1, Variable v2, Dictionary<string, IArgument> functions, Dictionary<string, string> variables)
    {
        if (v1.identifier == v2.identifier)
        {
            return new ResolveError($"Variable {v1.Print()} occurs in both clauses", Error.NotDisjointVariables);
        }

        // Check that the substitutions are consistent
        if (functions.TryGetValue(v1.identifier, out var compare1) && functions.TryGetValue(v2.identifier, out var compare2))
        {
            if (Eq(compare1, compare2) == false)
            {
                return new ResolveError($"Multiple different substitutions for variable {v2.Print()}", Error.InconsistentSubstitutions);
            }
        }

        // Redirect substitutions 
        if (functions.TryGetValue(v1.identifier, out compare1) && !functions.TryGetValue(v2.identifier, out compare2))
        {
            functions[v2.identifier] = compare1;
        }

        // --||--
        if (!functions.TryGetValue(v1.identifier, out compare1) && functions.TryGetValue(v2.identifier, out compare2))
        {
            functions[v1.identifier] = compare2;
        }

        // If not predetermined substitution can be found, make a variable substitution
        if (!functions.TryGetValue(v1.identifier, out compare1) && !functions.TryGetValue(v2.identifier, out compare2))
        {
            variables[v1.identifier] = v2.identifier;
        }

        return null;
    }





    /// <summary>
    /// Unify two sets of literals
    /// </summary>
    /// <param name="left"></param>
    /// <param name="right"></param>
    /// <returns></returns>
    /// <exception cref="UnificationException"></exception>
    /// <exception cref="NotImplementedException"></exception>
    private List<Change> Unify(HashSet<Literal> left, HashSet<Literal> right)
    {
        // Check signs and identifiers
        var err = CheckSignsAndIdentifiers(left,right);
        if (err != null) throw err;

        // For every combination of literals, collect the substitutions.
        var uncheckedSubstitutions = new List<Change>();
        foreach (var leftLiteral in left)
        {
            foreach (var rightLiteral in right)
            {
                uncheckedSubstitutions.AddRange(Unify(leftLiteral, rightLiteral));
            }
        }

        return uncheckedSubstitutions;
    }

    /// <summary>
    /// Checks sign and identifier requirements across both sets of literals
    /// </summary>
    /// <param name="left"></param>
    /// <param name="right"></param>
    /// <returns></returns>
    private UnificationException? CheckSignsAndIdentifiers(HashSet<Literal> left,
        HashSet<Literal> right)
    {
        if (left.Count == 0 || right.Count == 0)
        {
            return new UnificationException("No literals were found in the sets of literals");
        }

        // Check signs and identifiers
        var err = CheckSignsAndIdentifiers(left);
        if (err != null) return err;

        err = CheckSignsAndIdentifiers(right);
        if (err != null) return err;

        if (left.First().Sign == right.First().Sign)
        {
            return new UnificationException("Sets of literals do not clash");
        }

        return null;
    }

    /// <summary>
    /// Checks that sign and identifier of the literal are the same for one set of literals
    /// </summary>
    /// <param name="literals"></param>
    /// <returns></returns>
    private UnificationException? CheckSignsAndIdentifiers(HashSet<Literal> literals)
    {
        // Check that sign and identifier of the literal are the same across both groups
        var firstInLeft = literals.First();
        foreach (var literalInLeft in literals)
        {
            if (firstInLeft.Sign != literalInLeft.Sign)
            {
                return new UnificationException("Signs did not match across literals");
            }

            if (firstInLeft.Identifier != literalInLeft.Identifier)
            {
                return new UnificationException("Identifiers in literals did not match");
            }
        }
        // Otherwise, nothing found in sign and identifier check 
        return null;
    }

    /// <summary>
    /// Checks for circular substitutions
    /// </summary>
    /// <param name="variables"></param>
    /// <param name="functions"></param>
    /// <returns></returns>
    private bool CheckForCircularSubstitutions(Dictionary<string, string> variables, Dictionary<string, IArgument> functions)
    {
        // Left side is dependent on the right side.
        // Dependency set contains a tuple of bool and string, where bool represents whether the variable is encased in a function
        // which is important to decide whether the dependency is problematic in a circular substitution.
        var dependencies = new Dictionary<string, HashSet<Tuple<bool,string>>>();
        foreach (var pair in variables)
        {
            if (dependencies.TryGetValue(pair.Value, out var dependency))
            {
                dependency.Add(new Tuple<bool, string>(false,pair.Key));
            }
            else
            {
                dependencies[pair.Value] = new HashSet<Tuple<bool, string>> { new(false, pair.Key) };
            }
        }

        foreach (var pair in functions)
        {
            var args = ArgumentVariables(pair.Value);
            foreach (var arg in args)
            {
                if (dependencies.TryGetValue(arg, out var dependency))
                {
                    dependency.Add(new Tuple<bool, string>(true, pair.Key));
                }
                else
                {
                    dependencies[arg] = new HashSet<Tuple<bool, string>> { new(true, pair.Key) };
                }
            }
        }

        foreach (var pair in dependencies)
        {
            // Simply DFS traversal of the dependencies
            if (CheckForCircularSubstitutions(pair.Key, new HashSet<Tuple<bool, string>>(), dependencies))
                return true;
        }
        return false;
    }

    private bool CheckForCircularSubstitutions(string pairKey, HashSet<Tuple<bool, string>> visited, Dictionary<string, HashSet<Tuple<bool,string>>> dependencies)
    {
        visited = visited.ToList().ToHashSet();
        if (!dependencies.ContainsKey(pairKey))
        {
            return false;
        }
        foreach (var current in dependencies[pairKey])
        {
            if (visited.Contains(current))
            {
                if (current.Item1)
                {
                    return true;
                }
            }
            else
            {
                visited.Add(current);

                if (CheckForCircularSubstitutions(current.Item2, visited, dependencies))
                {
                    return true;
                }
            }
        }
        return false;
    }

    /// <summary>
    /// Gets a set of all variables in a clause
    /// </summary>
    /// <param name="clause"></param>
    /// <returns></returns>
    public HashSet<string> ClauseVariables(Clause clause)
    {
        return clause.Literals.SelectMany(literal => literal.Arguments.SelectMany(ArgumentVariables)).ToHashSet();
    }

    private List<string> ArgumentVariables(IArgument argument)
    {
        if (argument.GetType() == typeof(Variable))
            return new List<string> { ((Variable)argument).identifier };
        if (argument.GetType() == typeof(Function))
            return ((Function)argument).arguments.SelectMany(ArgumentVariables).ToList();
        throw new ArgumentException();
    }

    private List<Literal> ApplySubstitutions(List<Literal> atoms, Dictionary<string,IArgument> substitutions)
    {
        List<Literal>? substituted1 = null;
        List<Literal>? substituted2 = atoms.ToList();

        while (substituted1 == null || !Eq(new Clause(substituted1), new Clause(substituted2)))
        {
            substituted1 = substituted2.ToList();
            substituted2 = substituted1.Select(atom =>
                    new Literal(atom.Identifier, atom.Sign, ApplySubstitutions(atom.Arguments, substitutions)))
                .ToList();
        }
        return substituted1;
    }

    private List<IArgument> ApplySubstitutions(List<IArgument> arguments, Dictionary<string, IArgument> substitutions)
    {
        var newArgument = new List<IArgument>();
        foreach (var argument in arguments)
        {
            if (argument.GetType() == typeof(Variable))
            {
                var variable = (Variable) argument;
                newArgument.Add(substitutions.Keys.Any(x => x == variable.identifier)
                    ? substitutions[substitutions.Keys.First(x => x == variable.identifier)]
                    : argument);
            }
            if (argument.GetType() == typeof(Function))
            {
                var function = (Function) argument;
                newArgument.Add(new Function(function.identifier,
                    ApplySubstitutions(function.arguments, substitutions)));
            }
        }
        return newArgument;
    }

    /// <summary>
    /// Tells whether a given variable occurs in a given argument
    /// </summary>
    /// <param name="varname"></param>
    /// <param name="arg"></param>
    /// <returns></returns>
    private bool VariableOccurs(string varname, IArgument arg)
    {
        if (arg.GetType() == typeof(Function))
        {
            var argT = (Function)arg;
            foreach (var ar in argT.arguments)
            {
                if (VariableOccurs(varname, ar))
                {
                    return true;
                }
            }
        }
        if (arg.GetType() == typeof(Variable))
        {
            var argT = (Variable)arg;
            return argT.identifier == varname;
        }

        return false;
    }

    public struct ResolveError
    {
        public string message;
        public Error error;
        public ResolveError(string message, Error error)
        {
            this.message = message; this.error = error;
        }

        public string Print() => error + ": " + message;
    }

    public enum Error
    {
        NoClashesError,
        InconsistentSubstitutions,
        CircularSubstitution,
        NotDisjointVariables
    }

    public class Either<Left, Right>
    {
        private readonly object _value;
        private Either(object value) { _value = value; }

        public static implicit operator Either<Left, Right>(Left value) => new(value);
        public static implicit operator Either<Left, Right>(Right value) => new(value);

        public bool IsSuccesful => _value is Left;
        public Left Resolve => (Left)_value;
        public Right Error => (Right)_value;
    }

    /// <summary>
    /// Unify two literals
    /// </summary>
    /// <param name="a1"></param>
    /// <param name="a2"></param>
    /// <returns></returns>
    /// <exception cref="UnificationException"></exception>
    private List<Change> Unify(Literal a1, Literal a2)
    {
        var substitutions = new List<Change>();
        if (a1.Identifier != a2.Identifier || a1.Sign == a2.Sign)
        {
            throw new UnificationException("Literals do not clash each other");
        }
        if (a1.Arguments.Count != a2.Arguments.Count)
        {
            throw new UnificationException("Literals did not have the same argument list length");
        }
        var iterator = a1.Arguments.Zip(a2.Arguments, (o, t) => new { Left = o, Right = t });
        foreach (var iteration in iterator)
        {
            substitutions.AddRange(Unify(iteration.Left, iteration.Right));
        }
        return substitutions;
    }

    /// <summary>
    /// Unify two arguments
    /// </summary>
    /// <param name="a1"></param>
    /// <param name="a2"></param>
    /// <returns></returns>
    /// <exception cref="UnificationException"></exception>
    private List<Change> Unify(IArgument a1, IArgument a2)
    {
        var changes = new List<Change>();
        switch (a1, a2)
        {
            case (Function f1, Function f2):
                if (f1.identifier != f2.identifier)
                {
                    throw new UnificationException("Functions differ between literals");
                }
                if (f1.arguments.Count != f2.arguments.Count)
                {
                    throw new UnificationException("Literals did not have the same argument list length");
                }

                var iterator = f1.arguments.Zip(f2.arguments, (o, t) => new { Left = o, Right = t });
                foreach (var iteration in iterator)
                {
                    changes.AddRange(Unify(iteration.Left, iteration.Right));
                }
                break;
            case (Variable v1, Variable v2):
                changes.Add(new Change(a1, a2));
                break;
            default:
                changes.Add(new Change(a1, a2));
                break;
        }
        return changes;
    }

    private class UnificationException : Exception
    {
        public UnificationException(string message) : base(message) { }
    }

    /// <summary>
    /// Renames a variable and creates the rename step to be added to the proof.
    /// </summary>
    /// <param name="oldName"></param>
    /// <param name="newName"></param>
    /// <param name="origin"></param>
    /// <param name="clause"></param>
    /// <returns></returns>
    public Rename RenameVariable(string oldName, string newName, int origin, Clause clause)
    {
        var atoms = clause.Clone();
        var subbed = ApplySubstitutions(atoms.Literals, new Dictionary<string, IArgument> { { oldName, new Variable(newName) } });
        return new Rename(origin, new Clause(subbed), oldName, newName);
    }

    public bool Eq(Clause one, Clause two)
    {
        foreach (var literals1 in one.Literals)
        {
            var equ = false;
            foreach (var atom2 in two.Literals)
            {
                equ = equ || Eq(literals1, atom2);
            }

            if (!equ)
            {
                return false;
            }
        }
        foreach (var atom1 in two.Literals)
        {
            var equ = false;
            foreach (var atom2 in one.Literals)
            {
                equ = equ || Eq(atom1, atom2);
            }

            if (!equ)
            {
                return false;
            }
        }
        return true;
    }

    public bool Eq(Literal one, Literal two)
    {
        if (one.Sign != two.Sign || one.Identifier != two.Identifier || one.Arguments.Count != two.Arguments.Count)
        {
            return false;
        }
        var iterator = one.Arguments.Zip(two.Arguments, (o, t) => new { Left = o, Right = t });
        var condition = true;
        foreach (var iteration in iterator)
        {
            condition = condition && Eq(iteration.Left, iteration.Right);
        }
        return condition;
    }

    public bool Eq(IArgument one, IArgument two)
    {
        if (one.GetType() == typeof(Variable) && two.GetType() == typeof(Variable))
        {
            var typedOne = (Variable)one;
            var typedTwo = (Variable)two;
            return typedOne.identifier == typedTwo.identifier;
        }

        if (one.GetType() == typeof(Function) && two.GetType() == typeof(Function))
        {
            var typedOne = (Function)one;
            var typedTwo = (Function)two;
            if (typedOne.arguments.Count != typedTwo.arguments.Count || typedOne.identifier != typedTwo.identifier)
            {
                return false;
            }
            var iterator = typedOne.arguments.Zip(typedTwo.arguments, (o, t) => new { Left = o, Right = t });
            var condition = true;
            foreach (var iteration in iterator)
            {
                condition = condition && Eq(iteration.Left, iteration.Right);
            }
            return condition;
        }

        return false;
    }

    public bool IsEmptyClause(Clause clause)
    {
        return Eq(clause, new Clause(new List<Literal>()));
    }

    /// <summary>
    /// Pretty print sets of literals
    /// </summary>
    /// <param name="literals"></param>
    /// <returns></returns>
    public string Print(HashSet<Literal> literals)
    {
        var result = string.Empty;
        var list = literals.ToList();

        for (var index = 0; index < list.Count; index ++)
        {
            result += list[index].Print() ;
            if (index != list.Count - 1) result += ", ";
        }

        return result;
    }

    /// <summary>
    /// A difference between a literal on the left and a literal on the right
    /// </summary>
    public class Change
    {
        public IArgument Left;
        public IArgument Right;

        public Change(IArgument left, IArgument right)
        {
            Left = left;
            Right = right;
        }
    }
}