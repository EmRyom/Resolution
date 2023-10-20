

using System.Collections;

namespace Resolution
{
    public class Proof
    {
        public List<IApplication> Applications { get; set; }

        public Proof(ClausalForm.ClausalFormula formula)
        {
            Applications = new List<IApplication>();
            for (var i=1; i <= formula.Clauses.Count; i++)
            {
                Applications.Add(new Copy(formula.Clauses[i-1]));
            }
        }

        public ClausalForm.Clause GetClause(int n)
        {
            var current = Applications[n-1];

            if (current.GetType() == typeof(Copy))
            {
                var currentT = (Copy)current;
                return currentT.Clause;
            }
            if (current.GetType() == typeof(Resolve))
            {
                var currentT = (Resolve)current;
                return currentT.Resolvent;
            }
            if (current.GetType() == typeof(Rename))
            {
                var currentT = (Rename)current;
                return currentT.Clause;
            }
            throw new ArgumentException();
        }

        // This function finds if an application is used further down the proof, with
        // the intent of allowing/disallowing its removal in the UI
        public bool MustKeepApplication(int n)
        {
            if (Applications[n - 1].GetType() == typeof(Copy))
            {
                return true;
            }
            foreach (var application in Applications)
            {
                if (application.GetType() == typeof(Resolve))
                {
                    var current = (Resolve)application;
                    if (current.FirstClause == n || current.SecondClause == n) { return true; }
                }
                if (application.GetType() == typeof(Rename))
                {
                    var current = (Rename)application;
                    if (current.origin == n) { return true; }
                }
            }
            return false;
        }

        public void DeleteApplication(int n)
        {
            bool deleted = false;
            for(int i = 0; i<Applications.Count; i++)
            {
                if (Applications[i].GetType() == typeof(Resolve))
                {
                    var current = (Resolve)Applications[i];
                    int newFirst = current.FirstClause;
                    int newSecond = current.SecondClause;
                    if (current.FirstClause >= n)
                    {
                        //current.FirstClause--;
                        newFirst = current.FirstClause-1;
                    }
                    if (current.SecondClause >= n)
                    {
                        //current.SecondClause--;
                        newSecond = current.SecondClause-1;
                    }
                    var newResolve = new Resolve(
                        newFirst,
                        newSecond,
                        current.Resolvent,
                        current.FirstLiterals,
                        current.SecondLiterals,
                        current.Substitutions);
                    Applications[i] = newResolve;
                }
                if (Applications[i].GetType() == typeof(Rename))
                {
                    var current = (Rename)Applications[i];
                    if (current.origin >= n)
                    {
                        current.origin--;
                        Applications[i] = current;
                    }
                }
                if (i + 1 == n && !deleted)
                {
                    Applications.RemoveAt(i);
                    i--;
                    deleted = true;
                } 
            }
        }

        
    }

    public interface IApplication
    {
        public string PrintMethod();
        public string PrintSubstitutions();
        public ClausalForm.Clause GetClause();
    }
    
    public class Copy : IApplication
    {
        public ClausalForm.Clause Clause { get; set; }
        public Copy(ClausalForm.Clause clause) {
            Clause = clause;
        }

        public string PrintMethod()
        {
            return "a clause in the formula";
        }

        public string PrintSubstitutions()
        {
            return "";
        }

        public ClausalForm.Clause GetClause() => Clause;
        
        
    }

    public class Resolve : IApplication
    {
        public int FirstClause { get; set; }
        public int SecondClause { get; set; }
        public ClausalForm.Clause Resolvent { get; set; }
        public Dictionary<string, ClausalForm.IArgument> Substitutions { get; set; }
        public HashSet<ClausalForm.Literal> FirstLiterals { get; set; }
        public HashSet<ClausalForm.Literal> SecondLiterals { get; set; }
        public Resolve(int firstClause, int secondClause, ClausalForm.Clause resolvent, HashSet<ClausalForm.Literal> firstLiterals, HashSet<ClausalForm.Literal> secondLiterals, Dictionary<string, ClausalForm.IArgument> substitutions)
        {
            FirstClause = firstClause;
            SecondClause = secondClause;
            Resolvent = resolvent;
            FirstLiterals = firstLiterals;
            SecondLiterals = secondLiterals;
            Substitutions = substitutions;
        }

        public string PrintMethod()
        {
            var str = "C<sub>" + FirstClause + "</sub> ⊗ C<sub>" + SecondClause + "</sub>" ;
            return str;
        }

        public string PrintSubstitutions()
        {
            var str = "";
            foreach (var substitution in Substitutions.Keys)
            {
                str += "<font color=\"#f26c18\">" + substitution + "</font>  ← " + Substitutions[substitution].Print() + ", ";
            }
            if (Substitutions.Count > 0) {
                return str.Remove(str.Length-2);
            }
            return str;
        }
        public ClausalForm.Clause GetClause() => Resolvent;

        public List<ClausalForm.Literal> GetFirstLiterals() => FirstLiterals.ToList();
        public List<ClausalForm.Literal> GetSecondLiterals() => SecondLiterals.ToList();
    }

    public class Rename : IApplication
    {
        public int origin;
        public ClausalForm.Clause Clause { get; set; }
        public string originalName;
        public string newName;

        public Rename(int origin, ClausalForm.Clause clause, string originalName, string newName)
        {
            this.origin = origin;
            this.Clause = clause;
            this.originalName = originalName;
            this.newName = newName;
        }

        public string PrintMethod()
        {
            return $"Renamed variable in C<sub>{origin}</sub>";
        }

        public string PrintSubstitutions()
        {
            return new ClausalForm.Variable(newName).Print() + " ← " + new ClausalForm.Variable(originalName).Print();
        }

        public ClausalForm.Clause GetClause() => Clause;
    }

   


    public class ProofTools
    {
        private readonly bool _debugMode = false;

        public ProofTools(bool debugMode)
        {
            _debugMode = debugMode;
        }

        //Resolve -> Try to find which atoms clash within two clauses given (by the user) 
        //Gives either 1. a resolve application 
        //             2. a prompt (bool) for the user to manually designate the atoms to resolve on (in case there's multiple)
        //             3. an error in case no clashes are found
        public Either<Resolve, MultipleClashes, ResolveError> Resolve(int n1, int n2, ClausalForm.Clause c1, ClausalForm.Clause c2)
        {
            if (_debugMode)
            {
                Console.WriteLine($"Resolving: {c1.Print()} and {c2.Print()}");
            }

            ClausalForm.Literal? a1 = null;
            ClausalForm.Literal? a2 = null;
            UnificationException? e = null;


            // First lets try to find clashing literals by iterating across all literals
            foreach (ClausalForm.Literal at1 in c1.Literals)
            {
                foreach (ClausalForm.Literal at2 in c2.Literals)
                {
                    if (at1.Identifier == at2.Identifier && at1.Value != at2.Value)
                    {
                        try
                        {
                            Unify(at1, at2);
                            // If a pair of clashing literals has already been found, prompt the user to designate the pivotal literals
                            if (a1 != null && a2 != null)
                            {
                                Console.WriteLine("Clashes on multiple atoms, Please select atoms.");
                                return new MultipleClashes();
                            }

                            a1 = at1;
                            a2 = at2;
                        }
                        catch (UnificationException ue)
                        {
                            e = ue;
                        }
                    }
                }
            }
            // If no clashing literals were found, we return the detailed UnificationException for the last unification that failed.
            if (a1 == null || a2 == null)
            {
                var detail = e != null ? "(" + e.Message + ")" : "";
                var err = new ResolveError($"Clauses {c1.Print()} and {c2.Print()} do not clash. {detail}", Error.NoClashesError);
                if (_debugMode)
                {
                    Console.WriteLine(err.Print());
                }
                return err;
            }
            // If we found a pair of clashing literals, we go on.
            return Resolve(n1,n2,c1,c2,a1,a2); 
        }

        public struct MultipleClashes { public MultipleClashes() { } }

        public Either<Resolve, MultipleClashes, ResolveError> Resolve(int n1, int n2, ClausalForm.Clause c1,
            ClausalForm.Clause c2, ClausalForm.Literal a1, ClausalForm.Literal a2)
        {
            if (_debugMode)
            {
                Console.WriteLine($"Resolving: {c1.Print()} and {c2.Print()} with {a1.Print()} and {a2.Print()}");
            }

            List<Tuple<ClausalForm.IArgument, ClausalForm.IArgument>>? substitutions;

            try
            {
                substitutions = Unify(a1, a2);
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
            
            
            if (a1.Identifier != a2.Identifier || a1.Value == a2.Value)
            {
                var err = new ResolveError($"Clauses {c1.Print()} and {c2.Print()} do not clash on clauses {a1.Print()} and {a2.Print()}", Error.NoClashesError);
                if (_debugMode)
                {
                    Console.WriteLine(err.Print());
                }
                return err;
            }

            // Keep track of the substitution types
            Dictionary<string, ClausalForm.IArgument> functions = new Dictionary<string, ClausalForm.IArgument>();
            Dictionary<string, string> variables =  new Dictionary<string, string>();

            foreach (var substitution in substitutions)
            {
                var arg1 = substitution.Item1;
                var arg2 = substitution.Item2;

                // Handle the case of one part being a variable and the other an function in this specific order
                if (arg1.GetType() == typeof(ClausalForm.Variable) && arg2.GetType() == typeof(ClausalForm.Function))
                {
                    var arg1T = (ClausalForm.Variable)arg1;
                    var arg2T = (ClausalForm.Function)arg2;
                    if (VariableOccurs(arg1T.identifier, arg2T))
                    {
                        return new ResolveError($"Circular substitution for variable {arg1T.identifier}",
                            Error.CircularSubstitution);
                    }

                    if (functions.TryGetValue(arg1T.identifier, out var compare))
                    {
                        if (!Eq(compare, arg2T, true))
                        {
                            return new ResolveError(
                                $"Multiple different substitutions for variable {arg1T.identifier}",
                                Error.InconsistentSubstitutions);
                        }
                    }

                    // Check that the variables doesn't have a substitution for either of the variables, otherwise redirect the substitutions and remove the substitution from variables
                    if (variables.TryGetValue(arg1T.identifier, out var stringCompare))
                    {
                        functions[stringCompare] = arg2T; 
                        variables.Remove(arg1T.identifier);
                    }
                    var reverseVariablesKey = variables.FirstOrDefault(x => x.Value == arg1T.identifier).Key;
                    if (reverseVariablesKey != null)
                    {
                        functions[reverseVariablesKey] = arg2T;
                        variables.Remove(reverseVariablesKey);
                    }

                    // If all goes well, add the substitution
                    functions[arg1T.identifier] = arg2T;
                }

                // Handle the same case but in reverse order (no significant changes)
                if (arg1.GetType() == typeof(ClausalForm.Function) && arg2.GetType() == typeof(ClausalForm.Variable))
                {
                    var arg1T = (ClausalForm.Variable)arg2;
                    var arg2T = (ClausalForm.Function)arg1;

                    if (VariableOccurs(arg1T.identifier, arg2T))
                    {
                        return new ResolveError($"Circular substitution for variable {arg1T.identifier}",
                            Error.CircularSubstitution);
                    }

                    if (functions.TryGetValue(arg1T.identifier, out var compare))
                    {
                        if (!Eq(compare, arg2T, true))
                        {
                            return new ResolveError($"Multiple different substitutions for variable {arg1T.identifier}",
                                Error.InconsistentSubstitutions);
                        }
                    }
                    if (variables.TryGetValue(arg1T.identifier, out var stringCompare))
                    {
                        functions[stringCompare] = arg2T;
                        variables.Remove(arg1T.identifier);
                    }
                    var reverseVariablesKey = variables.FirstOrDefault(x => x.Value == arg1T.identifier).Key;
                    if (reverseVariablesKey != null)
                    {
                        functions[reverseVariablesKey] = arg2T;
                        variables.Remove(reverseVariablesKey);
                    }
                    functions[arg1T.identifier] = arg2T;
                }

                // Handle the case of both arugments being variables.
                if (arg1.GetType() == typeof(ClausalForm.Variable) && arg2.GetType() == typeof(ClausalForm.Variable))
                {
                    var arg1T = (ClausalForm.Variable)arg1;
                    var arg2T = (ClausalForm.Variable)arg2;

                    if (arg1T.identifier == arg2T.identifier)
                    {
                        return new ResolveError($"Variable {arg1T.Print()} occurs in both clauses", Error.NotDisjointVariables);
                    }

                    // Check that the substitutions are consistent
                    if (functions.TryGetValue(arg1T.identifier, out var compare1) && functions.TryGetValue(arg2T.identifier, out var compare2)) 
                    {
                        if (!Eq(compare1, compare2, true))
                        {
                            return new ResolveError($"Multiple different substitutions for variable {arg2T.Print()}", Error.InconsistentSubstitutions);
                        }
                    }

                    // Redirect substitutions 
                    if (functions.TryGetValue(arg1T.identifier, out compare1) && !functions.TryGetValue(arg2T.identifier, out compare2))
                    {
                        functions[arg2T.identifier] = compare1;
                    }

                    // --||--
                    if (!functions.TryGetValue(arg1T.identifier, out compare1) && functions.TryGetValue(arg2T.identifier, out compare2))
                    {
                        functions[arg1T.identifier] = compare2;
                    }

                    // If not predetermined substitution can be found, make a variable substitution
                    if (!functions.TryGetValue(arg1T.identifier, out compare1) && !functions.TryGetValue(arg2T.identifier, out compare2))
                    {
                        variables[arg1T.identifier] = arg2T.identifier;
                    }
                }
            }

            if (CheckForCircularSubstitutions(variables, functions))
            {
                return new ResolveError($"The unifier of these two clauses contains circular substitutions", Error.CircularSubstitution);
            }

            var allSubstitutions = new Dictionary<string, ClausalForm.IArgument>();
            foreach (var key in variables.Keys) allSubstitutions[key] = new ClausalForm.Variable(variables[key]);
            foreach (var key in functions.Keys) allSubstitutions[key] = functions[key];

            var atoms1 = c1.Literals.ToList();
            var atoms2 = c2.Literals.ToList();
            atoms1.Remove(a1);
            atoms2.Remove(a2);

            var newAtoms = ApplySubstitutions(atoms1, allSubstitutions);
            newAtoms.AddRange(ApplySubstitutions(atoms2, allSubstitutions));

            var resolvent = ApplyFactoring(new ClausalForm.Clause(newAtoms));
            if (_debugMode)
            {
                foreach (var atom in atoms1)
                {
                    Console.WriteLine($"Literals on the left side {atom.Print()}");
                }
                foreach (var atom in atoms2)
                {
                    Console.WriteLine($"Literals on the right side {atom.Print()}");
                }
                foreach (var atom in newAtoms)
                {
                    Console.WriteLine($"Literals on the resolvent side {atom.Print()}");
                }
                Console.WriteLine("Resolvent: "+resolvent.Print());
            }

            var resolution = new Resolve(n1, n2, resolvent, new HashSet<ClausalForm.Literal>{a1}, new HashSet<ClausalForm.Literal> { a2 }, allSubstitutions);
            
            return resolution;
        }

        private bool CheckForCircularSubstitutions(Dictionary<string, string> variables, Dictionary<string, ClausalForm.IArgument> functions)
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

        public HashSet<string> ClauseVariables(ClausalForm.Clause clause)
        {
            return clause.Literals.SelectMany(atom => atom.Args.SelectMany(ArgumentVariables)).ToHashSet();
        }

        private List<string> ArgumentVariables(ClausalForm.IArgument argument)
        {
            if (argument.GetType() == typeof(ClausalForm.Variable))
                return new List<string> { ((ClausalForm.Variable)argument).identifier };
            if (argument.GetType() == typeof(ClausalForm.Function))
                return ((ClausalForm.Function)argument).args.SelectMany(ArgumentVariables).ToList();
            throw new ArgumentException();
        }


        private List<ClausalForm.Literal> ApplySubstitutions(List<ClausalForm.Literal> atoms, Dictionary<string,ClausalForm.IArgument> substitutions)
        {
            List<ClausalForm.Literal>? substituted1 = null;
            List<ClausalForm.Literal>? substituted2 = atoms.ToList();

            while (substituted1 == null || !Eq(new ClausalForm.Clause(substituted1), new ClausalForm.Clause(substituted2),true))
            {
                substituted1 = substituted2.ToList();
                substituted2 = substituted1.Select(atom =>
                        new ClausalForm.Literal(atom.Identifier, atom.Value, ApplySubstitutions(atom.Args, substitutions)))
                    .ToList();
            }
            return substituted1;
        }

        private List<ClausalForm.IArgument> ApplySubstitutions(List<ClausalForm.IArgument> arguments, Dictionary<string, ClausalForm.IArgument> substitutions)
        {
            var newArgument = new List<ClausalForm.IArgument>();
            foreach (var argument in arguments)
            {
                if (argument.GetType() == typeof(ClausalForm.Variable))
                {
                    var variable = (ClausalForm.Variable) argument;
                    newArgument.Add(substitutions.Keys.Any(x => x == variable.identifier)
                        ? substitutions[substitutions.Keys.First(x => x == variable.identifier)]
                        : argument);
                }
                if (argument.GetType() == typeof(ClausalForm.Function))
                {
                    var function = (ClausalForm.Function) argument;
                    newArgument.Add(new ClausalForm.Function(function.identifier,
                        ApplySubstitutions(function.args, substitutions)));
                }
            }
            return newArgument;
        }

        public ClausalForm.Clause ApplyFactoring(ClausalForm.Clause clause)
        {
            if (_debugMode)
            {
                Console.WriteLine("Factoring clause " + clause.Print());
            }
            var atoms = clause.Literals;
            for (int i = 0; i < atoms.Count; i++)
            {
                for (int j = i + 1; j < atoms.Count; j++)
                {
                    if (Eq(atoms[i], atoms[j], false))
                    {
                        // Check if a variable involved factoring is mentioned anywhere else, as that might affect the soundness. 
                        if (!atoms[i].Args.SelectMany(ArgumentVariables)
                                .Any(x => atoms.Where(y => y != atoms[i])
                                    .SelectMany(z => z.Args).Any(w => VariableOccurs(x, w))))
                        {
                            var removeDuplicateClause = atoms.ToList();
                            removeDuplicateClause.Remove(atoms[j]);
                            return ApplyFactoring(new ClausalForm.Clause(removeDuplicateClause));
                        }

                        if (!atoms[j].Args.SelectMany(ArgumentVariables)
                                .Any(x => atoms.Where(y => y != atoms[j])
                                    .SelectMany(z => z.Args).Any(w => VariableOccurs(x, w))))
                        {
                            var removeDuplicateClause = atoms.ToList();
                            removeDuplicateClause.Remove(atoms[j]);
                            return ApplyFactoring(new ClausalForm.Clause(removeDuplicateClause));
                        }
                    }
                }
            }

            return clause;
        }

        private bool VariableOccurs(string varname, ClausalForm.IArgument arg)
        {
            if (arg.GetType() == typeof(ClausalForm.Function))
            {
                var argT = (ClausalForm.Function)arg;
                foreach (var ar in argT.args)
                {
                    if (VariableOccurs(varname, ar))
                    {
                        return true;
                    }
                }
            }
            if (arg.GetType() == typeof(ClausalForm.Variable))
            {
                var argT = (ClausalForm.Variable)arg;
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
            MultipleClashes,
            NoClashesError,
            InconsistentSubstitutions,
            CircularSubstitution,
            NotDisjointVariables
        }

        public class Either<TLeft, TMiddle, TRight>
        {
            private readonly object _value;
            private Either(object value)
            {
                _value = value;
            }
            public static implicit operator Either<TLeft, TMiddle, TRight>(TLeft value)
            {
                return new Either<TLeft, TMiddle, TRight>(value);
            }

            public static implicit operator Either<TLeft, TMiddle, TRight>(TMiddle value)
            {
                return new Either<TLeft, TMiddle, TRight>(value);
            }

            public static implicit operator Either<TLeft, TMiddle, TRight>(TRight value)
            {
                return new Either<TLeft, TMiddle, TRight>(value);
            }
            public bool IsLeft => _value is TLeft;
            public bool IsMiddle => _value is TMiddle;
            public bool IsRight => _value is TRight;
            public TLeft AsLeft => (TLeft)_value;
            public TMiddle AsMiddle => (TMiddle)_value;
            public TRight AsRight => (TRight)_value;
        }


        private List<Tuple<ClausalForm.IArgument, ClausalForm.IArgument>> Unify(ClausalForm.Literal a1,
            ClausalForm.Literal a2)
        {
            var list = new List<Tuple<ClausalForm.IArgument, ClausalForm.IArgument>>();
            if (a1.Identifier != a2.Identifier || a1.Value == a2.Value)
            {
                throw new UnificationException("Literals do not clash each other");
            }
            if (a1.Args.Count != a2.Args.Count)
            {
                throw new UnificationException("Literals did not have the same argument list length");
            }
            var iterator = a1.Args.Zip(a2.Args, (o, t) => new { Left = o, Right = t });
            foreach (var iteration in iterator)
            {
                list.AddRange(Unify(iteration.Left, iteration.Right));
            }
            return list;
        }

        private List<Tuple<ClausalForm.IArgument, ClausalForm.IArgument>> Unify(ClausalForm.IArgument a1,
            ClausalForm.IArgument a2)
        {
            var list = new List<Tuple<ClausalForm.IArgument, ClausalForm.IArgument>>();
            if (a1.GetType() == a2.GetType())
            {
                if (a1.GetType() == typeof(ClausalForm.Function))
                {
                    var a1T = (ClausalForm.Function)a1;
                    var a2T = (ClausalForm.Function)a2;
                    if (a1T.identifier != a2T.identifier)
                    {
                        throw new UnificationException("Functions differ between atoms");
                    }
                    if (a1T.args.Count != a2T.args.Count)
                    {
                        throw new UnificationException("Literals did not have the same argument list length");
                    }

                    var iterator = a1T.args.Zip(a2T.args, (o, t) => new { Left = o, Right = t });
                    foreach (var iteration in iterator)
                    {
                        list.AddRange(Unify(iteration.Left, iteration.Right));
                    }
                }
                if (a1.GetType() == typeof(ClausalForm.Variable))
                {
                    list.Add(new Tuple<ClausalForm.IArgument, ClausalForm.IArgument>(a1, a2));
                }
            }
            else
            {
                list.Add(new Tuple<ClausalForm.IArgument, ClausalForm.IArgument>(a1, a2));
            }
            return list;
        }

        private class UnificationException : Exception
        {
            public UnificationException(string message) : base(message) { }
        }

        public Rename RenameVariable(string oldName, string newName, int origin, ClausalForm.Clause clause)
        {
            var atoms = clause.Clone();
            var subbed = ApplySubstitutions(clause.Clone().Literals,
                new Dictionary<string, ClausalForm.IArgument> { { oldName, new ClausalForm.Variable(newName) } });
            return new Rename(origin, new ClausalForm.Clause(subbed), oldName, newName);
        }

        // checks if arguments are equivalent, or identical
        public bool Eq(ClausalForm.IArgument one, ClausalForm.IArgument two, bool identical)
        {
            if (one.GetType() == typeof(ClausalForm.Variable) && two.GetType() == typeof(ClausalForm.Variable))
            {
                var typedOne = (ClausalForm.Variable)one;
                var typedTwo = (ClausalForm.Variable)two;
                return typedOne.identifier == typedTwo.identifier || !identical;
            }

            if (one.GetType() == typeof(ClausalForm.Function) && two.GetType() == typeof(ClausalForm.Function))
            {
                var typedOne = (ClausalForm.Function)one;
                var typedTwo = (ClausalForm.Function)two;
                if (typedOne.args.Count != typedTwo.args.Count || typedOne.identifier != typedTwo.identifier)
                {
                    return false;
                }
                var iterator = typedOne.args.Zip(typedTwo.args, (o, t) => new { Left = o, Right = t });
                var condition = true;
                foreach (var iteration in iterator)
                {
                    condition = condition && Eq(iteration.Left, iteration.Right, identical);
                }
                return condition;
            }

            return false;
        }

        public bool Eq(ClausalForm.Literal one, ClausalForm.Literal two, bool identical)
        {
            if (one.Value != two.Value || one.Identifier != two.Identifier || one.Args.Count != two.Args.Count)
            {
                return false;
            }
            var iterator = one.Args.Zip(two.Args, (o, t) => new { Left = o, Right = t });
            var condition = true;
            foreach (var iteration in iterator)
            {
                condition = condition && Eq(iteration.Left, iteration.Right, identical);
            }
            return condition;
        }

        public bool Eq(ClausalForm.Clause one, ClausalForm.Clause two, bool identical)
        {
            if (identical)
            {
                var iterator = one.Literals.Zip(two.Literals, (o, t) => new { Left = o, Right = t });
                var condition = true;
                foreach (var iteration in iterator)
                {
                    condition = condition && Eq(iteration.Left, iteration.Right, identical);
                }
                return condition;
            } 
            foreach (var atom1 in one.Literals)
            {
                var equ = false;
                foreach (var atom2 in two.Literals)
                {
                    equ = equ || Eq(atom1, atom2, identical);
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
                    equ = equ || Eq(atom1, atom2, identical);
                }

                if (!equ)
                {
                    return false;
                }
            }
            return true;
        }
        public bool IsEmptyClause(ClausalForm.Clause clause)
        {
            return Eq(clause, new ClausalForm.Clause(new List<ClausalForm.Literal>()), false);
        }
    }
}
