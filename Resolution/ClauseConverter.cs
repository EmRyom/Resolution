namespace Resolution
{
    // This clause converter class vaguely follows this short guide https://april.eecs.umich.edu/courses/eecs492_w10/wiki/images/6/6b/CNF_conversion.pdf
    public class ClauseConverter
    {
        private readonly bool _debugging;

        public ClauseConverter(bool b) { _debugging = b; }

        public ClausalForm.ClausalFormula Compile(GeneralForm.IFormula formula)
        {
            var f = (GeneralForm.IFormula)new GeneralForm.Negation(formula);

            if (_debugging) { Console.WriteLine("Original :"+f.Print()); }
            TypeCheck(new List<GeneralForm.Variable>(), f);

            f = RemoveBiimp(f);
            f = RemoveImp(f);
            if (_debugging) { Console.WriteLine("Removed imp/biimp :\n" + f.Print()); }

            f = MoveNegInwards(f);
            if (_debugging) { Console.WriteLine("Moved neg :\n" + f.Print()); }
            
            f = UniquefyVariables(f);
            if (_debugging) { Console.WriteLine("Unique vars :\n" + f.Print()); }

            f = Skolemize(f);
            if (_debugging) { Console.WriteLine("Skolemized :\n" + f.Print()); }
            
            f = DropUniversals(f);
            if (_debugging) { Console.WriteLine("Unis dropped :\n" + f.Print()); }

            f = Distribute(f);
            if (_debugging) { Console.WriteLine("AND OR dist :\n" + f.Print()); }
            
            // This is a conversion from the GeneralForm class to the ClausalForm class, which enforces some properties using the class
            var c = StraightConversion(f);
            if (_debugging) { Console.WriteLine("Conversion :\n" + c.Print()); }

            return c;
        }

        private void VerifyArgumentsTypeCheck(List<GeneralForm.Variable> vars, GeneralForm.IArgument arg)
        {
            if (arg.GetType() == typeof(GeneralForm.Variable))
            {
                var argT = (GeneralForm.Variable)arg;
                if (!vars.Select(x => x.identifier).Contains(argT.identifier))
                {
                    throw new ArgumentException("Variable " + arg.Print() + " is not bound to a quantifier");
                }
            }
            if (arg.GetType() == typeof(GeneralForm.Function))
            {
                var argT = (GeneralForm.Function) arg;
                foreach (var v in argT.args)
                {
                    VerifyArgumentsTypeCheck(vars, v);
                }
            }
        }

        // Type check is used to check that every variable has a quantifier, and that every variable has a quantifier, and also that there's not twice the same variable quantified in the same scope
        public void TypeCheck(List<GeneralForm.Variable> vars, GeneralForm.IFormula formula) 
        {
            vars = vars.ToList();
            if (formula.GetType() == typeof(GeneralForm.Binary))
            {
                var f = (GeneralForm.Binary)formula;
                TypeCheck(vars, f.arg1);
                TypeCheck(vars, f.arg2);
            }
            if (formula.GetType() == typeof(GeneralForm.Quantifier))
            {
                var f = (GeneralForm.Quantifier)formula;
                if (vars.Select(x => x.identifier).Contains(f.argument.identifier))
                {
                    throw new ArgumentException("Variable " + f.argument.identifier + " is quantified more than once in this context");
                }
                vars.Add(f.argument);
                TypeCheck(vars, f.formula);
            }
            if (formula.GetType() == typeof(GeneralForm.Negation))
            {
                var f = (GeneralForm.Negation)formula;
                TypeCheck(vars, f.argument);
            }
            if (formula.GetType() == typeof(GeneralForm.Atom))
            {
                var f = (GeneralForm.Atom)formula;
                foreach (var arg in f.args)
                {
                    VerifyArgumentsTypeCheck(vars, arg);
                }
            }
        }

        //distribute /\ over \/ such that it becomes a CNF
        public GeneralForm.IFormula Distribute(GeneralForm.IFormula formula) 
        {
            var redistribute = false;
            if (formula.GetType() == typeof(GeneralForm.Binary))
            {
                var f = (GeneralForm.Binary)formula;
                if (GeneralForm.BinaryOperator.Or == f.@operator)
                {
                    var arg1 = f.arg1;
                    var arg2 = f.arg2;
                    if (arg1.GetType() == typeof(GeneralForm.Binary))
                    {
                        var arg1T = (GeneralForm.Binary)arg1;
                        switch (arg1T.@operator)
                        {
                            case GeneralForm.BinaryOperator.And:
                                var newArg1 = Distribute(new GeneralForm.Binary(GeneralForm.BinaryOperator.Or, arg1T.arg1, arg2));
                                var newArg2 = Distribute(new GeneralForm.Binary(GeneralForm.BinaryOperator.Or, arg1T.arg2, arg2));
                                return new GeneralForm.Binary(GeneralForm.BinaryOperator.And, newArg1, newArg2);
                        }
                    }
                    if (arg2.GetType() == typeof(GeneralForm.Binary))
                    {
                        var arg2T = (GeneralForm.Binary)arg2;
                        switch (arg2T.@operator)
                        {
                            case GeneralForm.BinaryOperator.And:
                                var newArg1 = Distribute(new GeneralForm.Binary(GeneralForm.BinaryOperator.Or, arg2T.arg1, arg1));
                                var newArg2 = Distribute(new GeneralForm.Binary(GeneralForm.BinaryOperator.Or, arg2T.arg2, arg1));
                                return new GeneralForm.Binary(GeneralForm.BinaryOperator.And, newArg1, newArg2);
                        }
                    }
                }

                // Keep recursively distributing if applying the function again makes the formula change
                if (Distribute(f.arg1) != f.arg1)
                {
                    redistribute = true;
                    f.arg1 = Distribute(f.arg1);
                }

                if (Distribute(f.arg2) != f.arg2)
                {
                    redistribute = true;
                    f.arg2 = Distribute(f.arg2);
                }

                formula = f;
            }

            return redistribute ? Distribute(formula) : formula;
        }


        private GeneralForm.IArgument ReplaceUniversalVars(string oldName, string newName, GeneralForm.IArgument arg)
        {
            if (arg.GetType() == typeof(GeneralForm.Function))
            {
                var f = (GeneralForm.Function)arg;
                f.args = f.args.Select(x => ReplaceUniversalVars(oldName, newName, x)).ToList();
                return f;
            }
            if (arg.GetType() == typeof(GeneralForm.Variable))
            {
                var f = (GeneralForm.Variable)arg;
                if (f.identifier == oldName)
                {
                    return new GeneralForm.Variable(newName);
                } return f;
            }
            throw new ArgumentException("Argument did not have a valid type");
        }

        private GeneralForm.IFormula ReplaceUniversalVars(string oldName, string newName, GeneralForm.IFormula formula)
        {
            if (formula.GetType() == typeof(GeneralForm.Binary))
            {
                var f = (GeneralForm.Binary)formula;
                f.arg1 = ReplaceUniversalVars(oldName, newName, f.arg1);
                f.arg2 = ReplaceUniversalVars(oldName, newName, f.arg2);
                return f;
            }
            if (formula.GetType() == typeof(GeneralForm.Negation))
            {
                var f = (GeneralForm.Negation)formula;
                f.argument = ReplaceUniversalVars(oldName, newName, f.argument);
                return f;
            }
            if (formula.GetType() == typeof(GeneralForm.Quantifier))
            {
                var f = (GeneralForm.Quantifier)formula;
                f.formula = ReplaceUniversalVars(oldName, newName, f.formula);
                return f;
            }
            if (formula.GetType() == typeof(GeneralForm.Atom))
            {
                var f = (GeneralForm.Atom)formula;
                f.args = f.args.Select(x => ReplaceUniversalVars(oldName, newName, x)).ToList();
                return f;
            }
            return formula; 
        }

        // Remove the universal quantifiers
        public GeneralForm.IFormula DropUniversals(GeneralForm.IFormula formula)
        {
            if (formula.GetType() == typeof(GeneralForm.Binary))
            {
                var f = (GeneralForm.Binary)formula;
                f.arg1 = DropUniversals(f.arg1);
                f.arg2 = DropUniversals(f.arg2);
                return f;
            }
            if (formula.GetType() == typeof(GeneralForm.Negation))
            {
                var f = (GeneralForm.Negation)formula;
                f.argument = DropUniversals(f.argument);
                return f;
            }
            if (formula.GetType() == typeof(GeneralForm.Quantifier))
            {
                var f = (GeneralForm.Quantifier)formula;
                // ReplaceUniversalVars does not change anything as it is not necessary to make universally quantified variables unique, as opposed to existentially quantified variables
                // Keep the functionality in case it is proven false later.
                f.formula = ReplaceUniversalVars(f.argument.identifier, f.argument.identifier, f.formula);
                return DropUniversals(f.formula);
            }
            return formula;
        }

        public GeneralForm.IFormula RemoveBiimp(GeneralForm.IFormula formula)
        {
            if (formula.GetType() == typeof(GeneralForm.Binary))
            {
                var f = (GeneralForm.Binary)formula;
                if (GeneralForm.BinaryOperator.BiImplication == f.@operator)
                {
                    var arg1 = RemoveBiimp(new GeneralForm.Binary(GeneralForm.BinaryOperator.Implies, f.arg1, f.arg2));
                    var arg2 = RemoveBiimp(new GeneralForm.Binary(GeneralForm.BinaryOperator.Implies, f.arg2, f.arg1));
                    return new GeneralForm.Binary(GeneralForm.BinaryOperator.And, arg1, arg2);
                }
                else
                {
                    f.arg1 = RemoveBiimp(f.arg1);
                    f.arg2 = RemoveBiimp(f.arg2);
                    return f;
                }
            }
            if (formula.GetType() == typeof(GeneralForm.Negation))
            {
                var f = (GeneralForm.Negation)formula;
                f.argument = RemoveBiimp(f.argument);
                return f;
            }
            if (formula.GetType() == typeof(GeneralForm.Quantifier))
            {
                var f = (GeneralForm.Quantifier)formula;
                f.formula = RemoveBiimp(f.formula);
                return f;
            }
            return formula;
        }

        public GeneralForm.IFormula RemoveImp(GeneralForm.IFormula formula)
        {
            if (formula.GetType() == typeof(GeneralForm.Binary))
            {
                var f = (GeneralForm.Binary)formula;
                if (GeneralForm.BinaryOperator.Implies == f.@operator)
                {
                    var arg1 = new GeneralForm.Negation(RemoveImp(f.arg1));
                    var arg2 = RemoveImp(f.arg2);
                    return new GeneralForm.Binary(GeneralForm.BinaryOperator.Or, arg1, arg2);
                }
                else
                {
                    f.arg1 = RemoveImp(f.arg1);
                    f.arg2 = RemoveImp(f.arg2);
                    return f;
                }
            }
            if (formula.GetType() == typeof(GeneralForm.Negation))
            {
                var f = (GeneralForm.Negation)formula;
                f.argument = RemoveImp(f.argument);
                return f;
            }
            if (formula.GetType() == typeof(GeneralForm.Quantifier))
            {
                var f = (GeneralForm.Quantifier)formula;
                f.formula = RemoveImp(f.formula);
                return f;
            }
            return formula;
        }

        public GeneralForm.IFormula MoveNegInwards(GeneralForm.IFormula formula)
        {
            if (formula.GetType() == typeof(GeneralForm.Negation))
            {
                var f = (GeneralForm.Negation)formula;
                var arg = f.argument;
                if (arg.GetType() == typeof(GeneralForm.Binary))
                {
                    GeneralForm.Binary argu = (GeneralForm.Binary)f.argument;
                    switch (argu.@operator)
                    {
                        case GeneralForm.BinaryOperator.Or:
                            return MoveNegInwards(new GeneralForm.Binary(GeneralForm.BinaryOperator.And, new GeneralForm.Negation(argu.arg1), new GeneralForm.Negation(argu.arg2)));
                        case GeneralForm.BinaryOperator.And:
                            return MoveNegInwards(new GeneralForm.Binary(GeneralForm.BinaryOperator.Or, new GeneralForm.Negation(argu.arg1), new GeneralForm.Negation(argu.arg2)));
                        // While it is formally possible to move negation inwards on Biimplication and Implication, this should never occur in the program as the connectives have been removed.
                        case GeneralForm.BinaryOperator.BiImplication:
                            throw new Exception("MoveNegInwards on Biimplication is Impossible");
                        case GeneralForm.BinaryOperator.Implies:
                            throw new Exception("MoveNegInwards on Implies is Impossible");
                    }
                }
                if (arg.GetType() == typeof(GeneralForm.Negation))
                {
                    var argArg = (GeneralForm.Negation)arg;
                    return MoveNegInwards(argArg.argument);
                }
                if (arg.GetType() == typeof(GeneralForm.Quantifier))
                {
                    GeneralForm.Quantifier quantifier = (GeneralForm.Quantifier)arg;
                    switch (quantifier.@operator)
                    {
                        case GeneralForm.QuantifierOperator.Exists:
                            quantifier.@operator = GeneralForm.QuantifierOperator.Forall;
                            quantifier.formula = MoveNegInwards(new GeneralForm.Negation(quantifier.formula));
                            return quantifier;
                        case GeneralForm.QuantifierOperator.Forall:
                            quantifier.@operator = GeneralForm.QuantifierOperator.Exists;
                            quantifier.formula = MoveNegInwards(new GeneralForm.Negation(quantifier.formula));
                            return quantifier;
                    }
                }
            }
            if (formula.GetType() == typeof(GeneralForm.Binary))
            {
                var f = (GeneralForm.Binary)formula;
                f.arg1 = MoveNegInwards(f.arg1);
                f.arg2 = MoveNegInwards(f.arg2);
                return f;
            }
            if (formula.GetType() == typeof(GeneralForm.Quantifier))
            {
                var f = (GeneralForm.Quantifier)formula;
                f.formula = MoveNegInwards(f.formula);
                return f;
            }
            return formula;
        }

        // Instantiate the arguments of a literal in class dedicated to the clausal form
        private ClausalForm.IArgument ConvertArgument(GeneralForm.IArgument arg)
        {
            if (arg.GetType() == typeof(GeneralForm.Function))
            {
                var f = (GeneralForm.Function)arg;
                var args = f.args.Select(x => ConvertArgument(x)).ToList();
                return new ClausalForm.Function(f.identifier, args);
            }
            if (arg.GetType() == typeof(GeneralForm.Variable))
            {
                var f = (GeneralForm.Variable)arg;
                return new ClausalForm.Variable(f.identifier);
            }
            throw new ArgumentException("Argument did not have a valid type");
        }

        private List<GeneralForm.IFormula> Flatten(GeneralForm.BinaryOperator op, GeneralForm.IFormula formula)
        {
            var flattened = new List<GeneralForm.IFormula>();
            if (formula.GetType() == typeof(GeneralForm.Binary))
            {
                var f = (GeneralForm.Binary)formula;
                if (f.@operator.Equals(op))
                {
                    flattened.AddRange(Flatten(op, f.arg1));
                    flattened.AddRange(Flatten(op, f.arg2));
                }
                else
                {
                    flattened.Add(f);
                }
            }
            else
            {
                flattened.Add(formula);
            }
            return flattened;
        }


        
        public ClausalForm.ClausalFormula StraightConversion(GeneralForm.IFormula formula, bool debugging = false)
        {
            // First flatten on AND, generating a list from a tree
            var flattened1 = Flatten(GeneralForm.BinaryOperator.And, formula);
            if (debugging)
            {
                Console.WriteLine(String.Join(" AND ", flattened1.Select(x => x.Print()).ToList()));
            }
            // Then flatten on OR for every item that was flattened on AND
            var flattened2 = flattened1.Select(x => Flatten(GeneralForm.BinaryOperator.Or, x)).ToList();
            if (debugging)
            {
                Console.WriteLine(String.Join(" AND ", flattened2.Select(x => x.Select(y => y.Print()).ToList()).ToList().Select(x => String.Join(" OR ", x)).ToList()));
            }
            var clauses = new List<ClausalForm.Clause>();
            foreach (List<GeneralForm.IFormula> l in flattened2)
            {
                var atoms = new List<ClausalForm.Literal>();
                foreach (GeneralForm.IFormula f in l)
                {
                    // Embed the value of the atom into the literal
                    if (f.GetType() == typeof(GeneralForm.Atom))
                    {
                        var sub = (GeneralForm.Atom)f;
                        atoms.Add(new ClausalForm.Literal(sub.identifier, true, sub.args.Select(x => ConvertArgument(x)).ToList()));
                    }
                    else if (f.GetType() == typeof(GeneralForm.Negation))
                    {
                        var sub = (GeneralForm.Negation)f;
                        var sub2 = sub.argument;
                        if (sub2.GetType() == typeof(GeneralForm.Atom))
                        {
                            var sub3 = (GeneralForm.Atom)sub2;
                            atoms.Add(new ClausalForm.Literal(sub3.identifier, false, sub3.args.Select(x => ConvertArgument(x)).ToList()));
                        }
                    }
                }
                var clause = new ClausalForm.Clause(atoms);
                clauses.Add(clause);
            }
            return new ClausalForm.ClausalFormula(clauses);
        }


        private List<GeneralForm.Variable> CollectVars(GeneralForm.IFormula formula)
        {
            if (_debugging)
            {
                Console.WriteLine($"Collecting vars for {formula.Print()}");
            }
            var variables = new List<GeneralForm.Variable>();
            if (formula.GetType() == typeof(GeneralForm.Binary))
            {
                var f = (GeneralForm.Binary)formula;
                variables.AddRange(CollectVars(f.arg1));
                variables.AddRange(CollectVars(f.arg2));
            }
            if (formula.GetType() == typeof(GeneralForm.Quantifier))
            {
                var f = (GeneralForm.Quantifier)formula;
                if (f.@operator == GeneralForm.QuantifierOperator.Exists)
                {
                    variables.Add(f.argument);  
                }
                variables.AddRange(CollectVars(f.formula));
            }
            if (formula.GetType() == typeof(GeneralForm.Negation))
            {
                var f = (GeneralForm.Negation)formula;
                variables.AddRange(CollectVars(f.argument));
            }

            if (_debugging)
            {
                Console.WriteLine($"Vars collected: {string.Join(",", variables.Select(x => x.identifier))}");
            }
            return variables;
        }

        private List<Dictionary<GeneralForm.Variable, String>> RenameDuplicates(List<GeneralForm.Variable> variables)
        {
            List<Dictionary<GeneralForm.Variable, String>> replacements = new List<Dictionary<GeneralForm.Variable, String>>();
            foreach (var variable in variables)
            {

                if (replacements.Select(x => x.Keys).Where(x => x.Contains(variable)).ToList().Any())
                {
                    continue;
                }
                HashSet<GeneralForm.Variable> duplicates = new HashSet<GeneralForm.Variable>(variables.Where(x => x.identifier == variable.identifier).ToList());
                if (duplicates.Count < 2)
                {
                    continue;
                }

                if (_debugging)
                {
                    Console.WriteLine($"Duplicates found: {string.Join(",",duplicates.Select(x => x.identifier))}");
                }
                Dictionary<GeneralForm.Variable, string> newNames = new Dictionary<GeneralForm.Variable, string>();
                int ident = 0;
                foreach (var v in duplicates)
                {
                    string toRepeat = "";
                    for (int i = 0; i < ident; i++)
                    {
                        toRepeat += "'";
                    }
                    newNames.Add(v,v.identifier + toRepeat);
                    ident++;
                }
                replacements.Add(newNames);
            }
            return replacements;
        }

        private GeneralForm.IArgument TraverseRename(string oldName, string newName, GeneralForm.IArgument arg)
        {
            if (arg.GetType() == typeof(GeneralForm.Function))
            {
                var f = (GeneralForm.Function)arg;
                f.args = f.args.Select(x => TraverseRename(oldName, newName, x)).ToList();
            }
            if (arg.GetType() == typeof(GeneralForm.Variable))
            {
                var f = (GeneralForm.Variable)arg;
                if (f.identifier == oldName)
                {
                    f.identifier = newName;
                }
            }
            return arg;
        }

        private GeneralForm.IFormula TraverseRename(String oldName, String newName, GeneralForm.IFormula formula)
        {
            if (formula.GetType() == typeof(GeneralForm.Binary))
            {
                var f = (GeneralForm.Binary)formula;
                f.arg1 = TraverseRename(oldName, newName, f.arg1);
                f.arg2 = TraverseRename(oldName, newName, f.arg2);
            }
            if (formula.GetType() == typeof(GeneralForm.Negation))
            {
                var f = (GeneralForm.Negation)formula;
                f.argument = TraverseRename(oldName, newName, f.argument);
            }
            if (formula.GetType() == typeof(GeneralForm.Quantifier))
            {
                var f = (GeneralForm.Quantifier)formula;
                f.formula = TraverseRename(oldName, newName, f.formula);
            }
            if (formula.GetType() == typeof(GeneralForm.Atom))
            {
                var f = (GeneralForm.Atom)formula;
                f.args = f.args.Select(x => TraverseRename(oldName, newName, x)).ToList();
            }
            return formula;
        }

        private GeneralForm.IFormula TraverseRename(Dictionary<GeneralForm.Variable, String> renamings, GeneralForm.IFormula formula)
        {
            if (formula.GetType() == typeof(GeneralForm.Binary))
            { 
                var f = (GeneralForm.Binary) formula;
                f.arg1 = TraverseRename(renamings, f.arg1);
                f.arg2 = TraverseRename(renamings, f.arg2);
                return f;
            }
            if (formula.GetType() == typeof(GeneralForm.Negation))
            { 
                var f = (GeneralForm.Negation) formula;
                f.argument = TraverseRename(renamings, f.argument);
                return f;
            }
            if (formula.GetType() == typeof(GeneralForm.Quantifier))
            {
                var f = (GeneralForm.Quantifier) formula;
                if (renamings.ContainsKey(f.argument))
                {
                    f.formula = TraverseRename(f.argument.identifier, renamings[f.argument], f.formula);
                    f.argument.identifier = renamings[f.argument];
                    return f;
                }
                else
                {
                    f.formula = TraverseRename(renamings, f.formula);
                    return f;
                }
            }
            return formula;
        }

        // 
        public GeneralForm.IFormula UniquefyVariables(GeneralForm.IFormula formula)
        {
            GeneralForm.IFormula result = formula.Clone();
            var variables = CollectVars(result);
            if (_debugging)
            {
                var s = string.Join(",", variables.Select(x => x.identifier));
                Console.WriteLine($"All {variables.Count} variables found in formula: {s}");
            }
            foreach (var duplicate in RenameDuplicates(variables))
            {
                result = TraverseRename(duplicate, result);
            }
            return result;
        }

        private string CapitalizeFirst(string s)
        {
            if (s.Length == 1)
                return "" + char.ToUpper(s[0]);
            return "" + char.ToUpper(s[0]) + s.Substring(1);
        }

        private GeneralForm.IArgument TraverseSkolemize(List<GeneralForm.Variable> encapsulating, List<GeneralForm.Variable> instantiatedExistVariables,
            GeneralForm.IArgument argument)
        {
            encapsulating = encapsulating.ToList();
            instantiatedExistVariables = instantiatedExistVariables.ToList();
            if (argument.GetType() == typeof(GeneralForm.Function))
            {
                var f = (GeneralForm.Function)argument;
                f.args = f.args.Select(x => TraverseSkolemize(encapsulating, instantiatedExistVariables, x)).ToList();
                return f;
            }
            if (argument.GetType() == typeof(GeneralForm.Variable))
            {
                var f = (GeneralForm.Variable)argument;
                if (instantiatedExistVariables.Select(x => x.identifier).Contains(f.identifier))
                {
                    return new GeneralForm.Function(CapitalizeFirst(f.identifier) + "'", encapsulating.Select(x => (GeneralForm.IArgument) x).ToList())
                        {
                            skolem = true
                        };
                }
            }
            return argument;
        }

        private GeneralForm.IFormula TraverseSkolemize(List<GeneralForm.Variable> encapsulating, List<GeneralForm.Variable> instantiatedExistVariables, GeneralForm.IFormula formula)
        {
            encapsulating = encapsulating.ToList();
            instantiatedExistVariables = instantiatedExistVariables.ToList();
            if (formula.GetType() == typeof(GeneralForm.Binary))
            {
                var f = (GeneralForm.Binary)formula;
                f.arg1 = TraverseSkolemize(encapsulating, instantiatedExistVariables, f.arg1);
                f.arg2 = TraverseSkolemize(encapsulating, instantiatedExistVariables, f.arg2);
                return f;
            }
            if (formula.GetType() == typeof(GeneralForm.Negation))
            {
                var f = (GeneralForm.Negation)formula;
                f.argument = TraverseSkolemize(encapsulating, instantiatedExistVariables, f.argument);
                return f;
            }
            if (formula.GetType() == typeof(GeneralForm.Quantifier))
            {
                var f = (GeneralForm.Quantifier)formula;
                if (f.@operator == GeneralForm.QuantifierOperator.Exists)
                {
                    instantiatedExistVariables.Add(f.argument);
                    return TraverseSkolemize(encapsulating, instantiatedExistVariables, f.formula);
                }
                if (f.@operator == GeneralForm.QuantifierOperator.Forall)
                {
                    encapsulating.Add(f.argument);
                    f.formula = TraverseSkolemize(encapsulating, instantiatedExistVariables, f.formula);
                    return f;
                }
            }
            if (formula.GetType() == typeof(GeneralForm.Atom))
            {
                var f = (GeneralForm.Atom)formula;
                f.args = f.args.Select(x => TraverseSkolemize(encapsulating, instantiatedExistVariables, x)).ToList();
                return f;
            }

            return formula;
        }

        public GeneralForm.IFormula Skolemize(GeneralForm.IFormula formula)
        {
            return TraverseSkolemize(new List<GeneralForm.Variable>(), new List<GeneralForm.Variable>(), formula);
        }
    }
}
