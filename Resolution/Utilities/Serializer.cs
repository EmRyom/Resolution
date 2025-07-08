using Newtonsoft.Json.Linq;
using static Resolution.ClausalForm;

namespace Resolution.Utilities
{
    public static class Serializer
    {
        public static JObject Export(string formula, Proof proof)
        {
            var result = Export(proof);
            result.AddFirst(new JProperty("Formula", formula));
            return result;
        }

        public static JObject Export(Proof proof)
        {
            var result = new JObject();
            for (int i = 0; i < proof.Applications.Count; i++)
                result.Add($"Application {i + 1}", Export(proof.Applications[i]));

            return result;
        }

        public static Proof ImportProof(string proof)
        {
            var applications = JObject.Parse(proof).Properties()
                .Where(x => x.Name.Contains("Application"))
                .OrderBy(x => x.Name)
                .Select(x => ImportApplication((JObject)x.Value))
                .ToList();

            return new Proof() { Applications = applications };
        }

        public static JObject Export(IApplication application)
        {
            var app = new JObject();
            switch (application)
            {
                case Copy c:
                    app.Add("ApplicationType", "Copy");
                    app.Add("Clause", Export(c.Clause.Literals));
                    return app;
                case Resolve r:
                    app.Add("ApplicationType", "Resolve");
                    app.Add("Resolvent", Export(r.Resolvent.Literals));
                    app.Add("FirstClause", r.FirstClause);
                    app.Add("SecondClause", r.SecondClause);
                    app.Add("FirstLiterals", Export(r.FirstLiterals.ToList()));
                    app.Add("SecondLiterals", Export(r.SecondLiterals.ToList()));
                    app.Add("Substitutions", Export(r.Substitutions));
                    return app;
                case Rename re:
                    app.Add("ApplicationType", "Rename");
                    app.Add("Origin", re.origin);
                    app.Add("OriginalName", re.originalName);
                    app.Add("NewName", re.newName);
                    app.Add("Clause", Export(re.Clause.Literals));
                    return app;
                default: throw new ArgumentException("Wrong type IApplication");
            }
        }

        public static IApplication ImportApplication(JObject application)
        {
            var type = (string)application.SelectToken("ApplicationType");
            switch (type)
            {
                case "Copy":
                    var literals = ImportLiterals((JObject)application.SelectToken("Clause"));
                    return new Copy(new Clause(literals));
                case "Resolve":
                    var resolventLiterals = ImportLiterals((JObject)application.SelectToken("Resolvent"));
                    var firstClause = (int)application.SelectToken("FirstClause");
                    var secondClause = (int)application.SelectToken("SecondClause");
                    var firstLiterals = ImportLiterals((JObject)application.SelectToken("FirstLiterals"));
                    var secondLiterals = ImportLiterals((JObject)application.SelectToken("SecondLiterals"));
                    var substitutions = ImportSubstitutions((JObject)application.SelectToken("Substitutions"));
                    return new Resolve(firstClause, secondClause, new Clause(resolventLiterals), firstLiterals.ToHashSet(), secondLiterals.ToHashSet(), substitutions);
                case "Rename":
                    var origin = (int)application.SelectToken("Origin");
                    var originalName = (string)application.SelectToken("OriginalName");
                    var newName = (string)application.SelectToken("NewName");
                    var literalsRename = ImportLiterals((JObject)application.SelectToken("Clause"));
                    return new Rename(origin, new Clause(literalsRename), originalName, newName);
                default: throw new ArgumentException("Wrong type Application");
            }
        }

        public static JObject Export(Dictionary<string, IArgument> substitutions)
        {
            var result = new JObject();

            foreach (var substitution in substitutions)
                result.Add(substitution.Key, Export(substitution.Value));

            return result;
        }

        public static Dictionary<string, IArgument> ImportSubstitutions(JObject subtitutions)
        {
            return subtitutions.Properties().ToDictionary(x => x.Name, x => ImportArgument((JObject)x.Value));
        }

        /// <summary>
        /// Exports literals for both clauses and sets of literals. Process is the same.
        /// </summary>
        /// <param name="literals"></param>
        /// <returns></returns>
        public static JObject Export(List<Literal> literals)
        {
            var result = new JObject();

            for (int i = 0; i < literals.Count; i++)
                result.Add($"Literal {i + 1}", Export(literals[i]));

            return result;
        }

        public static List<Literal> ImportLiterals(JObject literals)
        {
            return literals.Properties()
                .Where(x => x.Name.Contains("Literal"))
                .OrderBy(x => x.Name)
                .Select(x => ImportLiteral((JObject)x.Value))
                .ToList();
        }

        public static JObject Export(Literal literal)
        {
            var result = new JObject()
            {
                { "Sign", literal.Sign },
                { "Identifier", literal.Identifier }
            };

            var arguments = new JObject();

            for (int i = 0; i < literal.Arguments.Count; i++)
                arguments.Add($"Argument {i + 1}", Export(literal.Arguments[i]));
            
            result.Add("Arguments", arguments);
            return result;
        }

        public static Literal ImportLiteral(JObject literal)
        {
            var sign = (bool)literal.SelectToken("Sign");
            var identifier = (string)literal.SelectToken("Identifier");
            var argumentsContainer = (JObject)literal.SelectToken("Arguments");

            var arguments = argumentsContainer.Properties()
                .Where(x => x.Name.Contains("Argument"))
                .OrderBy(x => x.Name)
                .Select(x => ImportArgument((JObject)x.Value))
                .ToList();

            return new Literal(identifier, sign, arguments);
        }

        public static JObject Export(IArgument argument)
        {
            var result = new JObject();
            switch (argument)
            {
                case Function f:
                    result.Add("ArgumentType", "Function");
                    result.Add("Identifier", f.identifier);
                    var arguments = new JObject();
                    for (int i = 0; i < f.arguments.Count; i++)
                        arguments.Add($"Argument {i + 1}", Export(f.arguments[i]));
                    
                    result.Add("Arguments", arguments);
                    return result;
                case Variable v:
                    result.Add("ArgumentType", "Variable");
                    result.Add("Identifier", v.identifier);
                    return result;
                default: throw new ArgumentException("IArgument was not supported");
            }
        }

        public static IArgument ImportArgument(JObject argument)
        {
            var argumentType = (string)argument.SelectToken("ArgumentType");
            switch (argumentType)
            {
                case "Variable":
                    return new Variable((string)argument.SelectToken("Identifier"));
                case "Function":
                    var identifier = (string)argument.SelectToken("Identifier");
                    var argumentsContainer = (JObject)argument.SelectToken("Arguments");

                    var arguments = argumentsContainer.Properties()
                        .Where(x => x.Name.Contains("Argument"))
                        .OrderBy(x => x.Name)
                        .Select(x => ImportArgument((JObject)x.Value))
                        .ToList();

                    return new Function(identifier, arguments);
                default: throw new ArgumentException("Wrong type Argument");
            }
        }
    }
}
