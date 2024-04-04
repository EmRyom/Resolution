using static Resolution.ClausalForm;

namespace Resolution
{
    public class Proof
    {
        public List<IApplication> Applications { get; set; }

        public Proof(ClausalFormula formula)
        {
            Applications = new List<IApplication>();
            for (var i=1; i <= formula.Clauses.Count; i++)
            {
                Applications.Add(new Copy(formula.Clauses[i-1]));
            }
        }

        public Clause GetClause(int n)
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
        public Clause GetClause();
    }
    
    public class Copy : IApplication
    {
        public Clause Clause { get; set; }
        public Copy(Clause clause) {
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

        public Clause GetClause() => Clause;
    }

    public class Resolve : IApplication
    {
        public int FirstClause { get; set; }
        public int SecondClause { get; set; }
        public Clause Resolvent { get; set; }
        public Dictionary<string, IArgument> Substitutions { get; set; }
        public HashSet<Literal> FirstLiterals { get; set; }
        public HashSet<Literal> SecondLiterals { get; set; }
        public Resolve(int firstClause, int secondClause, Clause resolvent, HashSet<Literal> firstLiterals, HashSet<Literal> secondLiterals, Dictionary<string, IArgument> substitutions)
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
        public Clause GetClause() => Resolvent;

        public List<Literal> GetFirstLiterals() => FirstLiterals.ToList();
        public List<Literal> GetSecondLiterals() => SecondLiterals.ToList();
    }

    public class Rename : IApplication
    {
        public int origin;
        public Clause Clause { get; set; }
        public string originalName;
        public string newName;

        public Rename(int origin, Clause clause, string originalName, string newName)
        {
            this.origin = origin;
            Clause = clause;
            this.originalName = originalName;
            this.newName = newName;
        }

        public string PrintMethod() => $"Renamed variable in C<sub>{origin}</sub>";

        public string PrintSubstitutions()
        {
            return new Variable(newName).Print() + " ← " + new Variable(originalName).Print();
        }

        public Clause GetClause() => Clause;
    }
}
