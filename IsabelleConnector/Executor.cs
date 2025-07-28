using System.Diagnostics;
using System.Text.RegularExpressions;

namespace IsabelleConnector;

public class Executor
{
    // Path to local isabelle installation.
    private readonly string isabellePath;

    private const string rootFile = """
session "Resolution_FOL" = "HOL-Library" +
  options [document = false]
  theories
    IsabelleConnector
""";

    public Executor(string isabellePath)
    {
        this.isabellePath = isabellePath;

        // Set up Resolution formalization files.
        string sourceFullPath = Path.GetFullPath(@"Resolution_FOL");
        string targetFullPath = Path.Combine(isabellePath, Path.GetFileName(sourceFullPath));

        if (!Directory.Exists(targetFullPath))
        {
            Directory.CreateDirectory(targetFullPath);
            foreach (string file in Directory.GetFiles(sourceFullPath))
            {
                string fileName = Path.GetFileName(file);
                string destFile = Path.Combine(targetFullPath, fileName);
                File.Copy(file, destFile, overwrite: true);
            }
        }

        if (!File.Exists($"{targetFullPath}/ROOT"))
        {
            File.WriteAllText($"{targetFullPath}/ROOT", rootFile);
        }
    }

    public string Execute(string proof)
    {
        string filePath = $"{isabellePath}/Resolution_FOL/IsabelleConnector.thy";
        string content = $"theory IsabelleConnector imports Resolution begin \n{proof} \nend";

        File.WriteAllText(filePath, content);

        // Prepare folder structure with proof.
        string bashPath = isabellePath + @"\contrib\cygwin\bin\bash.exe";

        string isabelleHome = Regex.Replace(
               isabellePath,
               @"^([A-Za-z]):\\",
               m => $"/cygdrive/{m.Groups[1].Value.ToLower()}/"
           ).Replace("\\", "/");

        string proofDir = $"{isabelleHome}/Resolution_FOL";

        string bashArgs = $"-lc \"export PATH={isabelleHome}/contrib/cygwin/bin:$PATH; " +
                          $"export ISABELLE_HOME={isabelleHome}; " +
                          $"{isabelleHome}/bin/isabelle build -D {proofDir}\"";

        var psi = new ProcessStartInfo
        {
            FileName = bashPath,
            Arguments = bashArgs,
            RedirectStandardOutput = true,
            RedirectStandardError = true,
            UseShellExecute = false,
            CreateNoWindow = true
        };

        using (var process = Process.Start(psi))
        {
            string output = process.StandardOutput.ReadToEnd();
            string error = process.StandardError.ReadToEnd();

            process.WaitForExit();
            return output + error;
        }
    }
}
