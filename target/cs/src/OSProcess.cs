using System;
using System.Diagnostics;
using System.IO;

namespace OSProcesses {
  
  public class OSProcess {
    private Dafny.ISequence<Dafny.Rune> executableName;
    private Process process;
    private StreamWriter input;
    private StreamReader output;

    public static Std.Wrappers._IResult<OSProcess, Dafny.ISequence<Dafny.Rune>> Create(Dafny.ISequence<Dafny.Rune> executable, Dafny.ISequence<Dafny.Rune> arguments)
    {
      var execName = executable.ToVerbatimString(false);
      var args = arguments.ToVerbatimString(false);

      var p = new OSProcess(executable);
      try {
        var startInfo = new ProcessStartInfo(execName, args);
        startInfo.RedirectStandardInput = true;
        startInfo.RedirectStandardOutput = true;
        startInfo.RedirectStandardError = true;
        startInfo.UseShellExecute = false;
        startInfo.CreateNoWindow = true;

        p.process = Process.Start(startInfo);
        if (p.process == null) {
          var errorMessage = Dafny.Sequence<Dafny.Rune>.UnicodeFromString($"Failed to start '{executable}' process");
          return Std.Wrappers.Result<OSProcess, Dafny.ISequence<Dafny.Rune>>.create_Failure(errorMessage);
        }

        p.input = p.process.StandardInput;
        p.output = p.process.StandardOutput;

      } catch (Exception ex) {
        var errorMessage = Dafny.Sequence<Dafny.Rune>.UnicodeFromString($"Error initializing '{executable}': {ex.Message}");
        return Std.Wrappers.Result<OSProcess, Dafny.ISequence<Dafny.Rune>>.create_Failure(errorMessage);
      }

      return Std.Wrappers.Result<OSProcess, Dafny.ISequence<Dafny.Rune>>.create_Success(p);
    }

    public OSProcess(Dafny.ISequence<Dafny.Rune> executable) {
      executableName = executable;
    }

    public Dafny.ISequence<Dafny.Rune> ExecutableName() {
      return executableName;
    }

    public Std.Wrappers._IResult<_System._ITuple0, Dafny.ISequence<Dafny.Rune>> Send(Dafny.ISequence<Dafny.Rune> cmdDafny) {
      var cmd = cmdDafny.ToVerbatimString(false);
      input.WriteLine(cmd);
      input.Flush();

      var r = Std.Wrappers.Result<_System._ITuple0, Dafny.ISequence<Dafny.Rune>>.create_Success(_System.Tuple0.create());
      return r;
    }

    public Std.Wrappers._IResult<Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>> ReadLine()
    {
      var line = output.ReadLine();
      var dafnyLine = Dafny.Sequence<Dafny.Rune>.UnicodeFromString(line);
      var some = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(dafnyLine);
      var r = Std.Wrappers.Result<Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>>.create_Success(some);
      return r;
    }
  }
}
