package OSProcesses;

import java.io.*;

public class OSProcess {
    private dafny.DafnySequence<? extends dafny.CodePoint> executableName;
    private Process process;
    private PrintWriter input;
    private BufferedReader output;

    public static Std.Wrappers.Result<OSProcess, dafny.DafnySequence<? extends dafny.CodePoint>> Create(
        dafny.DafnySequence<? extends dafny.CodePoint> executable,
        dafny.DafnySequence<? extends dafny.CodePoint> arguments)
    {
      String execName = executable.verbatimString();
      String args = arguments.verbatimString();

      OSProcess p = new OSProcess(executable);
      try {
          ProcessBuilder pb = new ProcessBuilder(execName, args); // TODO: is this right if "arguments" contains several arguments?
          pb.redirectErrorStream(true);
          p.process = pb.start();

          p.input = new PrintWriter(p.process.getOutputStream(), true);
          p.output = new BufferedReader(new InputStreamReader(p.process.getInputStream()));

      } catch (Exception ex) {
          String javaErrorMessage = "Error initializing '" + executable + "': " + ex.getMessage();
          dafny.DafnySequence<? extends dafny.CodePoint> errorMessage = dafny.DafnySequence.asUnicodeString(javaErrorMessage);
          return Std.Wrappers.Result.<OSProcess, dafny.DafnySequence<? extends dafny.CodePoint>>create_Failure(
              ((dafny.TypeDescriptor<OSProcess>)(java.lang.Object)dafny.TypeDescriptor.reference(OSProcess.class)),
              dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR),
              errorMessage);
      }

      Std.Wrappers.Result<OSProcess, dafny.DafnySequence<? extends dafny.CodePoint>> r =
          Std.Wrappers.Result.<OSProcess, dafny.DafnySequence<? extends dafny.CodePoint>>create_Success(
              ((dafny.TypeDescriptor<OSProcess>)(java.lang.Object)dafny.TypeDescriptor.reference(OSProcess.class)),
              dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR),
              p);
      return r;
    }

    public OSProcess(dafny.DafnySequence<? extends dafny.CodePoint> executable) {
        executableName = executable;
    }

    public dafny.DafnySequence<? extends dafny.CodePoint> ExecutableName() {
        return executableName;
    }

    public Std.Wrappers.Result<dafny.Tuple0, dafny.DafnySequence<? extends dafny.CodePoint>> Send(
        dafny.DafnySequence<? extends dafny.CodePoint> cmdDafny)
    {
        String cmd = cmdDafny.verbatimString();
        input.println(cmd);
        input.flush();

        Std.Wrappers.Result<dafny.Tuple0, dafny.DafnySequence<? extends dafny.CodePoint>> r =
            Std.Wrappers.Result.<dafny.Tuple0, dafny.DafnySequence<? extends dafny.CodePoint>>create_Success(
                dafny.Tuple0._typeDescriptor(),
                dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR),
                dafny.Tuple0.create());
        return r;
    }

    public Std.Wrappers.Result<Std.Wrappers.Option<dafny.DafnySequence<? extends dafny.CodePoint>>, dafny.DafnySequence<? extends dafny.CodePoint>> ReadLine()
    {
        String line;
        try {
            line = output.readLine();
        } catch (Exception ex) {
            String javaErrorMessage = "Error reading response from '" + executableName.verbatimString() + "': " + ex.getMessage();
            dafny.DafnySequence<? extends dafny.CodePoint> errorMessage = dafny.DafnySequence.asUnicodeString(javaErrorMessage);
            return Std.Wrappers.Result.<Std.Wrappers.Option<dafny.DafnySequence<? extends dafny.CodePoint>>, dafny.DafnySequence<? extends dafny.CodePoint>>create_Failure(
                Std.Wrappers.Option.<dafny.DafnySequence<? extends dafny.CodePoint>>_typeDescriptor(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR)),
                dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR),
                errorMessage);
        }

        dafny.DafnySequence<? extends dafny.CodePoint> dafnyLine = dafny.DafnySequence.asUnicodeString(line);
        Std.Wrappers.Option<dafny.DafnySequence<? extends dafny.CodePoint>> some =
            Std.Wrappers.Option.<dafny.DafnySequence<? extends dafny.CodePoint>>create_Some(
                dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR),
                dafnyLine);
        return Std.Wrappers.Result.<Std.Wrappers.Option<dafny.DafnySequence<? extends dafny.CodePoint>>, dafny.DafnySequence<? extends dafny.CodePoint>>create_Success(
            Std.Wrappers.Option.<dafny.DafnySequence<? extends dafny.CodePoint>>_typeDescriptor(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR)),
            dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR),
            some);
    }
}