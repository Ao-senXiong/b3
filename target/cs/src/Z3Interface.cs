using System;
using System.Diagnostics;
using System.IO;
using Smt;

namespace Z3SmtSolver {
  
  public class Z3SmtProcess : SmtProcess {
    const bool DEBUG = true;
    private Process z3Process;
    private StreamWriter z3Input;
    private StreamReader z3Output;
    private bool isDisposed;

    public void Log(string s) {
      if (DEBUG) {
        Console.WriteLine(s);
      }
    }

    public Z3SmtProcess() {
      try {
        // Start Z3 process in interactive mode
        var startInfo = new ProcessStartInfo("z3", "-in -smt2");
        startInfo.RedirectStandardInput = true;
        startInfo.RedirectStandardOutput = true;
        startInfo.RedirectStandardError = true;
        startInfo.UseShellExecute = false;
        startInfo.CreateNoWindow = true;

        z3Process = Process.Start(startInfo);
        if (z3Process != null) {
          z3Input = z3Process.StandardInput;
          z3Output = z3Process.StandardOutput;

          // Initialize Z3 with SMT-LIB2 commands
          SendCmd("(set-option :produce-models true)");
          SendCmd("(set-logic ALL)");
        }
        else {
          Console.WriteLine("Failed to start Z3 process");
        }
        
        isDisposed = false;
      }
      catch (Exception ex) {
        Console.WriteLine($"Error initializing Z3: {ex.Message}");
        isDisposed = true;
      }
    }

    public bool Disposed() {
      return isDisposed;
    }

    public Dafny.ISequence<Dafny.Rune> SendCmd(Dafny.ISequence<Dafny.Rune> cmdDafny) {
      var cmd = cmdDafny.ToVerbatimString(false);
      var response = SendCmd(cmd);
      var dafnyResponse = Dafny.Sequence<Dafny.Rune>.UnicodeFromString(response);
      return dafnyResponse;
    }

    public string SendCmd(string cmd) {
      try {
        if (isDisposed || z3Input == null || z3Output == null) {
          return "error: Z3 not initialized or disposed";
        }
        
        // Special case for exit command - mark as disposed
        if (cmd == "(exit)") {
          isDisposed = true;
        }
        
        // Send command
        z3Input.WriteLine(cmd);
        z3Input.Flush();
        Log($"Z3 << {cmd}");
        
        // Read response
        string response = ReadResponse(cmd);
        Log($"Z3 >> {response}");
        return response;
      } catch (Exception ex) {
        Console.WriteLine($"Error communicating with Z3: {ex.Message}");
        return $"error: {ex.Message}";
      }
    }
    
    private string ReadResponse(string cmd) {
      // For simple commands like (push), (pop), just return "success"
      if (cmd == "(push)" || cmd == "(pop)" || cmd.StartsWith("(assert ") || 
          cmd.StartsWith("(set-option ") || cmd.StartsWith("(set-logic ") ||
          cmd == "(exit)" || cmd.StartsWith("(declare-fun") || cmd.StartsWith("(declare-const")) {
        return "success";
      }
      
      // For check-sat, read a single line
      if (cmd == "(check-sat)") {
        return z3Output.ReadLine();
      }
      
      // For get-model, read until we get a balanced set of parentheses
      if (cmd == "(get-model)") {
        var response = new System.Text.StringBuilder();
        string line;
        int parenCount = 0;
        bool started = false;
        
        while ((line = z3Output.ReadLine()) != null) {
          response.AppendLine(line);
          
          // Count parentheses to determine when the response is complete
          foreach (char c in line) {
            if (c == '(') {
              started = true;
              parenCount++;
            } else if (c == ')') {
              parenCount--;
            }
          }
          
          // If we've started receiving a response and all parentheses are balanced, we're done
          if (started && parenCount <= 0) {
            break;
          }
        }
        
        return response.ToString();
      }
      
      // Default case
      return z3Output.ReadLine();
    }
  }
  public static partial class __default {
    public static SmtProcess CreateZ3Process() {
      return new Z3SmtProcess();
    }
  }
}