// Z3SmtSolver.js - JavaScript implementation for Z3 SMT solver external functions
if (typeof Z3SmtSolver === "undefined") {
  Z3SmtSolver = {}; // Should not happen because invoked after b3.js
}

// Implement the extern function declared in Z3SmtSolver.dfy:
// @Axiom
// method {:extern} CreateZ3Process() returns (process: Smt.SmtProcess)
Z3SmtSolver.__default = Z3SmtSolver.__default || {};
Z3SmtSolver.__default.CreateZ3Process = function () {
  console.log("Creating Z3 process...");

  // Initialize Z3WorkerManager if not already done
  if (typeof Z3WorkerManager !== 'undefined') {
    Z3WorkerManager.init();
  }

  // Create a Z3 SMT process that implements the Smt.SmtProcess interface
  var z3Process = {
    // Private state
    disposed: false,

    // Required method: Disposed()
    Disposed: function () {
      return this.disposed;
    },

    // Required method: SendCmd(cmd)
    SendCmd: function (cmdDafny) {
      if (this.disposed) {
        return _dafny.Seq.UnicodeFromString("error: Z3 process is disposed");
      }

      // Convert Dafny string to JavaScript string
      var cmd = cmdDafny.toVerbatimString ? cmdDafny.toVerbatimString(false) : String(cmdDafny);

      console.log("Z3 command:", cmd);

      // If this is the exit command, mark as disposed
      if (cmd === "(exit)") {
        this.disposed = true;
        return _dafny.Seq.UnicodeFromString("success");
      }

      // For now, return mock responses for common Z3 commands
      // In a real implementation, we would send the command to Z3 and get the result
      if (cmd.startsWith("(declare-fun")) {
        return _dafny.Seq.UnicodeFromString("success");
      } else if (cmd.startsWith("(assert")) {
        return _dafny.Seq.UnicodeFromString("success");
      } else if (cmd === "(check-sat)") {
        return _dafny.Seq.UnicodeFromString("sat");
      } else if (cmd === "(get-model)") {
        return _dafny.Seq.UnicodeFromString("((define-fun x () Int 5))");
      } else if (cmd === "(push)") {
        return _dafny.Seq.UnicodeFromString("success");
      } else if (cmd === "(pop)") {
        return _dafny.Seq.UnicodeFromString("success");
      } else {
        return _dafny.Seq.UnicodeFromString("unknown command: " + cmd);
      }
    }
  };

  return z3Process;
};