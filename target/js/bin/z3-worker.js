// z3-worker.js - Web Worker for Z3 SMT solver
// Based on the original worker.js from z3.wasm

// Import the protocol definitions
var queries = { VERIFY: "VERIFY", EVAL: "EVAL", INIT: "INIT" };
var responses = { 
  PROGRESS: "PROGRESS", 
  READY: "READY",
  STDOUT: "STDOUT", 
  STDERR: "STDERR",
  VERIFICATION_COMPLETE: "VERIFICATION_COMPLETE",
  EVAL_COMPLETE: "EVAL_COMPLETE"
};

var solver;
var ready = false;

function sendMessage(kind, payload) {
  self.postMessage({ kind: kind, payload: payload });
}

function progress(message) {
  sendMessage(responses.PROGRESS, message);
  console.info("Worker:", message);
}

function onRuntimeInitialized() {
  ready = true;
  progress("Done initializing SMT solver.");
  sendMessage(responses.READY);
}

var STUB_MSG = "Calling stub instead of signal()";

function postOutput(channel, output) {
  output = output.replace(STUB_MSG, "");
  if (output != "") {
    sendMessage(channel, output);
  }
}

function loadSolver() {
  progress("Downloading SMT solver…");
  importScripts("z3.wasm/z3smt2w.js");
  progress("Initializing SMT solver…");
  
  // Create a dummy ArrayBuffer to pass as wasmBinary
  // The real binary will be fetched by the z3smt2w.js script
  var dummyBuffer = new ArrayBuffer(1);
  
  solver = Z3({ 
    ENVIRONMENT: "WORKER",
    wasmBinary: dummyBuffer,
    onRuntimeInitialized: onRuntimeInitialized,
    print: function(message) { postOutput(responses.STDOUT, message); },
    printErr: function(message) { postOutput(responses.STDERR, message); }
  });
}

function evalSmt2(id, cmd) {
  if (!ready) {
    sendMessage(responses.EVAL_COMPLETE, {
      id: id,
      error: "SMT solver not ready"
    });
    return;
  }
  
  try {
    // Create an SMT2 instance if needed
    if (!solver.SMT2) {
      solver.SMT2 = new solver.SMT2();
    }
    
    // Evaluate the command
    var result = solver.SMT2.eval(cmd);
    
    // Send the result back
    sendMessage(responses.EVAL_COMPLETE, {
      id: id,
      result: result
    });
  } catch (error) {
    sendMessage(responses.EVAL_COMPLETE, {
      id: id,
      error: error.message
    });
  }
}

function onMessage(event) {
  var kind = event.data.kind;
  var payload = event.data.payload;
  
  switch (kind) {
    case queries.INIT:
      loadSolver();
      break;
      
    case queries.EVAL:
      evalSmt2(payload.id, payload.cmd);
      break;
  }
}

// Set up message handler
self.onmessage = onMessage;