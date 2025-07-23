function makeWorker(self, console, queries, responses, performance) {
    var INPUT_FNAME = "input.b3";
    var b3Module;
    var ready = false;

    function postMessage(kind, payload) {
        console.info("B3 → Window (" + kind + "):", payload);
        self.postMessage({ kind: kind, payload: payload });
    }

    function runCompiler(input, args) {
        if (!ready) {
            console.error("Cannot run B3 compiler yet.");
            postMessage(responses.DONE, false);
            return;
        }

        try {
            // Write the input file
            b3Module.FS.writeFile(INPUT_FNAME, input, { encoding: "utf8" });
            
            // Prepare arguments for the B3 compiler
            var fullArgs = args.slice();
            fullArgs.unshift(INPUT_FNAME);
            
            // Run the B3 compiler
            console.log("Running B3 compiler with", fullArgs);
            var result = b3Module.callMain(fullArgs);
            
            if (result === 0) {
                postMessage(responses.STDOUT, "Compilation successful!");
            } else {
                postMessage(responses.STDERR, "Compilation failed with code: " + result);
            }
        } catch (error) {
            postMessage(responses.STDERR, "Error: " + error.message);
        }
        
        postMessage(responses.COMPILATION_COMPLETE, true);
    }

    function progress(message) {
        postMessage(responses.PROGRESS, message);
        console.info("Worker:", message, performance.now());
    }

    function onRuntimeInitialized() {
        ready = true;
        progress("B3 compiler initialized and ready.");
        postMessage(responses.READY);
    }

    function postOutput(channel, output) {
        if (output != "") {
            postMessage(channel, output);
        }
    }

    function loadCompiler() {
        progress("Loading B3 compiler...");
        self.importScripts("b3.js");
        
        progress("Initializing B3 compiler...");
        b3Module = B3({
            ENVIRONMENT: "WORKER",
            onRuntimeInitialized: onRuntimeInitialized,
            print: function(message) { postOutput(responses.STDOUT, message); },
            printErr: function(message) { postOutput(responses.STDERR, message); }
        });
    }

    function onMessage(event) {
        console.info("Window → B3:", event);
        var kind = event.data.kind;
        var payload = event.data.payload;
        switch (kind) {
        case queries.COMPILE:
            runCompiler(payload.input, payload.args);
            break;
        }
    }

    function init() {
        loadCompiler();
        self.onmessage = onMessage;
    }

    return { init: init };
}

importScripts("b3-protocol.js");
makeWorker(self, console, queries, responses, performance).init();