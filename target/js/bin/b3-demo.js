/* exported makeB3Demo */
function makeB3Demo(window, queries, responses, ace) {
    var editor;
    var worker;
    var compilation_start;

    var console = window.console;
    var document = window.document;
    var command_line_args = document.getElementById("command-line-args");
    var run_button = document.getElementById("run");
    var stdout_textbox = document.getElementById("stdout");

    function postB3Message(query, payload) {
        console.info("[Window] → B3 (" + query + "):", payload);
        worker.postMessage({ kind: query, payload: payload });
    }

    function clear(node) {
        while (node.hasChildNodes()) {
            node.removeChild(node.lastChild);
        }
    }

    function disableButton(message) {
        run_button.disabled = true;
        run_button.value = message;
    }

    function enableButton() {
        run_button.disabled = false;
        run_button.value = "Run B3!";
    }

    function compileCurrentInput(_event) {
        var input = editor.getValue();
        var args = command_line_args.value.split(/ +/).filter(Boolean);
        clear(stdout_textbox);
        disableButton("Compiling…");
        compilation_start = window.performance.now();
        postB3Message(queries.COMPILE, { args: args, input: input });
    }

    function logOutput(message, cssClass) {
        var span_node = window.document.createElement("span");
        span_node.className = cssClass;
        span_node.appendChild(window.document.createTextNode(message + "\n"));
        stdout_textbox.appendChild(span_node);
    }

    function onB3Message(event) {
        console.info("B3 → [Window]:", event);
        var kind = event.data.kind;
        var payload = event.data.payload;
        switch (kind) {
        case responses.PROGRESS:
            disableButton(payload);
            break;
        case responses.READY:
            enableButton();
            break;
        case responses.STDOUT:
            logOutput(payload, "stdout-msg");
            break;
        case responses.STDERR:
            logOutput(payload, "stderr-msg")
            break;
        case responses.COMPILATION_COMPLETE:
            enableButton();
            var elapsed = Math.round(window.performance.now() - compilation_start);
            logOutput("-- Compilation complete (" + elapsed + "ms)", "info-msg");
            break;
        }
    }

    function setupB3Worker() {
        worker = new window.Worker("b3-worker.js");
        worker.onmessage = onB3Message;
    }

    function setupAceEditor() {
        editor = ace.edit("editor");
        editor.setTheme("ace/theme/monokai");
        editor.getSession().setMode("ace/mode/javascript");
        editor.setOptions({ fontFamily: "Ubuntu Mono, monospace", fontSize: "1rem" });
    }

    function init() {
        setupAceEditor();
        setupB3Worker();
        clear(stdout_textbox);
        run_button.onclick = compileCurrentInput;
    }

    return { init: init };
}