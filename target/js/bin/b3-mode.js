// Custom Ace editor mode for B3 language
define("ace/mode/b3_highlight_rules", ["require", "exports", "module", "ace/lib/oop", "ace/mode/text_highlight_rules"], function(require, exports, module) {
  "use strict";

  var oop = require("../lib/oop");
  var TextHighlightRules = require("./text_highlight_rules").TextHighlightRules;

  var B3HighlightRules = function() {
    // Keywords from the sample program
    var keywords = (
      "procedure|var|val|exit|return|check|assume|assert|probe|forall|" +
      "if|else|case|loop|invariant|asap|inout|out|requires|ensures|type"
    );

    // Types from the sample program
    var types = "int|bool|string";

    // Define the highlighting rules
    this.$rules = {
      "start": [
        {
          token: "comment",
          regex: "\\/\\/.*$"
        },
        {
          token: "keyword.control",
          regex: "\\b(?:if|else|case|loop|asap|exit|return)\\b"
        },
        {
          token: "keyword.declaration",
          regex: "\\b(?:procedure|var|val|type|requires|ensures|invariant)\\b"
        },
        {
          token: "keyword.operator",
          regex: "\\b(?:check|assume|assert|probe|forall|inout|out)\\b"
        },
        {
          token: "storage.type",
          regex: "\\b(?:" + types + ")\\b"
        },
        {
          token: "constant.numeric",
          regex: "\\b[0-9]+\\b"
        },
        {
          token: "string",
          regex: '".*?"'
        },
        {
          token: "punctuation.operator",
          regex: ":=|:|,|;"
        },
        {
          token: "paren.lparen",
          regex: "[\\{\\(]"
        },
        {
          token: "paren.rparen",
          regex: "[\\}\\)]"
        },
        {
          token: "variable.parameter",
          regex: "\\b(?:out|inout)\\s+([a-zA-Z_$][a-zA-Z0-9_$]*)"
        },
        {
          token: "identifier",
          regex: "[a-zA-Z_$][a-zA-Z0-9_$]*"
        }
      ]
    };
  };

  oop.inherits(B3HighlightRules, TextHighlightRules);

  exports.B3HighlightRules = B3HighlightRules;
});

define("ace/mode/b3", ["require", "exports", "module", "ace/lib/oop", "ace/mode/text", "ace/mode/b3_highlight_rules"], function(require, exports, module) {
  "use strict";

  var oop = require("../lib/oop");
  var TextMode = require("./text").Mode;
  var B3HighlightRules = require("./b3_highlight_rules").B3HighlightRules;

  var Mode = function() {
    this.HighlightRules = B3HighlightRules;
    this.$behaviour = this.$defaultBehaviour;
  };
  oop.inherits(Mode, TextMode);

  (function() {
    this.lineCommentStart = "//";
    this.$id = "ace/mode/b3";
  }).call(Mode.prototype);

  exports.Mode = Mode;
});