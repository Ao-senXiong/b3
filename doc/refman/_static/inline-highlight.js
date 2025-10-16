document.addEventListener('DOMContentLoaded', function() {
    // Keywords from b3.json (keywords + verifyKeywords arrays)
    // Keep in sync with b3.json when keywords are updated
    const b3Keywords = [
        "contract", "axiom", "type", "partition", "function", "predicate", "procedure",
        "var", "val", "define", "inout", "out", "call", "assert", "assume", "check",
        "learn", "exit", "then", "else", "if", "return", "probe", "where", "loop",
        "old", "forall", "exists", "closure", "lift", "into", "by", "case",
        "false", "true", "requires", "ensures", "invariant", "reqensinv",
        "trigger", "explains", "injective"
    ];
    
    document.querySelectorAll('code.docutils.literal.notranslate span.pre').forEach(function(span) {
        if (b3Keywords.includes(span.textContent.trim())) {
            span.classList.add('b3-keyword');
        }
    });
});
