module PrintUtil {

  method Indent(indent: nat) {
    for i := 0 to indent {
      print " ";
    }
  }

  const IndentAmount := 2

  datatype ExprFormatOption = SingleLine | MultipleLines(indent: nat)
  {
    method Space() {
      match this
      case SingleLine => print " ";
      case MultipleLines(indent) =>
        print "\n";
        Indent(indent);
    }

    function More(): ExprFormatOption {
      match this
      case SingleLine => this
      case MultipleLines(indent) =>
        MultipleLines(indent + IndentAmount)
    }
  }
}