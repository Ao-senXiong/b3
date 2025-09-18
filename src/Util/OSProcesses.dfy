module OSProcesses {
  import opened Std.Wrappers

  export
    reveals OSProcess
    provides OSProcess.Create, OSProcess.Valid, OSProcess.ExecutableName
    provides OSProcess.Send, OSProcess.ReadLine
    provides Wrappers

  class {:extern} OSProcess {
    ghost predicate {:extern} Valid()
    function {:extern} ExecutableName(): string

    @Axiom
    static method {:extern} Create(executable: string, arguments: string) returns (r: Result<OSProcess, string>)
      ensures r.Success? ==> var p := r.value; p.Valid() && fresh(p)

    @Axiom
    method {:extern} Send(msg: string) returns (r: Result<(), string>)
      requires Valid()
      modifies this
      ensures r.Success? ==> Valid()

    // A return of Success(None) means the process output has signaled an end-of-file
    @Axiom
    method {:extern} ReadLine() returns (r: Result<Option<string>, string>)
      requires Valid()
      modifies this
      ensures r.Success? ==> Valid()
  }
}