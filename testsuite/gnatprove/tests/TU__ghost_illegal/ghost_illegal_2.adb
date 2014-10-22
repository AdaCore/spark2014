package body Ghost_Illegal_2 is
   function Add (X, Y : Integer) return Integer is (X + Y);

   function Add_And_Double (X, Y : Integer) return Integer is
     --  TU: 12. A ghost entity shall only be referenced:
     --  * from within an assertion expression; or
     --  * within the declaration or completion of a
     --    ghost entity (e.g., from within the body of a ghost subprogram); or
     --  * within a statement which does not contain (and is not itself)
     --    either an assignment statement targeting a non-ghost variable,
     --    a procedure call which passes a non-ghost variable as an out or in
     --    out mode actual parameter, or a call to a procedure which has a
     --    non-ghost global output. [Strictly speaking, the final "non-ghost
     --    global output" part of this rule is a Verification Rule rather
     --    than a Legality Rule.] [Note that in order to determine whether a
     --    given reference satisfies this condition, it suffices to examine
     --    only the innermost statement enclosing the reference.]
   begin
      return Add (X, Y) * 2;
   end Add_And_Double;

   function Reads_A_Volatile return Integer is
     --  TU: 19. A ghost procedure shall not have an effectively
     --  volatile global input with the properties Async_Writers or
     --  Effective_Reads set to True. [This rule says, in effect, that
     --  ghost procedures are subject to the same restrictions as
     --  non-ghost functions with respect to reading volatile
     --  objects.]
   begin
      return Vol_Int + 1;  --  Ghost functions are not allowed to read
                           --  Volatiles.
   end Reads_A_Volatile;


   function Is_Even (X : Integer) return Boolean is (X mod 2 = 0);

   procedure Ghost_Func_In_Flow_Exprpession (Par : in out Integer) is
     --  TU: 12. A ghost entity shall only be referenced:
     --  * from within an assertion expression; or
     --  * within the declaration or completion of a
     --    ghost entity (e.g., from within the body of a ghost subprogram); or
     --  * within a statement which does not contain (and is not itself)
     --    either an assignment statement targeting a non-ghost variable,
     --    a procedure call which passes a non-ghost variable as an out or in
     --    out mode actual parameter, or a call to a procedure which has a
     --    non-ghost global output. [Strictly speaking, the final "non-ghost
     --    global output" part of this rule is a Verification Rule rather
     --    than a Legality Rule.] [Note that in order to determine whether a
     --    given reference satisfies this condition, it suffices to examine
     --    only the innermost statement enclosing the reference.]
   begin
      if Is_Even (Par) then
         Par := 0;
      else
         Par := Par + 1;
      end if;
   end Ghost_Func_In_Flow_Exprpession;
end Ghost_Illegal_2;
