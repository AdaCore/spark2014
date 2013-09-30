package body Ghost_Illegal_2 is
   function Add (X, Y : Integer) return Integer is
      (X + Y);


   function Add_And_Double (X, Y : Integer) return Integer is
     --  TU: 5. A ghost entity shall only be referenced:
     --  * from within an assertion expression; or
     --  * within or as part of the declaration or completion of a
     --    ghost entity (e.g., from within the body of a ghost function); or
     --  * within a statement which does not contain (and is not itself) either
     --    an assignment statement targeting a non-ghost variable or a
     --    procedure call which passes a non-ghost variable as an out or in out
     --    mode actual parameter.
   begin
      return (Add (X, Y) * 2);
   end Add_And_Double;


   function Reads_A_Volatile return Integer is
     --  TU: 6. Within a ghost procedure, the view of any non-ghost variable is
     --  a constant view. Within a ghost procedure, a volatile object shall not
     --  be read. [In a ghost procedure we do not want to allow assignments to
     --  non-ghosts either via assignment statements or procedure calls.]
   begin
      return (Vol_Int + 1);  --  Ghost functions are not allowed to read
                             --  Volatiles.
   end Reads_A_Volatile;


   function Is_Even (X : Integer) return Boolean is
      (X mod 2 = 0);


   procedure Ghost_Func_In_Flow_Exprpession (Par : in out Integer) is
     --  TU: 15. A ghost entity shall not be referenced
     --  * within a call to a procedure which has a non-ghost output; or
     --  * within a control flow expression (e.g., the condition of an if
     --    statement, the selecting expression of a case statement, the
     --    bounds of a for loop) of a compound statement which contains
     --    such a procedure call. [The case of a non-ghost-updating
     --    assignment statement is handled by a legality rule; this rule is
     --    needed to prevent a call to a procedure which updates a
     --    non-ghost via an up-level reference, as opposed to updating a
     --    parameter.] [This rule is intended to ensure an update of a
     --    non-ghost entity shall not have a control flow dependency on a
     --    ghost entity.]
   begin
      if Is_Even (Par) then
        Par := 0;
      else
        Par := Par + 1;
      end if;
   end Ghost_Func_In_Flow_Exprpession;
end Ghost_Illegal_2;