with Call_Assign; use Call_Assign;
package body Reverse_Call_Assign is
   procedure Call_Simple (X : in out Integer) is
   begin
      Call (X, Simple);
   end Call_Simple;
   procedure Call_Conditional (X : in out Integer) is
   begin
      Call (X, Conditional);
   end Call_Conditional;
   procedure Call_Self (X : in out Integer) is
   begin
      Call (X, Self);
   end Call_Self;
end Reverse_Call_Assign;
