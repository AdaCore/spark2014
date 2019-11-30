package body SXML.Generic_Parser with
   Refined_State => (State => (Call_Stack.State))
is
   procedure Parse
   is
   begin
      Call_Stack.Init;
   end Parse;

end SXML.Generic_Parser;
