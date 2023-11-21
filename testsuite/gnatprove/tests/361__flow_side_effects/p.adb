package body P with Refined_State => (State => X) is
   X : Boolean;
   function Init (Val : Boolean) return Boolean is
   begin
      X := Val;
      return True;
   end Init;
end P;
