package body SXML.Stack with
   Refined_State => (State => (S, Index))
is
   type Stack_Type is array (1 .. Size) of Element_Type;
   S     : Stack_Type := (others => Null_Element);
   Index : Natural    := S'First;

   procedure Init
   is
   begin
      S (S'Range) := (others => Null_Element);
      Index := S'First;
   end Init;

end SXML.Stack;
