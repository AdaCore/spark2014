with Parent.Privchild;

package body Parent with Refined_State => (State => Parent.Privchild.Child_State) is

   procedure Init
     with Refined_Global => (Output => Parent.Privchild.Child_State) is
   begin
      Parent.Privchild.Init;
   end;

   function Read return Integer
     with Refined_Global => (Input => Parent.Privchild.Child_State)
   is
   begin
      return Parent.Privchild.Read;
   end;

end;
