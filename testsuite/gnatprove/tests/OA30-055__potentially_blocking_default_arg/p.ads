with Ada.Real_Time; package P is

   function Blocking return Boolean;

   protected PO is
      entry Dummy (Arg : Boolean := Blocking);
   end;

end;
