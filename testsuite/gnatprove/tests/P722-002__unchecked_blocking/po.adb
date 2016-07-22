with Ada.Unchecked_Conversion;

package body PO is

   type My_Boolean is new Boolean;
   for My_Boolean'Size use Integer'Size;

   function Dummy is new Ada.Unchecked_Conversion (My_Boolean, Integer);

   protected body Foo is
      procedure Bar is
         I : Integer;
         pragma Unreferenced (I);
      begin
         I := Dummy (True);
      end Bar;

   end Foo;

end PO;
