with Parent.Private1;
package body Parent.Public1 is

   C : constant Private1.Private_Int := Private1.K;

   procedure Process (Value : in out Pub_Array1) is
      Temp : Parent_Int;
   begin
      Temp      := Value (1);
      Value (1) := Value (3);
      Value (3) := Temp;
   end Process;

end Parent.Public1;
