package body Generic_Package
with
   Refined_State => (State => Element),
   SPARK_Mode => On
is

   Element : Element_T;

   procedure Read (Value : out Element_T) is
   begin
      Value := Element;
   end Read;

   procedure Write (Value: in Element_T) is
   begin
      Element := Value;
   end Write;

end Generic_Package;
