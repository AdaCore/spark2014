package body Test with
   SPARK_Mode
is

   function Context_Field (Context : Context_Type) return Field_Type is
     (Context.Field);

   procedure Verify_Destination (Context : in out Context_Type) is
   begin
      Context.Elements (Destination) := (State => Valid);
      Context.Field := Destination;
      pragma Assert (Context.Field = Destination);
      pragma Assert (Context_Field (Context) = Destination);

   end;

end Test;
