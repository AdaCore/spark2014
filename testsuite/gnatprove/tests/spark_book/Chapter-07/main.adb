with Interfaces.C;
with Console_IO;
with Messages;

procedure Main
  with
    SPARK_Mode,
    Global => (In_Out => Console_IO.IO_Subsystem) is

   Text : String := "Hello";
   Checksum : Interfaces.C.unsigned_short;
begin
   pragma Assert(Text'Length /= 0);  -- If Text'Length is zero, To_C propagates Constraint_Error.
   Checksum := Messages.Compute_Fletcher_Checksum(Interfaces.C.To_C(Text, False), Text'Length);
   Console_IO.Put_Line(Integer'Image(Integer(Checksum)));
end Main;
