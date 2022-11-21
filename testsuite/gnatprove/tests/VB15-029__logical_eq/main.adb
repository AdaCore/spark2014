procedure Main
  with
    SPARK_Mode => On
is

   function Eq (X, Y : String) return Boolean with
     Import,
     Global => null,
     Annotate => (GNATprove, Always_Return),
     Annotate => (GNATprove, Logical_Equal);
begin
   pragma Assert (Eq ("1", "2")); --@ASSERT:FAIL
end Main;
