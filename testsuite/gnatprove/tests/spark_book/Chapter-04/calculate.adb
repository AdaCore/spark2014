
-- The purpose of this procedure is to just explore the kind of flow messages the tools produce.
procedure Calculate(A : out Integer; B : in Integer; C : in out Integer)
  with
    SPARK_Mode,
    Global => null,
    Depends => (A => (B, C), C => C)
is
   pragma Annotate(GNATprove, Intentional, "incorrect dependency", "Demonstration");
begin
   A := B;
   C := C + 1;
end Calculate;
