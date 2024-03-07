package body Gen with SPARK_Mode, Annotate => (GNATprove, Unhide_Info, "Package_Body") is

  function G (X : Integer) return Integer is (X);

  function Read (X : Integer) return Ar is (1 .. 2 => 2);

  function F return Integer is
    Z : Integer := 0;
  begin
    Read (Read (10), Z);
    return Z;
  end F;

end Gen;
