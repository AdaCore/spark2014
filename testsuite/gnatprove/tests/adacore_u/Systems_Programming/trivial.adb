package body Trivial
  with SPARK_Mode
is
   procedure Get (Val : out Integer) is
   begin
      Val := X;
   end Get;

end Trivial;
