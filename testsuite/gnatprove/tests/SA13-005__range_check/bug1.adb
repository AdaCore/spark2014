package body Bug1
  with SPARK_Mode => On
is
   procedure P (C :    out Seq;
                M : in     Seq)
   is
   begin
      C := M;
   end P;
end Bug1;
