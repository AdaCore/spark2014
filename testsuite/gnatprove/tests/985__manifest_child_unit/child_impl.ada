package body Pkg.Child
  with SPARK_Mode
is
   procedure R (X : Integer) is
   begin
      Sink := X;
   end R;
end Pkg.Child;
