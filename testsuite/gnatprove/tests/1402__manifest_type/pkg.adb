package body Pkg
  with SPARK_Mode
is

   procedure Reset (X : out T) is
   begin
      X := (Lo => 0, Hi => 5);
   end Reset;

end Pkg;
