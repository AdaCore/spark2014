package body Unit1 with
  SPARK_Mode
is

   procedure Create (X : out T1) is
   begin
      X.C1 := 0;
   end Create;

   procedure Bump (X : in out T1) is
   begin
      X.C1 := X.C1 + 1;
   end Bump;

end Unit1;
