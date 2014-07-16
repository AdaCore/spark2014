package body Unit2 with
  SPARK_Mode
is

   procedure Create (X : out T2) is
   begin
      T1(X).Create;
      X.C2 := 0;
   end Create;

   procedure Bump (X : in out T2) is
   begin
      T1(X).Bump;
      X.C2 := X.C2 + 1;
   end Bump;

end Unit2;
