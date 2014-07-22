package body Unit3 with
  SPARK_Mode
is

   procedure Create (X : out T3) is
   begin
      T2(X).Create;
      X.C3 := 0;
   end Create;

   procedure Bump (X : in out T3) is
   begin
      T2(X).Bump;
      X.C3 := X.C3 + 1;
   end Bump;

end Unit3;
