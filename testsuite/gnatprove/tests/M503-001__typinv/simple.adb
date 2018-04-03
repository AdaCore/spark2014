package body Simple with SPARK_Mode is

   procedure Create (X : out T) is
   begin
      X := 1;  --  @INVARIANT_CHECK:NONE
   end Create;

   procedure Update (X : in out T) is
   begin
      if X /= T'First then
         X := abs (X);  --  @INVARIANT_CHECK:NONE
      end if;
   end Update;

   function Get (X : T) return Integer is (Integer (X));

end Simple;
