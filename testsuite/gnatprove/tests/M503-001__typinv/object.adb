package body Object is

   procedure Create (X : out T) is  --  @INVARIANT_CHECK:PASS
   begin
      X.C := 1;  --  @INVARIANT_CHECK:NONE
   end Create;

   procedure Update (X : in out T) is  --  @INVARIANT_CHECK:PASS
   begin
      if X.C /= Integer'First then
         X.C := abs (X.C);  --  @INVARIANT_CHECK:NONE
      end if;
   end Update;

   function Get (X : T) return Integer is (Integer (X.C));

end Object;
