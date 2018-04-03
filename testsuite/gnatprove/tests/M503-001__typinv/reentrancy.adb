with External;

package body Reentrancy with SPARK_Mode is

   Start : Boolean := True;

   procedure Create (X : out T) is
   begin
      if Start then
         Start := False;
         External.Create (X);  --  @INVARIANT_CHECK:NONE
      else
         X := 1;  --  @INVARIANT_CHECK:NONE
      end if;
   end Create;

   procedure Update (X : in out T) is
   begin
      if Start then
         Start := False;
         External.Update (X);  --  @INVARIANT_CHECK:PASS
      else
         if X /= T'First then
            X := abs (X);  --  @INVARIANT_CHECK:NONE
         end if;
      end if;
   end Update;

   function Get (X : T) return Integer is
   begin
      if Start then
        -- Start := False;
         return External.Get (X);  --  @INVARIANT_CHECK:PASS
      else
         return Integer (X);
      end if;
   end Get;

end Reentrancy;
