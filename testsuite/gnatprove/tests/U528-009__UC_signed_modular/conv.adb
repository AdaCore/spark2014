with Ada.Unchecked_Conversion;
with Interfaces; use Interfaces;

procedure Conv is
   
   subtype Int64 is Integer_64;   
   subtype Uns64 is Unsigned_64;
   
   function To_Uns is new Ada.Unchecked_Conversion (Int64, Uns64);
   function To_Int is new Ada.Unchecked_Conversion (Uns64, Int64);

   function To_Uns_Explicit (X : Int64) return Uns64 is
      (if X >= 0 then Uns64(X) elsif X = Int64'First then 2**63 else -Uns64(-X));

   function To_Int_Explicit (X : Uns64) return Int64 is
      (if X < 2**63 then Int64(X) elsif X = 2**63 then Int64'First else -Int64(-X));
      
   procedure To_Uns_Equiv (X : Int64) with
     Ghost
   is
   begin
      pragma Assert (To_Uns (X) = To_Uns_Explicit (X));  --@ASSERT:PASS
      pragma Assert (False);  --@ASSERT:FAIL
   end;
   
   procedure To_Int_Equiv (X : Uns64) with
     Ghost
   is
   begin
      pragma Assert (To_Int (X) = To_Int_Explicit (X));  --@ASSERT:PASS
      pragma Assert (False);  --@ASSERT:FAIL
   end;
begin
   null;
end;
