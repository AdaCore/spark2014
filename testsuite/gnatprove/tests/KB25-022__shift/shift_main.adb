with Interfaces; use Interfaces;

procedure Shift_Main is
   pragma SPARK_Mode (On);
   function P (A : Unsigned_64) return Unsigned_64 is
   begin
      return Shift_Right (A, 5);
   end P;

   function Q (A : Unsigned_64) return Unsigned_64 is
   begin
      return Shift_Left (A, 5);
   end Q;

   function R (A : Unsigned_64) return Unsigned_64 is
   begin
      return Rotate_Left (A, 5);
   end R;

   function S (A : Unsigned_64) return Unsigned_64 is
   begin
      return Rotate_Right (A, 5);
   end S;

   function T (A : Unsigned_64) return Unsigned_64 is
   begin
      return Shift_Right_Arithmetic (A, 5);
   end T;

   A : Unsigned_64 := 12;
begin
   A := P (A);
   A := Q (A);
   A := R (A);
   A := S (A);
   A := T (A);
end;
