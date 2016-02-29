with System;                  use System;
with System.Storage_Elements; use System.Storage_Elements;

procedure Address (V : Integer) with SPARK_Mode is

   X : String := "hello";
   Y : System.Address := X(V)'Address;

   procedure Memcpy
     (S1 : in out String;
      From1 : Positive;
      N : Natural)
   with
     Pre =>
       (if N /= 0 then
          From1 in S1'Range and then
          From1 + N - 1 in S1'Range)
   is
   begin
      null;
   end Memcpy;

begin
   null;
end Address;
