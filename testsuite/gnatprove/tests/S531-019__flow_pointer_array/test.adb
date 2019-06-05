procedure Test with SPARK_Mode is
   type R is record
      F : Integer := 0;
   end record;
   type U_Array is array (Positive range <>) of R;
   type U_Array_Acc is access U_Array;

   procedure P (A : in out U_Array_Acc) with
     Pre  => A /= null,
     Post => A /= null and A'First = A'First'Old and A'Last = A'Last'Old
   is
   begin
      L : for I in A'Range loop
         A (I).F := 0;
      end loop L;
   end P;

   A : U_Array_Acc := new U_Array (1 .. 100);
begin
   pragma Assert (A'First = 1);
   P (A);
   pragma Assert (A'First = 1); -- unproved
end Test;
