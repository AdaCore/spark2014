pragma Ada_2022;
package Ops with SPARK_Mode is

   type U32 is mod 2**32;
   type U64 is mod 2**64;

   A, B : U32 with Import;

   pragma Assert ((-A) = (if A = 0 then 0 else U32'Last - A + 1));

   pragma Assert
     (if A <= U32'Last - B then U32(A + B) = U32(U64(A) + U64(B)));

   pragma Assert
     (declare
        C : constant U64 := U64(A) + U64(B);
      begin
        (if C > U64(U32'Last) then A + B = U32(C - 2**32)));

   pragma Assert
     (A + B =
        (declare
           C : constant U64 := U64(A) + U64(B);
         begin
           (if C <= U64(U32'Last) then U32(C) else U32(C - 2**32))));

   pragma Assert
     (A - B =
        (declare
           C : constant U64 := U64(A) + (2**32 - U64(B));
         begin
           (if C > U64(U32'Last) then U32(C - 2**32) else U32(C))));
end;
