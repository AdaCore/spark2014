with Ada.Numerics.Big_Numbers.Big_Reals;
use  Ada.Numerics.Big_Numbers.Big_Reals;
procedure Main with SPARK_Mode is
   A : constant Big_Real := From_Quotient_String ("1/2");
   B : constant Big_Real := From_Quotient_String ("1/3");
   C : constant Big_Real := From_Quotient_String ("222/333");
   pragma Assert (B < A); --@ASSERT:PASS
   pragma Assert (A < C); --@ASSERT:PASS
   R : constant Big_Real := From_Quotient_String ("abcd"); --@PRECONDITION:FAIL
begin
   null;
end Main;
