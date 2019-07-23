with Ada.Text_IO;
procedure A with SPARK_Mode is

   type Int_Ptr is access Integer;
   subtype Not_Null_Int_Ptr is not null Int_Ptr;

   procedure Set_To_Null (X : in out Int_Ptr) with Global => null is
   begin
      X := null;
   end Set_To_Null;

   X : Not_Null_Int_Ptr := new Integer'(12);
   C : Integer;
begin
   Set_To_Null (X);  --@NULL_EXCLUSION:FAIL
end A;
