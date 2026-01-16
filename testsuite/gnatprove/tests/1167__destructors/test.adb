pragma Extensions_Allowed (All_Extensions);

with Ada.Unchecked_Deallocation;

procedure Test with SPARK_Mode is
   package Nested is
      type Int_Access is access Integer;
      type T1 is tagged record
         F : Int_Access;
      end record;

      procedure T1'Destructor (X : in out T1);
   end Nested;

   package body Nested is

      procedure Free is new Ada.Unchecked_Deallocation (Integer, Int_Access);

      procedure T1'Destructor (X : in out T1) is
      begin
         Free (X.F);
      end T1'Destructor;
   end Nested;
   use Nested;

   C : T1 := (F => new Integer'(12)); --  There should not be a leak
begin
   null;
end;
