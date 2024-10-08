pragma Extensions_Allowed (On);

with Ada.Unchecked_Deallocation;

procedure Test_Leaks (B : Boolean) with SPARK_Mode is

   type Int_Acc is access Integer;

   procedure Free is new Ada.Unchecked_Deallocation (Integer, Int_Acc);

   function Raise_Exp (B : Boolean) return Integer with
     Side_Effects,
     Post => not B,
     Exceptional_Cases => (Program_Error => B);

   function Raise_Exp (B : Boolean) return Integer is
   begin
      if B then
         raise Program_Error;
      else
         return 1;
      end if;
   end Raise_Exp;

   Y : Int_Acc := new Integer'(14); --  @RESOURCE_LEAK_AT_END_OF_SCOPE:FAIL
begin
   I : Integer := Raise_Exp (B);
   Free (Y);
exception
   when Program_Error =>
      null; --  Y is not freed
end Test_Leaks;
