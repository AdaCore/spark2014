with Ada.Unchecked_Deallocation;

procedure Test with SPARK_Mode is
   type Int_acc is access Integer with Predicate => Int_Acc /= null;

   procedure Free is new Ada.Unchecked_Deallocation (Integer, Int_Acc);

   X : Int_acc := new Integer'(15);
begin
   Free (X); --  @PREDICATE_CHECK:FAIL
   pragma Assert (False);
end Test;
