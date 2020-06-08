pragma SPARK_Mode;
with Ada.Unchecked_Deallocation;

procedure Free is

   type T is access Integer;

   procedure Dealloc is new Ada.Unchecked_Deallocation (Integer, T);

   X : T;
begin
   pragma Assert (X = null);
   X := new Integer'(0);
   Dealloc (X);
   pragma Assert (X = null);

end Free;
