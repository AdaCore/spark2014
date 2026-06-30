procedure Test_Array_Component with SPARK_Mode is

   --  Test that we can prove Modifies on array from Modifies on component

   type Int_Array is array (Positive range <>) of Integer;

   procedure Write_If_B (X : in out Integer; B : Boolean) with
     Modifies => (X when B)
   is
   begin
      if B then
         X := 0;
      end if;
   end Write_If_B;

   procedure Write_Cell_If_B (A : in out Int_Array; I : Positive; B : Boolean) with
     Pre => I in A'Range,
     Modifies => (A (I) when B)
   is
   begin
      Write_If_B (A (I), B);
   end Write_Cell_If_B;

begin
   null;
end;
