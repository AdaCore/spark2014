package body Bad_Array with SPARK_Mode is
   function Foo return Pos_Array is
   begin
      return A : Int_Array (1 .. 1) := (1 .. 1 => 1) do
         A (1) := -1;
      end return;
   end;
end;
