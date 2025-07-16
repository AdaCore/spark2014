procedure Foo with SPARK_Mode is
   type Int_Acc is access Integer;
   X : Int_Acc;
begin
   loop
      declare
         Y : Int_Acc := X;
      begin
         null;
      end;
   end loop;
end Foo;
