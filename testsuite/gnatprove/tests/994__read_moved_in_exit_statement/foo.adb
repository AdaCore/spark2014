procedure Foo with SPARK_Mode is
   type Int_Acc is not null access Integer;
begin
   loop
      declare
         X : Int_Acc := new Integer'(0);
         Y : Int_Acc := X;
      begin
         exit when X.all = 0;
      end;
   end loop;
end Foo;
