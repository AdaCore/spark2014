pragma SPARK_Mode;
procedure Acc (Some_Condition : Boolean) is
   X : access Integer;
   type Int_Ptr is access Integer;
   Global_Int : Int_Ptr := new Integer;
   procedure Foo is
     Y : access Integer;
     type Local_Int_Ptr is access Integer;
     Local_Int : Local_Int_Ptr := new Integer;
   begin
     if Some_Condition then
       Y := Global_Int;
     else
       Y := Local_Int;
     end if;
     X := Y; -- might fail accessibility check
   end;
begin
   null;
end Acc;
