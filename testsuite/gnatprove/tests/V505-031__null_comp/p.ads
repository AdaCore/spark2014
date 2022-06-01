package P with SPARK_Mode is

   type Buffer_Acc is not null access all String;

   type Buffer_Rec is record
      Data : Buffer_Acc (1 .. 10);
   end record;

   type Buffer_Arr is array (Boolean) of Buffer_Acc (1 .. 10);

   function To_Acc return Buffer_Acc with Import;
   function To_Rec return Buffer_Rec with Import;
   function To_Arr return Buffer_Arr with Import;

   Acc : Buffer_Acc := To_Acc;
   Rec : Buffer_Rec := To_Rec;
   Arr : Buffer_Arr := To_Arr;

   pragma Assert (Acc /= null);         --@ASSERT:PASS
   pragma Assert (Rec.Data /= null);    --@ASSERT:PASS
   pragma Assert (Arr (True) /= null);  --@ASSERT:PASS
end;
