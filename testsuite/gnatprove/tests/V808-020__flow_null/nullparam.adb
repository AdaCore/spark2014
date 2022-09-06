procedure Nullparam (Dummy : in out Integer) is
   type Acc is access all Integer;

   procedure Iofunc_Attr_Init (Data : Acc);

   procedure Iofunc_Attr_Init (Data : Acc) with
      SPARK_Mode => Off
   is
   begin
      null;
   end Iofunc_Attr_Init;
begin
   Iofunc_Attr_Init (null);
end Nullparam;
