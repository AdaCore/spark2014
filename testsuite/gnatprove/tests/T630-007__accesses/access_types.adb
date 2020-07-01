with Acc_Ext;
procedure Access_Types (I : Integer) with SPARK_Mode is
   type Rec is record
      F, G : Integer;
   end record;

   type Rec_Acc is not null access Rec with
     Predicate => Rec_Acc.F < Rec_Acc.G;

   X : Rec_Acc := new Rec'(1, 2);
   Y : Integer := Acc_Ext.P_Vol.all;
   Z : Integer := Acc_Ext.P_Vol.all;
begin
   if I = 1 then
      X := new Rec'(2, 2); --@PREDICATE_CHECK:FAIL
   elsif I = 2 then
      pragma Assert (Y = Z); --@ASSERT:FAIL
   end if;
end Access_Types;
