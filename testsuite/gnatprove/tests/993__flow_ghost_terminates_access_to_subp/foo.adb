procedure Foo is
   type Proc_Acc is access procedure (I : out Integer);

   procedure P (I : out Integer) is
      P_Acc : Proc_Acc := P'Access;
   begin
      P_Acc.all (I);
   end P;

   P_Acc : Proc_Acc := P'Access with Ghost;

   I : Integer with Ghost;
begin
   P_Acc.all (I);
end Foo;
