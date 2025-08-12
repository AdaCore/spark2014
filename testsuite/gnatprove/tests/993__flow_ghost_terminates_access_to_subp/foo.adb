procedure Foo is
   type Proc_Acc is access procedure (I : out Integer);
   type Func_Acc is access function (I : Integer) return Boolean;

   function F1 (I : Integer) return Boolean is (I = 0);
   function F2 (I : Integer) return Boolean is
      F2_Acc : Func_Acc := F2'Access;
   begin
      return F2_Acc.all (I);
   end F2;

   procedure P (I : out Integer) is
      P_Acc : Proc_Acc := P'Access;
   begin
      P_Acc.all (I);
   end P;

   P_Acc : Proc_Acc := P'Access with Ghost;
   F1_Acc : Func_Acc := F1'Access with Ghost; --@TERMINATION:NONE
   F2_Acc : Func_Acc := F2'Access with Ghost; --@TERMINATION:FAIL

   I : Integer with Ghost;
   B1, B2 : Boolean with Ghost;
begin
   P_Acc.all (I);          --@TERMINATION:FAIL
   B1 := F1_Acc.all (1);
   B2 := F2_Acc.all (2);
end Foo;
