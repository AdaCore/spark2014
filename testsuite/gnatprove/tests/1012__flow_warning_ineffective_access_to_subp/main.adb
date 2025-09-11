procedure Main with SPARK_Mode is
   type Proc_Acc is access procedure (X : out Integer);

   procedure P (X : out Integer) is begin X := 1; end;

   procedure Foo (X : out Integer) is
      P_Acc : Proc_Acc := P'Access;
   begin
      P_Acc.all (X);
      X := 0;
   end;
begin
   null;
end;
