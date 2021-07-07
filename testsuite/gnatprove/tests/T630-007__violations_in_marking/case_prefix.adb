procedure Case_Prefix with SPARK_Mode is
   type Int_Acc is access Integer;
   type My_Enum is (One, Two, Three);

   X1 : not null Int_Acc := new Integer'(1);
   X2 : not null Int_Acc := new Integer'(2);
   X3 : not null Int_Acc := new Integer'(3);

   function Get_X (E : My_Enum) return Integer is
     (Int_Acc'(case E is
         when One   => X1,
         when Two   => X2,
         when Three => X3).all);
begin
   pragma Assert (Get_X (One) = 1);
   pragma Assert (Int_Acc'(new Integer'(1)).all = 1);
end Case_Prefix;
