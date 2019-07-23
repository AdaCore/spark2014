package body Inst with SPARK_Mode is

   package My_Gen1 is new Gen (T1);
   package My_Gen2 is new Gen (T2);
   package My_Gen3 is new Gen (T3);
   package My_Gen4 is new Gen (T4);
   package My_Gen5 is new Gen (T5);
   package My_Gen6 is new Gen (T6);
   package My_Gen7 is new Gen (T7);

   procedure P1 is
   begin
      null;
   end P1;

end Inst;
