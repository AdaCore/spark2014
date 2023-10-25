package body Variables1 is
   pragma SPARK_Mode (On);

   procedure Proc_1 (Formal : Volatile_Nat) is begin null; end Proc_1;
   procedure Proc_2 (Formal : Volatile_Rec) is begin null; end Proc_2;
   procedure Proc_3 is begin null; end Proc_3;

   function Func_1 (Formal : Volatile_Nat) return Integer is
   begin return 0; end Func_1;
   function Func_2 (Formal : Volatile_Rec) return Integer is
   begin return 0; end Func_2;
   function Func_3 return Integer is
   begin return 0; end Func_3;

   Obj_1 : Integer := Func_1 (OK_1);                                 --  Error
   Obj_2 : Integer := Func_2 (OK_2);                                 --  OK

begin
   Proc_1 (OK_1);                                                    --  Error
   Proc_2 (OK_2);                                                    --  OK

   if OK_1 = 0 then                                                  --  Error
      null;
   end if;
end Variables1;
