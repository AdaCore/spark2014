with Gen;

package Variables1 is
   pragma SPARK_Mode (On);

   type Volatile_Nat is new Natural range 1 .. 10 with Volatile;
   type Volatile_Rec is null record with Volatile;

   OK_1 : Volatile_Nat with Async_Writers;                           --  OK
   OK_2 : Volatile_Rec;                                              --  OK

   procedure Proc_1 (Formal : Volatile_Nat);                         --  OK
   procedure Proc_2 (Formal : Volatile_Rec);                         --  OK
   procedure Proc_3
     with Global => (Input => OK_1);                                 --  OK

   function Func_1 (Formal : Volatile_Nat) return Integer;           --  Error
   function Func_2 (Formal : Volatile_Rec) return Integer;           --  Error
   function Func_3 return Integer
     with Global => (Input => OK_2);                                 --  Error

   package Inst is new Gen (Volatile_Rec, OK_2);                     --  Error
end Variables1;
