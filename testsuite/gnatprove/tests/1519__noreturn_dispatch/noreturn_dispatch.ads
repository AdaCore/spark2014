package Noreturn_Dispatch with SPARK_Mode is
   pragma Elaborate_Body;
   type Root is tagged null record;
   procedure Stop (X : Root) with No_Return, Always_Terminates => False;
   type Child is new Root with null record;
   overriding procedure Stop (X : Child) with
     No_Return, Always_Terminates => False;

   procedure Halt with
     No_Return,
     Post => False,
     Always_Terminates => False;
end Noreturn_Dispatch;
