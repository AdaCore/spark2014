package Bad_Spec with SPARK_Mode is

   procedure Jump with No_Return;

   generic
   function Call_Jump_Fun return Boolean with
     Always_Terminates => False;

   function Call_Jump is new Call_Jump_Fun;

   generic
   procedure Call_Jump_Proc (B : Boolean) with
     No_Return,
     Always_Terminates => False,
     Global => null,
     Post => not B;

   procedure Call_Jump is new Call_Jump_Proc;

   function Silent_Call_Jump return Boolean;

   type T is tagged null record;

   generic
   procedure Proc_Gen (X : T) with
     Always_Terminates => False,
     Global => null;

   procedure Proc is new Proc_Gen;

end Bad_Spec;
