package Bad_Spec with SPARK_Mode is

   procedure Jump with No_Return;

   function Call_Jump return Boolean;
   --   Always_Terminates cannot apply to functions

   procedure Call_Jump (B : Boolean) with
     No_Return,
     Always_Terminates => False,
     Global => null,
     Post => not B;

   function Silent_Call_Jump return Boolean;

   type T is tagged null record;

   procedure Proc (X : T) with
     Always_Terminates => False,
     Global => null;

end Bad_Spec;
