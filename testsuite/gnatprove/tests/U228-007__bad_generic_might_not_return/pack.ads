package Pack with SPARK_Mode is

   procedure Jump (B : Boolean) with No_Return, Pre => B;

   generic
   procedure Call_Jump_Gen (B : Boolean) with
     Always_Terminates => False,
     Global => null,
     Post => not B;

   procedure Call_Jump (B : Boolean) with
     Always_Terminates => False,
     Global => null,
     Post => not B;

   procedure Proc with
     Always_Terminates => False,
     Global => null;

   procedure Call_Jump2 (B : Boolean) with
     Always_Terminates => False,
     Post => not B;
   --  This is the same as Call_Jump, but without a Global contract

   X, Y : Boolean := True;

   generic
   procedure Effect_Gen (B : Boolean) with
     Always_Terminates => False,
     Global => (In_Out => (X, Y));
   --  This tracks the global effects on paths that (might) not return

end Pack;
