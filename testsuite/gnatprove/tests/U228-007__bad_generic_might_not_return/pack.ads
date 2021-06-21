package Pack with SPARK_Mode is

   procedure Jump (B : Boolean) with No_Return, Pre => B;

   generic
   procedure Call_Jump_Gen (B : Boolean) with
     Annotate => (GNATprove, Might_Not_Return),
     Global => null,
     Post => not B;

   procedure Call_Jump (B : Boolean) with
     Annotate => (GNATprove, Might_Not_Return),
     Global => null,
     Post => not B;

   procedure Proc with
     Annotate => (GNATprove, Might_Not_Return),
     Global => null;

   procedure Call_Jump2 (B : Boolean) with
     Annotate => (GNATprove, Might_Not_Return),
     Post => not B;
   --  This is the same as Call_Jump, but without a Global contract

   X, Y : Boolean := True;

   generic
   procedure Effect_Gen (B : Boolean) with
     Annotate => (GNATprove, Might_Not_Return),
     Global => (In_Out => (X, Y));
   --  This tracks the global effects on paths that (might) not return

end Pack;
