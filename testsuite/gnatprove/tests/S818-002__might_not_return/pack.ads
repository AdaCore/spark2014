package Pack with SPARK_Mode is

   procedure Jump with No_Return;

   procedure Call_Jump (B : Boolean) with
     Annotate => (GNATprove, Might_Not_Return),
     Global => null,
     Post => not B;

   procedure Proc with
     Annotate => (GNATprove, Might_Not_Return),
     Global => null;

end Pack;
