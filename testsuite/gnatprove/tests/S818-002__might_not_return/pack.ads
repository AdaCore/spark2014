package Pack with SPARK_Mode is

   procedure Jump (B : Boolean) with No_Return, Pre => B;

   procedure Call_Jump (B : Boolean) with
     Annotate => (GNATprove, Might_Not_Return),
     Global => null,
     Post => not B;

   procedure Proc with
     Annotate => (GNATprove, Might_Not_Return),
     Global => null;

end Pack;
