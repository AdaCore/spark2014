package Bad with SPARK_Mode is

   procedure Jump with No_Return;

   function Call_Jump return Boolean;

   procedure Call_Jump (B : Boolean) with
     Annotate => (GNATprove, Might_Not_Return),
     Global => null,
     Post => not B;

   function Silent_Call_Jump return Boolean;

   type T is tagged null record;

   procedure Proc (X : T) with
     Global => null;

end Bad;
