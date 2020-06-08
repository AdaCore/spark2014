package Bad_Spec with SPARK_Mode is

   procedure Jump with No_Return;

   function Call_Jump return Boolean with
     Annotate => (GNATprove, Might_Not_Return);

   procedure Call_Jump (B : Boolean) with
     No_Return,
     Annotate => (GNATprove, Might_Not_Return),
     Global => null,
     Post => not B;

   function Silent_Call_Jump return Boolean;

   type T is tagged null record;

   procedure Proc (X : T) with
     Annotate => (GNATprove, Might_Not_Return),
     Global => null;

end Bad_Spec;
