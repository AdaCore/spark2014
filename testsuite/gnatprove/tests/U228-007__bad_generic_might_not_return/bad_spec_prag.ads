package Bad_Spec_Prag with SPARK_Mode is

   generic
   procedure Jump with No_Return;
   pragma Annotate (GNATprove, Might_Not_Return);

   generic
   function Call_Jump_Fun return Boolean;
   pragma Annotate (GNATprove, Might_Not_Return, Call_Jump_Fun);

   generic
   procedure Call_Jump (B : Boolean) with
     No_Return,
     Global => null,
     Post => not B;
   pragma Annotate (GNATprove, Might_Not_Return, Call_Jump);

   function Silent_Call_Jump return Boolean;

   type T is tagged null record;
   pragma Annotate (GNATprove, Might_Not_Return, T);

   generic
   procedure Proc (X : T) with
     Global => null;
   pragma Annotate (GNATprove, Might_Not_Return, Proc);

end Bad_Spec_Prag;
