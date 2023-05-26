procedure Exc_Cases_And_Annotations with SPARK_Mode is

   procedure Always_Return_P (X : in out Integer) with
     Import,
     Global => null,
     Annotate => (GNATprove, Always_Return),
     Exceptional_Cases => (Constraint_Error => True);

   function F return Integer with
     Import,
     Global => null;

   procedure Lemma (X : in out Integer) with
     Import,
     Ghost,
     Global => null,
     Annotate => (GNATprove, Automatic_Instantiation),
     Exceptional_Cases => (Constraint_Error => True);

begin
   null;
end Exc_Cases_And_Annotations;
