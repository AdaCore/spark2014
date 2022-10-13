package Connection
  with SPARK_Mode
is
   type Connection_Id_T is private
   with
     Default_Initial_Condition => Is_Detached (Connection_Id_T),
     Annotate => (GNATprove, Ownership, "Needs_Reclamation");

   function Is_Detached
     (Coid : Connection_Id_T)
      return Boolean
   with
     Ghost,
     Import,
     Global => null,
     Annotate => (GNATprove, Always_Return),
     Annotate => (GNATprove, Ownership, "Is_Reclaimed");

private
   pragma SPARK_Mode (Off);

   type Connection_Id_T is new Integer;

end Connection;
