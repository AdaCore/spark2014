package Connection
  with SPARK_Mode
is
   type Connection_Id_T is private
   with
     Default_Initial_Condition => Is_Detached (Connection_Id_T),
     Annotate => (GNATprove, Ownership, "Needs_Reclamation");

   Null_Connection : constant Connection_Id_T;

   function Is_Detached
     (Coid : Connection_Id_T)
      return Boolean
   with
     Ghost,
     Import,
     Global => null,
     Annotate => (GNATprove, Always_Return),
     Annotate => (GNATprove, Ownership, "Is_Reclaimed");

   procedure Invalid_Connection_Id_Is_Detached (Coid : Connection_Id_T)
   with
     Ghost,
     Import,
     Global => null,
     Annotate => (GNATprove, Automatic_Instantiation),
     Pre =>
       Coid = Null_Connection,
     Post =>
       Is_Detached (Coid);

private
   pragma SPARK_Mode (Off);

   type Connection_Id_T is new Integer;

   Null_Connection : constant Connection_Id_T := 0;
end Connection;
