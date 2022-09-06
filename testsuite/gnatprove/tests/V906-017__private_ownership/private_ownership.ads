package Private_Ownership with
  SPARK_Mode,
  Annotate => (GNATprove, Always_Return)
is
   package Nested is
      type Pool_Specific_Access is private with
        Annotate => (GNATprove, Ownership, "Needs_Reclamation");

      function Is_D (A : Pool_Specific_Access) return Boolean;

   private
      pragma SPARK_Mode (Off);
      type Pool_Specific_Access is access Integer;
   end Nested;
   use Nested;

   function Is_Null (A : Pool_Specific_Access) return Boolean with
     Global => null,
     Post => False, --@POSTCONDITION:FAIL
     Annotate => (GNATprove, Ownership, "Is_Reclaimed");

   function Is_Null (A : Pool_Specific_Access) return Boolean is
     (Is_D (A));
end Private_Ownership;
