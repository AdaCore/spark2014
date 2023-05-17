package Private_Discriminants with
  SPARK_Mode,
  Always_Terminates
is
   type Pool_Specific_Access (B : Boolean := False) is private with
     Default_Initial_Condition => Is_Null (Pool_Specific_Access),
     Annotate => (GNATprove, Ownership, "Needs_Reclamation");

   function Is_Null (A : Pool_Specific_Access) return Boolean with
     Global => null,
     Annotate => (GNATprove, Ownership, "Is_Reclaimed");
   function Deref (A : Pool_Specific_Access) return Integer with
     Global => null,
     Pre => not Is_Null (A);

   function Allocate (X : Integer) return Pool_Specific_Access with
     Global => null,
     Post => not Is_Null (Allocate'Result) and then Deref (Allocate'Result) = X;
   procedure Deallocate (A : in out Pool_Specific_Access) with
     Global => null,
     Post => Is_Null (A);

private
   pragma SPARK_Mode (Off);
   type Pool_Specific_Access (B : Boolean := False) is record
      Content : access Integer;
   end record;
end Private_Discriminants;
