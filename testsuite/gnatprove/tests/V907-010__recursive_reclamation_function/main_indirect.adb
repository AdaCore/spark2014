procedure Main_Indirect with SPARK_Mode is

   package Nested with Annotate => (GNATprove, Always_Return)
   is
      type Pool_Specific_Access is private with
        Default_Initial_Condition =>
          Is_Null_Int (Pool_Specific_Access, Pool_Specific_Access),
        Annotate => (GNATprove, Ownership, "Needs_Reclamation");

      function Is_Null_Int (A, B : Pool_Specific_Access) return Boolean with
        Import,
        Global => null;

   private
      pragma SPARK_Mode (Off);
      type Pool_Specific_Access is access Integer;
   end Nested;
   use Nested;

   function Is_Null_One (A : Pool_Specific_Access) return Boolean
     with Global => null,
     Post => False --  Should not be provable, it is a tool limitation
   is
      X : Pool_Specific_Access;
      --  Implicit recusion for proof as Is_Null is used to check for leaks
      --  when X goes out of scope.
   begin
      return Is_Null_Int (A, X);
   end Is_Null_One;

   function Is_Null (A : Pool_Specific_Access) return Boolean with
     Global => null,
     Post => False, --  Should not be provable, it is a tool limitation
     Annotate => (GNATprove, Ownership, "Is_Reclaimed");

   function Is_Null (A : Pool_Specific_Access) return Boolean is
   begin
      return Is_Null_One (A);
   end Is_Null;

begin
   null;
end Main_Indirect;
