package P with
   Initializes       => (X, Y),
   Initial_Condition => X and Y.C
is
   type T is record
      C : Boolean;
   end record;

   X : Boolean := False;
   Y : T       := (C => False);
   --  Both objects are declared as False, but set to True in body;
   --  one is a scalar, other is a record.

   pragma Assert (not X and not Y.C);
   --  Make use of the declared values (otherwise we will get a warning)

   procedure Set (A : out Boolean) with Post => A, Global => null;
   --  Will be used to indirectly set objects to True (if we set them with
   --  direct assignments, then frontend is smart enough to complain about the
   --  missing pragma Elaborate_Body;

end P;
