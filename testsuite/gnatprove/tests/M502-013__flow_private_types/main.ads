package Main
is
   type T is private;
   type U is limited private;
   --   type V is tagged private;

   procedure Do_Stuff (X : in out T);

private

   type T is record
      A : Boolean;
      B : Boolean;
   end record;

   type U is record
      A : Boolean;
      B : Boolean;
   end record;

   --  type V is tagged record
   --     A : Boolean;
   --     B : Boolean;
   --  end record;

end Main;
