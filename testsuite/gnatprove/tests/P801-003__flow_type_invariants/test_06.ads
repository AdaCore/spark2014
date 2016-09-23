package Test_06 with Elaborate_Body is

   type T is private;

   function F (X : T) return Boolean;

private

   type T is record
      A : Boolean := False;
      B : Boolean := True;
   end record
   with Type_Invariant => F (T);

   --  Not OK, call to boundary subprogram in invariant.

end Test_06;
