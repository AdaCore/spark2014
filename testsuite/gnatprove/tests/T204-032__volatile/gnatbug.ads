package gnatBug is

   type T is record
      C : Integer;
   end record with Volatile;

   procedure P (X : T) with Global => null;

end gnatBug;
