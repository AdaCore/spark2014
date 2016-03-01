procedure Main is

   type T is record
      Dummy : Integer := 0;
   end record
   with Dynamic_Predicate => False;

   X : T; -- !!! check will fail here
begin
   null;
end;
