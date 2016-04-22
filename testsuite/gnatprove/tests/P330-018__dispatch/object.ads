package Object is

   type T is tagged record
      B : Boolean := True;
   end record;

   function Is_Valid (X : T) return Boolean is (X.B);

   procedure Do_Stuff (X : in out T) is null with
     Pre'Class => Is_Valid (X);

end Object;
