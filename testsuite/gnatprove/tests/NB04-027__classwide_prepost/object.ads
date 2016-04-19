package Object is

   type T is tagged record
      B : Boolean;
   end record;

   procedure Create (X : out T) with
     Post'Class => X.B;

   function Is_Valid (X : T) return Boolean is (X.B);

   procedure Do_Stuff (X : in out T) with
     Pre'Class => Is_Valid (X);

end Object;
