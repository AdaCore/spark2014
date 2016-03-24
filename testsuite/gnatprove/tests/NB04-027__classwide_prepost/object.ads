package Object is

   type T is tagged record
      B : Boolean;
   end record;

   procedure Create (X : out T) with
     Post'Class => X.B;

end Object;
