procedure Main is
   type T is access function return Boolean;

   function F return Boolean with Post => False;
   function G return Boolean;

   function G return Boolean is (F);

   function F return Boolean is
      X : T := G'Access;
   begin
      return X.all;
   end;
begin
   null;
end;
