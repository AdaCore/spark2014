package P is
   pragma Elaborate_Body;

   X : Boolean;
   function F_True return Boolean is (True);
   function F_X return Boolean is (X);

   function F_False return Boolean
     with Post => not F_False'Result;

   function F_False return Boolean is (False);

   function F_Y return Boolean
     with Post => F_Y'Result = X;

   function F_Y return Boolean is (X);
end;
