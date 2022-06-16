procedure Main is
   type T is access Integer;

   X : T := new Integer'(10);
   Y : T := X;
   Z : T := X;
begin
   null;
end Main;
