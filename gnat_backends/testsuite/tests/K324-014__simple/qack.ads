package Qack is

   X : Boolean;
   procedure Flip;
   procedure Bad
     with Post => X = X'Old; -- should not be provable (actually it is false)

end;
