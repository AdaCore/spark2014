package Qack is

   X : Boolean;
   procedure Flip;
   procedure Bad
     with Post => X = X'Old;

end;
