package Pack is
   type T1 is record
      X : Boolean;
   end record;
   type T2 is new Integer range 1 .. 10;
   X1 : constant T1;
   X2 : constant T2;

   function Query_X1 return Boolean with
     Post => Query_X1'Result = True;

   function Query_X2 return T2 with
     Post => Query_X2'Result = 3;
private
   X1 : constant T1 := (X => True);
   X2 : constant T2 := 3;

   function Query_X1 return Boolean is (X1.X);
end Pack;
