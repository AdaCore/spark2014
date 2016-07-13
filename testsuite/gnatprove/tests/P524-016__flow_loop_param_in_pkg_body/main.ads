package Main with
   Elaborate_Body
is

   package P with
      Initializes => V
   is
      type T is record
         V : Boolean;
      end record;
      V : T;
      procedure Dummy;
   end P;

end Main;
