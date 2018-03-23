package Rack is

   protected P1 is
      procedure Set (Arg : Integer);
      function State return Integer with Volatile_Function;
   private
      My_State : Integer := 0;
   end P1;

   protected P2 is
      procedure Set (Arg : Integer);
      function State return Integer with Volatile_Function;
   private
      My_State : Integer := 0;
   end P2;

end Rack;
