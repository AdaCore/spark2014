package body Rack is

   protected body P1 is
      procedure Set (Arg : Integer) is
      begin
        My_State := Arg;
      end Set;

      function State return Integer is (My_State);
   end P1;

   protected body P2 is
      procedure Set (Arg : Integer) is
         Const : constant Integer := P1.State;
      begin
         My_State := Arg + Const;
      end Set;

      function State return Integer is (My_State);
   end P2;

end Rack;
