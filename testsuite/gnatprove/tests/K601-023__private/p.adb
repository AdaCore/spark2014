procedure P is
   package P0 is
      type F0 is private;
   private
      type F0 is range 0 .. 1;
   end P0;

   package P1 is
      type FC is private;
   private
      type FC is new P0.F0;
   end  P1;

begin
   null;
end P;
