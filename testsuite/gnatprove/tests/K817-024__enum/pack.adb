procedure Pack is

   package P1 is
      type Priv is private;
   private
      type Priv is (One, Two, Three, Four, Five, Six);
   end P1;

   package P2 is
      type D is limited private;
   private
      type D is new P1.Priv;
   end P2;

begin
     null;
end Pack;
