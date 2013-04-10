with Other;

package body Test
is

   Y : Integer;

   --  OK
   procedure Test_01
   is
   begin
      Other.Initialise;
   end Test_01;

   --  Bad
   procedure Test_02
     with Depends => null
   is
   begin
      Other.Initialise;
   end Test_02;

   --  Bad for several reasons
   procedure Test_03
     with Depends => (Y => Y)
   is
   begin
      Other.Initialise;
   end Test_03;

   --  OK
   procedure Test_04
   is
   begin
      Y := Other.Get_X;
   end Test_04;

   --  Bad
   procedure Test_05
     with Depends => (Y => null)
   is
   begin
      Y := Other.Get_X;
   end Test_05;

   --  Bad
   procedure Test_06
     with Global => null
   is
   begin
      Other.Initialise;
   end Test_06;

   --  Bad
   procedure Test_07
     with Global => (Output => Y)
   is
   begin
      Y := Other.Get_X + Other.Get_X * 2;
   end Test_07;

end Test;
