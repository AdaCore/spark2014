package body P is
   function F3 return Boolean is (True);
   function F4 return Boolean is
   begin
      return True;
   end F4;

   function CF1 return Boolean is (F1);
   function CF2 return Boolean is (F2);
   function CF3 return Boolean is (F3);
   function CF4 return Boolean is (F4);

   procedure P1
     with Pre => CF1;

   procedure P1 is
   begin
      null;
   end P1;

   procedure P2
     with Pre => CF2;

   procedure P2 is
   begin
      null;
   end P2;

   procedure P3
     with Pre => CF3;

   procedure P3 is
   begin
      null;
   end P3;

   procedure P4
     with Pre => CF4;

   procedure P4 is
   begin
      null;
   end P4;

end P;
