package body Test is

   procedure Test_01 (A : Integer;
                      B : out Integer)
   is
      L : Integer;
   begin
      if A > 10 then
         L := 5;
         B := L;
      else
         B := 10;
      end if;
      --  OK
   end Test_01;

   procedure Test_02 (A : Integer;
                      B : out Integer)
   is
      L : Integer;
   begin
      if A > 10 then
         L := 5;
         B := L;
      end if;
      --  B may not be set
   end Test_02;

   procedure Test_03 (A : Integer;
                      B : out Integer;
                      C : out Integer)
   is
      L : Integer;
   begin
      if A > 10 then
         L := 5;
         B := L;
      end if;
      --  B and C may not be set
   end Test_03;

end Test;
