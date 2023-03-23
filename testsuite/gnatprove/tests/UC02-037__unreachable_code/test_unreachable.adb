procedure Test_Unreachable with SPARK_Mode is

   E1, E2, E3 : exception;

   --  Test that we get a warning on unreachable handlers

   procedure P (X : Integer; Y : aliased out Integer) with
     Post => (X = Y) or else Y = 42,
     Exceptional_Cases =>
       (E1 => X = 1 and Y = 1,
        E2 => X = 2 and Y = 2); --  Unreachable branch

   procedure P (X : Integer; Y : aliased out Integer) is
   begin
      case X is
      when 1 =>
         Y := 1;
         raise E1;
      when 2 =>
         Y := 1;
         raise E2;
      when 3 =>
         Y := 3;
      when others =>
         Y := 42;
      end case;
   exception
      when E1 =>
         raise E1;
      when E2 =>
         Y := Y * 2;
      when others =>
         null; --  Unreachable code
   end P;

begin
   null;
end;
