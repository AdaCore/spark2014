procedure Test_Handlers with SPARK_Mode is

   E1, E2, E3 : exception;

   --  Test that handlers are properly handled in the Why3 translation

   procedure P1 (X : Integer; Y : aliased out Integer) with
     Post => (X = 3 and Y = 3) or else Y = 42,
     Exceptional_Cases =>
       (E1 => X = 1 and Y = 1,
        E2 => X = 2 and Y = 2);

   procedure P1 (X : Integer; Y : aliased out Integer) is
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
         raise E3;
      when others =>
         Y := 42;
      end case;
   exception
      when E1 =>
         raise E1;
      when E2 =>
         Y := Y * 2;
         raise E2;
      when others =>
         null;
   end P1;

   procedure P2 (X : Integer; Y : aliased out Integer) with
     Post => Y = 42,
     Exceptional_Cases =>
       (E1 => X = 1 and Y = 1);

   procedure P2 (X : Integer; Y : aliased out Integer) is
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
         raise E3;  --@RAISE:FAIL
      when others =>
         Y := 42;
      end case;
   exception
      when E1 =>
         raise E1;
      when E2 =>
         Y := Y * 2;
         raise E2;  --@RAISE:FAIL
   end P2;

   procedure P3 (X : Integer; Y : aliased out Integer) with
     Post => Y = 42,
     Exceptional_Cases =>
       (E1 => X in 1 | 2 and Y = 1,
        E3 => X = Y);

   procedure P3 (X : Integer; Y : aliased out Integer) is
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
         raise E3;
      when others =>
         Y := 42;
      end case;
   exception
      when E1 | E2 =>
         raise E1;
   end P3;

   procedure P4 (X : Integer; Y : aliased out Integer) with
     Post => Y = 42,
     Exceptional_Cases =>
       (E1 => X in 1 | 2 | 3 and Y = 1);

   procedure P4 (X : Integer; Y : aliased out Integer) is
   begin
      case X is
      when 1 =>
         Y := 1;
         raise E1;
      when 2 =>
         Y := 1;
         raise E2;
      when 3 =>
         Y := 1;
         raise E3;
      when others =>
         Y := 42;
      end case;
   exception
      when others =>
         raise E1;
   end P4;

   --  Test that we expect handlers in extended return and declare statements

   function F (X : Integer) return Integer with
     Post => F'Result = X;

   function F (X : Integer) return Integer is
   begin
      return Y : Integer do
         case X is
         when 1 =>
            Y := 1;
            raise E1;
         when 2 =>
            Y := 1;
            raise E2;
         when 3 =>
            Y := 1;
         when others =>
            Y := X;
            return;
         end case;
         raise E3;
      exception
         when E3 =>
            Y := Y * 3;
         when E2 =>
            Y := Y * 2;
         when others =>
            null;
      end return;
   end F;

   procedure P5 (X : Integer; Y : aliased out Integer) with
     Post => Y = 42,
     Exceptional_Cases =>
       (E1 => X in 1 | 2 | 3 and Y = X);

   procedure P5 (X : Integer; Y : aliased out Integer) is
   begin
      begin
         case X is
         when 1 =>
            Y := 1;
            raise E1;
         when 2 =>
            Y := 1;
            raise E2;
         when 3 =>
            Y := 1;
            raise E3;
         when others =>
            Y := 42;
         end case;
      exception
         when E3 =>
            Y := Y * 3;
            raise E2;
         when E2 =>
            Y := Y * 2;
            raise E3;
      end;
   exception
      when others =>
         raise E1;
   end P5;

begin
   null;
end;
