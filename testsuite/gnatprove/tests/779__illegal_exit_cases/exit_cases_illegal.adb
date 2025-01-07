procedure Exit_Cases_Illegal with SPARK_Mode is

   E1, E2 : exception;

   --  Exit cases contracts on procedure always returning normally

   procedure P_1 (X : Integer) with
     Exit_Cases =>
       (X = 1 => Normal_Return,
        X = 2 => Normal_Return);

   procedure P_1 (X : Integer) is
   begin
      case X is
      when 1 =>
         return;
      when 2 =>
         return;
      when others =>
         return;
      end case;
   end P_1;

   --  Exit cases with exception when none is allowed

   procedure P_2 (X : Integer) with
     Exit_Cases =>
       (X = 1 => Normal_Return,
        X = 2 => Exception_Raised),
     Exceptional_Cases => (others => False);

   procedure P_2 (X : Integer) is
   begin
      case X is
      when 1 =>
         return;
      when 2 =>
         raise E1;
      when others =>
         raise E2;
      end case;
   end P_2;

   --  Exit cases with unexpected exception

   procedure P_3 (X : Integer) with
     Exit_Cases =>
       (X = 1 => Normal_Return,
        X = 2 => (Exception_Raised => E1)),
     Exceptional_Cases => (E2 => True);

   procedure P_3 (X : Integer) is
   begin
      case X is
      when 1 =>
         return;
      when 2 =>
         raise E1;
      when others =>
         raise E2;
      end case;
   end P_3;

   package Nested is
      type Root is tagged record
         F : Integer;
      end record;

      --  Exit cases contracts on dispatching operation

      procedure P_4 (X : Root) with
        Exit_Cases =>
          (X.F = 1 => Normal_Return,
           X.F = 2 => (Exception_Raised => E1));
   end Nested;

   package body Nested is
      procedure P_4 (X : Root) is
      begin
         case X.F is
         when 1 =>
            return;
         when 2 =>
            raise E1;
         when others =>
            return;
         end case;
      end P_4;
   end Nested;

begin
   null;
end Exit_Cases_Illegal;
