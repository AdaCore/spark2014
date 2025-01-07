procedure Exit_Cases_Bad with SPARK_Mode is

   E1, E2 : exception;

   --  Non-disjoint exit cases

   procedure P_1 (X : Integer) with
     Exit_Cases => -- @DISJOINT_CASES:FAIL
       (X = 1 => Normal_Return,
        X < 2 => Normal_Return,
        X = 2 => Exception_Raised);

   procedure P_1 (X : Integer) is
   begin
      case X is
      when 1 =>
         return;
      when 2 =>
         raise E1;
      when others =>
         return;
      end case;
   end P_1;

   --  Incorrect normal return exit cases.
   --  Regular choice, no others.

   procedure P_2 (X : Integer) with
     Exit_Cases =>
       (X = 1 => Normal_Return, -- @EXIT_CASE:FAIL
        X = 2 => Exception_Raised);

   procedure P_2 (X : Integer) is
   begin
      case X is
      when 1 =>
         raise E2;
      when 2 =>
         raise E1;
      when others =>
         return;
      end case;
   end P_2;

   --  Others choice

   procedure P_3 (X : Integer) with
     Exit_Cases =>
       (X = 1 => Normal_Return,
        X = 2 => Exception_Raised,
        others => Normal_Return); -- @EXIT_CASE:FAIL

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

   --  Regular choice, others is normal

   procedure P_4 (X : Integer) with
     Exit_Cases =>
       (X = 1 => Normal_Return, -- @EXIT_CASE:FAIL
        X = 2 => Exception_Raised,
        others => Normal_Return);

   procedure P_4 (X : Integer) is
   begin
      case X is
      when 1 =>
         raise E2;
      when 2 =>
         raise E1;
      when others =>
         return;
      end case;
   end P_4;

   --  Regular choice, others is exceptional

   procedure P_5 (X : Integer) with
     Exit_Cases =>
       (X = 1 => Normal_Return, -- @EXIT_CASE:FAIL
        X = 2 => Exception_Raised,
        others => Exception_Raised);

   procedure P_5 (X : Integer) is
   begin
      case X is
      when 1 =>
         raise E2;
      when 2 =>
         raise E1;
      when others =>
         raise E2;
      end case;
   end P_5;

   --  Incorrect exceptional exit cases.
   --  Regular choice.

   procedure P_6 (X : Integer) with
     Exit_Cases =>
       (X = 1 => Normal_Return,
        X = 2 => Exception_Raised); -- @EXIT_CASE:FAIL

   procedure P_6 (X : Integer) is
   begin
      case X is
      when 1 =>
         return;
      when 2 =>
         return;
      when others =>
         raise E1;
      end case;
   end P_6;

   --  Others choice

   procedure P_7 (X : Integer) with
     Exit_Cases =>
       (X = 1 => Normal_Return,
        X = 2 => Exception_Raised,
        others => Exception_Raised); -- @EXIT_CASE:FAIL

   procedure P_7 (X : Integer) is
   begin
      case X is
      when 1 =>
         return;
      when 2 =>
         raise E1;
      when others =>
         return;
      end case;
   end P_7;

   --  Wrong exception

   procedure P_8 (X : Integer) with
     Exit_Cases =>
       (X = 1 => Normal_Return,
        X = 2 => (Exception_Raised => E1), -- @EXIT_CASE:FAIL
        others => Exception_Raised);

   procedure P_8 (X : Integer) is
   begin
      case X is
      when 1 =>
         return;
      when 2 =>
         raise E2;
      when others =>
         raise E1;
      end case;
   end P_8;

begin
   null;
end Exit_Cases_Bad;
