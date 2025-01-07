procedure Exit_Cases_OK with SPARK_Mode is

   E1, E2 : exception;

   --  Correct exit cases contracts

   procedure P_1 (X : Integer) with
     Exit_Cases => -- @DISJOINT_CASES:PASS
       (X = 1 => Normal_Return, -- @EXIT_CASE:PASS
        X = 2 => Normal_Return, -- @EXIT_CASE:PASS
        X = 3 => (Exception_Raised => E2), -- @EXIT_CASE:PASS
        others => Exception_Raised); -- @EXIT_CASE:PASS

   procedure P_1 (X : Integer) is
   begin
      case X is
      when 1 =>
         return;
      when 2 =>
         return;
      when 3 =>
         raise E2;
      when others =>
         raise E1;
      end case;
   end P_1;

   procedure Call_P_1 (X : Integer) with
     Exit_Cases => -- @DISJOINT_CASES:PASS
       (X = 1 => Normal_Return, -- @EXIT_CASE:PASS
        X = 2 => Normal_Return, -- @EXIT_CASE:PASS
        X = 3 => (Exception_Raised => E2), -- @EXIT_CASE:PASS
        others => Exception_Raised); -- @EXIT_CASE:PASS

   procedure Call_P_1 (X : Integer) is
   begin
      P_1 (X);
   end Call_P_1;

   procedure P_2 (X : Integer) with
     Exit_Cases => -- @DISJOINT_CASES:PASS
       (X = 1 => Normal_Return, -- @EXIT_CASE:PASS
        X = 2 => (Exception_Raised => E1), -- @EXIT_CASE:PASS
        X = 3 => (Exception_Raised => E2), -- @EXIT_CASE:PASS
        others => Normal_Return); -- @EXIT_CASE:PASS

   procedure P_2 (X : Integer) is
   begin
      case X is
      when 1 =>
         return;
      when 2 =>
         raise E1;
      when 3 =>
         raise E2;
      when others =>
         return;
      end case;
   end P_2;

   procedure Call_P_2 (X : Integer) with
     Exit_Cases => -- @DISJOINT_CASES:PASS
       (X = 1 => Normal_Return, -- @EXIT_CASE:PASS
        X = 2 => (Exception_Raised => E1), -- @EXIT_CASE:PASS
        X = 3 => (Exception_Raised => E2), -- @EXIT_CASE:PASS
        others => Normal_Return); -- @EXIT_CASE:PASS

   procedure Call_P_2 (X : Integer) is
   begin
      P_2 (X);
   end Call_P_2;

   procedure P_3 (X : Integer) with
     Exit_Cases => -- @DISJOINT_CASES:PASS
       (X = 1 => Normal_Return, -- @EXIT_CASE:PASS
        X = 2 => Normal_Return, -- @EXIT_CASE:PASS
        X = 3 => (Exception_Raised => E2), -- @EXIT_CASE:PASS
        X = 4 => Exception_Raised); -- @EXIT_CASE:PASS

   procedure P_3 (X : Integer) is
   begin
      case X is
      when 1 =>
         return;
      when 2 =>
         return;
      when 3 =>
         raise E2;
      when others =>
         raise E1;
      end case;
   end P_3;

   procedure Call_P_3 (X : Integer) with
     Exit_Cases => -- @DISJOINT_CASES:PASS
       (X = 1 => Normal_Return, -- @EXIT_CASE:PASS
        X = 2 => Normal_Return, -- @EXIT_CASE:PASS
        X = 3 => (Exception_Raised => E2), -- @EXIT_CASE:PASS
        X = 4 => Exception_Raised); -- @EXIT_CASE:PASS

   procedure Call_P_3 (X : Integer) is
   begin
      P_3 (X);
   end Call_P_3;

   procedure P_4 (X : Integer) with
     Exit_Cases => -- @DISJOINT_CASES:PASS
       (X = 1 => Normal_Return, -- @EXIT_CASE:PASS
        X = 2 => (Exception_Raised => E1), -- @EXIT_CASE:PASS
        X = 3 => (Exception_Raised => E2), -- @EXIT_CASE:PASS
        X = 4 => Normal_Return); -- @EXIT_CASE:PASS

   procedure P_4 (X : Integer) is
   begin
      case X is
      when 1 =>
         return;
      when 2 =>
         raise E1;
      when 3 =>
         raise E2;
      when others =>
         return;
      end case;
   end P_4;

   procedure Call_P_4 (X : Integer) with
     Exit_Cases => -- @DISJOINT_CASES:PASS
       (X = 1 => Normal_Return, -- @EXIT_CASE:PASS
        X = 2 => (Exception_Raised => E1), -- @EXIT_CASE:PASS
        X = 3 => (Exception_Raised => E2), -- @EXIT_CASE:PASS
        X = 4 => Normal_Return); -- @EXIT_CASE:PASS

   procedure Call_P_4 (X : Integer) is
   begin
      P_4 (X);
   end Call_P_4;

   --  Correct exit cases - degenerated cases where an exception is always
   --  raised/never raised.

   procedure P_5 (X : Integer) with
     Exit_Cases =>  -- @DISJOINT_CASES:PASS
       (X = 1 => (Exception_Raised => E2), -- @EXIT_CASE:PASS
        X = 2 => (Exception_Raised => E2), -- @EXIT_CASE:PASS
        X = 3 => (Exception_Raised => E2), -- @EXIT_CASE:PASS
        others => Exception_Raised);

   procedure P_5 (X : Integer) is
   begin
      raise E2;
   end P_5;

   procedure Call_P_5 (X : Integer) with
     Exit_Cases => -- @DISJOINT_CASES:PASS
       (X = 1 => (Exception_Raised => E2), -- @EXIT_CASE:PASS
        X = 2 => (Exception_Raised => E2), -- @EXIT_CASE:PASS
        X = 3 => (Exception_Raised => E2), -- @EXIT_CASE:PASS
        others => Exception_Raised); -- @EXIT_CASE:PASS

   procedure Call_P_5 (X : Integer) is
   begin
      P_5 (X);
   end Call_P_5;

   procedure P_6 (X : Integer) with
     Exit_Cases => -- @DISJOINT_CASES:PASS
       (X = 1 => Normal_Return, -- @EXIT_CASE:PASS
        X = 2 => Normal_Return, -- @EXIT_CASE:PASS
        X = 3 => Normal_Return, -- @EXIT_CASE:PASS
        others => Normal_Return), -- @EXIT_CASE:PASS
     Exceptional_Cases => (others => True);

   procedure P_6 (X : Integer) is
   begin
      return;
   end P_6;

   procedure Call_P_6 (X : Integer) with
     Exit_Cases => -- @DISJOINT_CASES:PASS
       (X = 1 => Normal_Return, -- @EXIT_CASE:PASS
        X = 2 => Normal_Return, -- @EXIT_CASE:PASS
        X = 3 => Normal_Return, -- @EXIT_CASE:PASS
        others => Normal_Return), -- @EXIT_CASE:PASS
     Exceptional_Cases => (others => True);

   procedure Call_P_6 (X : Integer) is
   begin
      P_6 (X);
   end Call_P_6;

   procedure P_7 (X : Integer) with
     Exit_Cases => -- @DISJOINT_CASES:PASS
       (X = 1 => (Exception_Raised => E2), -- @EXIT_CASE:PASS
        X = 2 => (Exception_Raised => E2), -- @EXIT_CASE:PASS
        X = 3 => (Exception_Raised => E2), -- @EXIT_CASE:PASS
        X = 4 => Exception_Raised);

   procedure P_7 (X : Integer) is
   begin
      raise E2;
   end P_7;

   procedure Call_P_7 (X : Integer) with
     Exit_Cases => -- @DISJOINT_CASES:PASS
       (X = 1 => (Exception_Raised => E2), -- @EXIT_CASE:PASS
        X = 2 => (Exception_Raised => E2), -- @EXIT_CASE:PASS
        X = 3 => (Exception_Raised => E2), -- @EXIT_CASE:PASS
        X = 4 => Exception_Raised); -- @EXIT_CASE:PASS

   procedure Call_P_7 (X : Integer) is
   begin
      P_7 (X);
   end Call_P_7;

   procedure P_8 (X : Integer) with
     Exit_Cases => -- @DISJOINT_CASES:PASS
       (X = 1 => Normal_Return, -- @EXIT_CASE:PASS
        X = 2 => Normal_Return, -- @EXIT_CASE:PASS
        X = 3 => Normal_Return, -- @EXIT_CASE:PASS
        X = 4 => Normal_Return), -- @EXIT_CASE:PASS
     Exceptional_Cases => (others => True);

   procedure P_8 (X : Integer) is
   begin
      return;
   end P_8;

   procedure Call_P_8 (X : Integer) with
     Exit_Cases => -- @DISJOINT_CASES:PASS
       (X = 1 => Normal_Return, -- @EXIT_CASE:PASS
        X = 2 => Normal_Return, -- @EXIT_CASE:PASS
        X = 3 => Normal_Return, -- @EXIT_CASE:PASS
        X = 4 => Normal_Return), -- @EXIT_CASE:PASS
     Exceptional_Cases => (others => True);

   procedure Call_P_8 (X : Integer) is
   begin
      P_8 (X);
   end Call_P_8;

begin
   null;
end Exit_Cases_OK;
