package body P is
   S : String (1 .. 10) := "1234567890";

   procedure P1 is
      V : Integer := 1;
      subtype Index is Integer range V .. 3;
      S1 : String renames S (Index);
      --  Illegal; SPARK RM 4.4(2) bans this kind of
      --  expression with variable input.
   begin
      S1 (S1'First) := S(S'Last);
   end P1;

   procedure P2 is
      V : Integer := 1;
      S1 : String renames S (Positive range V .. 3);
      --  Variation on illegal theme from P1, but exercises
      --  surprisingly different code.
   begin
      S1 (S1'First) := S(S'Last);
   end P2;

   procedure P3 is
      V : constant Integer := 1;
      subtype Index is Integer range V .. 3;
      --  Legal, as V is constant
      S1 : String renames S (Index);
   begin
      S1 (S1'First) := S(S'Last);
   end P3;

end P;
