with SPARK.Cut_Operations; use SPARK.Cut_Operations;
procedure Cut_Operations_Context with SPARK_Mode is
   procedure Test1 (A, B : Boolean) with Global => null is
   begin
      pragma Assert (By (A, B));
      pragma Assert_And_Cut (By (A, B));
      pragma Assume (By (A, B));  -- INCORRECT
   end Test1;
   procedure Test2 (A, B : Boolean) with
     Import,
     Post => By (A, B);  -- INCORRECT
   procedure Test3 (A, B : Boolean) with
     Import,
     Pre => By (A, B);  -- INCORRECT
   procedure Test4 (A, B, C : Boolean) with Global => null is
   begin
      pragma Assert (if C then By (A, B) else By (B, A));
      pragma Assert (if By (A, B) then C else not C);  -- INCORRECT
   end Test4;
   procedure Test5 (A, B, C : Boolean) with Global => null is
   begin
      pragma Assert (case C is when True => By (A, B), when False => By (B, A));
      pragma Assert (case By (A, B) is when True => C, when False => not C);  -- INCORRECT
   end Test5;
   procedure Test6 with Global => null is
      function A (X : Integer) return Boolean with Import;
      function B (X : Integer) return Boolean with Import;
   begin
      pragma Assert (for all X in 1 .. 10 => By (A (X), B (X)));
      pragma Assert (for all X in 1 .. 10 when By (A (X), B (X)) => X > 0);  -- INCORRECT
      pragma Assert (for some X in Boolean range By (A (1), B (1)) .. False => not X);  -- INCORRECT
   end Test6;
   procedure Test7 (A, B, C : Boolean) with Global => null is
   begin
      pragma Assert (By (A, B) or By (A, C));
      pragma Assert (By (A, B) or else By (A, C));
      pragma Assert (By (A, B) and By (C, B));
      pragma Assert (By (A, B) and then By (C, B));
   end Test7;
   procedure Test8 (A, B, C : Boolean) with Global => null is
   begin
      pragma Assert (declare D : constant Boolean := B and not C; begin By (A, D));
      pragma Assert (declare D : constant Boolean := By (A, B); begin C and D);  -- INCORRECT
   end Test8;
   procedure Test9 (A, B, C : Boolean) with Global => null is
      function P (X : Boolean) return Boolean with Import;
   begin
      pragma Assert (By (A, So (B, C)));
      pragma Assert (By (Consequence => A, Premise => So (B, C)));
      pragma Assert (P (By (A, So (B, C))));  -- INCORRECT
   end Test9;
begin
   null;
end Cut_Operations_Context;
