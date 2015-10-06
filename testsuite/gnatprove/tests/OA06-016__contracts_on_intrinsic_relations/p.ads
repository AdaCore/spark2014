package P
  with SPARK_Mode => On
is

   type Time_Span is private;

   T_Zero : constant Time_Span;

   function ">" (Left, Right : Time_Span) return Boolean;
   --  with Global => null;

   function "abs" (Left : Time_Span) return Time_Span;

   procedure Proc1 (X : Time_Span) with Pre => X > T_Zero;
   procedure Proc2 (X : Time_Span) with Pre => True;

private
   pragma SPARK_Mode (On);

   type Time_Span is range -10 .. 10;

   T_Zero : constant Time_Span := 0;

   pragma Import (Intrinsic, ">");
   pragma Import (Intrinsic, "abs");
end;
