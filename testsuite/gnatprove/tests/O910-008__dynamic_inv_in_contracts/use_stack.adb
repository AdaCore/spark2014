with External_Var;

procedure Use_Stack with SPARK_Mode is
   package Stacks with Initial_Condition => Is_Empty is
      Max : constant Positive := External_Var.C;
      function Is_Full return Boolean;
      function Is_Empty return Boolean;
      function Peek return Positive with
        Pre => not Is_Empty;
      function All_Eq (E : Positive) return Boolean;

      procedure Pop (E : out Positive) with
        Pre  => not Is_Empty,
        Post => not Is_Full and Peek'Old = E;
      procedure Push (E : Positive) with
        Pre  => not Is_Full,
        Post => not Is_Empty and Peek = E;
      procedure Fill (E : Positive) with
        Pre  => Is_Empty,
        Post => Is_Full and All_Eq (E);
   private
      subtype Top_Range is Natural range 0 .. Max;
      type My_Array is array (1 .. Max) of Positive;

      Top     : Top_Range := 0;
      Content : My_Array;

      function Is_Full return Boolean is (Top = Max);
      function Is_Empty return Boolean is (Top = 0);
      function Peek return Positive is (Content (Top));
      function All_Eq (E : Positive) return Boolean is
        (for all I in Content'Range => Content (I) = E);
   end Stacks;
   package body Stacks is

      procedure Pop (E : out Positive) is
      begin
         E := Content (Top);
         Top := Top - 1;
      end Pop;
      procedure Push (E : Positive) is
      begin
         Top := Top + 1;
         Content (Top) := E;
      end Push;
      procedure Fill (E : Positive) is
      begin
         Top := Max;
         for I in Content'Range loop
            Content (I) := E;
            pragma Loop_Invariant (for all J in 1 .. I => Content (J) = E);
         end Loop;
      end Fill;
   end Stacks;
   use Stacks;

   E : Positive := 1;
begin
   Fill (E);
   Pop  (E);
   pragma Assert (E = 1);
end Use_Stack;
