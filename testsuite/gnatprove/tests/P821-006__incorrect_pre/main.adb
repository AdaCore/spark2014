with foo; use foo;
with Interfaces; use Interfaces;

--  GNATprove misses a failed precondition check in the call at line 18
procedure main with SPARK_Mode is

   --  inlined callee
   procedure bar (d : out Data_Type)
   is begin
      d := (others => 0); -- with this, GNATprove does not find violation in line 18
      --d (d'First) := 0; -- with this, GNATprove indeed finds a violation in line 18
   end bar;

   arr : Data_Type (0 .. 91) := (others => 0);
   i32 : Integer_32;
begin
   bar (arr); -- essential
   i32 := foo.toInteger_32 (arr (60 .. 64)); -- length check proved, but actually exception
end main;
