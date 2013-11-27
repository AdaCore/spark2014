package body Initializes_Illegal_2
  with SPARK_Mode,
       Refined_State => (AS  => A,
                         AS2 => (B, C))
is
   A, B : Integer := 1;
   C    : Integer;
begin
   C := B + X;  --  warning: AS2 must not depend on X
end Initializes_Illegal_2;
