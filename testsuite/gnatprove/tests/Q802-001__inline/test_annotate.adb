with Inlined; use Inlined;
procedure Test_Annotate with SPARK_Mode is


begin
   pragma Assert (F_1 (1) = 1);
   pragma Assert (F_2 (2) = 2);
   pragma Assert (F_4 (4) = 4);
end Test_Annotate;
