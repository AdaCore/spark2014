procedure Test_Dispatch with spark_mode is

   type R is record
      I : Integer;
   end record;

   package Nested is
      type Root is tagged null record;
      procedure P (X : Root; Y : R) with
        Import,
        Relaxed_Initialization => Y;
      function F (X : Root) return R with
        Import,
        Relaxed_Initialization => F'Result;
   end Nested;
begin
   null;
end;
