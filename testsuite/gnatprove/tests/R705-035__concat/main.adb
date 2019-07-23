
procedure main with SPARK_Mode => On is

   subtype Count_T is Integer range 0 .. 5;
   subtype Index_T is Integer range 1 .. 10;

   type Unconstrained_array_T is array (Integer range <>) of Integer;

   subtype Array_A_T is Unconstrained_array_T (Index_T);

   type Array_B_T is array (Index_T) of Integer;

   A : constant Array_A_T := (others => 0);
   B : constant Array_B_T := (others => 0);

   function Combine (Count : Count_T) return Array_A_T
   is
      (Array_A_T'(Unconstrained_array_T (A (Index_T'First + Count ..  Index_T'Last)) & --@INDEX_CHECK:FAIL
                  Unconstrained_array_T (B (Index_T'First .. Count))));

   Combined : Array_A_T;
   pragma Unreferenced (Combined);
begin
   Combined := Combine (1);
end main;
