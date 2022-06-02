package body Pkg is
   package body Nested is
      procedure Swap_T2_Inst is new Swap_View_Conversion (T2);
      procedure Swap_T2 (X : in out T2) renames Swap_T2_Inst;
   end;
end;
