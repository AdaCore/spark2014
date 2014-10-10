package Escape
   with SPARK_Mode
is

   function Backslash_Escape (S : String) return String
      with Post => Backslash_Escape'Result'Length >= S'Length;
end Escape;
