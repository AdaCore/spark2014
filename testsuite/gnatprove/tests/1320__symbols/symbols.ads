package Symbols
  with SPARK_Mode
is

   type Symbol is access constant String;

   Out_Of_Space : exception;

   procedure Intern (S : String; Sym : out Symbol)
        with Exceptional_Cases => (Out_Of_Space => True);

end Symbols;
