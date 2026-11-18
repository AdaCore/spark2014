package Exits with SPARK_Mode is
   E : exception;

   procedure Stop with
     Import,
     Global => null,
     No_Return,
     Always_Terminates,
     Program_Exit => True;

   function "&" (Left, Right : Integer) return Integer with
     Side_Effects,
     Exit_Cases =>
       (Left < 0 => (Exception_Raised => E),
        Left = 0 => Program_Exit,
        others => Normal_Return),
     Exceptional_Cases => (E => True),
     Program_Exit => True;
end Exits;
