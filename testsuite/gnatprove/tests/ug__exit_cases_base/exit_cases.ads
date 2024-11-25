package Exit_Cases with SPARK_Mode is

   E1, E2 : exception;

   procedure OS_Exit with
     Import,
     Global => null,
     No_Return,
     Always_Terminates,
     Program_Exit => True;

   procedure Might_Return_Abnormally (X : in out Integer) with
     Exit_Cases =>
       (X = 1  => Normal_Return,
        X = 2  => (Exception_Raised => E1),
        X = 3  => Exception_Raised,
        others => Program_Exit),
     Exceptional_Cases => (E1 | E2 => True),
     Program_Exit => True;

end Exit_Cases;
