package Exit_Cases_Default_Contract with SPARK_Mode is

   E1, E2 : exception;

   procedure Might_Return_Abnormally (X : in out Integer) with
     Exit_Cases =>
       (X = 1  => Normal_Return,
        X = 2  => (Exception_Raised => E1),
        others => Exception_Raised);

   procedure Call_Might_Return_Abnormally (X : in out Integer) with
     Exceptional_Cases => (E1 | E2 => True);

end Exit_Cases_Default_Contract;
