package Exit_Cases_Incomplete with SPARK_Mode is

   E1, E2 : exception;

   procedure Might_Return_Abnormally (X : in out Integer) with
     Exit_Cases =>
       (X = 2 => (Exception_Raised => E1)),
     Exceptional_Cases => (E1 | E2 => True);

end Exit_Cases_Incomplete;
