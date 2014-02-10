package Segway.Execute is
   pragma SPARK_Mode (Off);

   type Reader is access function return Input;

   procedure Execute (Read : Reader)
   with
     Pre => Speed_Is_Valid,
     Post => Current_Status = Still and Speed_Is_Valid,
     Test_Case =>
       (Name     => "Segway standing still",
        Mode     => Nominal,
        Requires => Current_Status = Still),
     Test_Case =>
       (Name     => "Segway moving forward",
        Mode     => Nominal,
        Requires => Current_Status = Forward),
     Test_Case =>
       (Name     => "Segway moving backward",
        Mode     => Nominal,
        Requires => Current_Status = Backward);

end Segway.Execute;
