with Segway; use Segway;

package Segway.Execute is
   pragma SPARK_Mode (Off);

   type Reader is access function return Input;

   procedure Execute (Read : Reader)
   with Pre => Speed_Is_Valid,
     Post => State = Still and Speed_Is_Valid,
     Test_Case =>
       (Name     => "Segway standing still",
        Mode     => Nominal,
        Requires => State = Still),
     Test_Case =>
       (Name     => "Segway moving forward",
        Mode     => Nominal,
        Requires => State = Forward),
     Test_Case =>
       (Name     => "Segway moving backward",
        Mode     => Nominal,
        Requires => State = Backward);

end Segway.Execute;
