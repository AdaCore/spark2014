package P1 with SPARK_Mode is
   type T1 (D : Boolean) is private;

   function Always_True (X, Y : T1) return Boolean with
     Post => Always_True'Result and (if X.D = Y.D then X = Y);
   pragma Annotate (GNATprove, Terminating, Always_True);
private
   pragma SPARK_Mode (Off);
   type T1 (D : Boolean) is null record;

   function Always_True (X, Y : T1) return Boolean is (True);
end P1;
