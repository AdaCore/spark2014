package P2 with SPARK_Mode is
   type T2 (D : Boolean) is private;

   function Always_True (X, Y : T2) return Boolean with
     Post => Always_True'Result and (X /= Y);
   pragma Annotate (GNATprove, Terminating, Always_True);
private
   pragma SPARK_Mode (Off);
   type S is record
      X : Integer;
   end record;
   function "=" (X, Y : S) return Boolean is (False);

   type T2 (D : Boolean) is record
      C : S;
   end record;

   function Always_True (X, Y : T2) return Boolean is (True);
end P2;
