procedure Main with SPARK_Mode is
   package Nested is
      type T is private with
        Default_Initial_Condition,
        Annotate => (GNATprove, Ownership, "Needs_Reclamation");
   private
      pragma SPARK_Mode (Off);
      type T is tagged null record;
   end Nested;
   use Nested;

   type Int_Acc is access Integer;

   type Holder is record
      F : T;
      G : Int_Acc;
   end record;

   X : Holder; --@RESOURCE_LEAK:PASS
   Y : Holder; --@RESOURCE_LEAK:FAIL
begin
   X.G := new Integer'(15);
   Y.F := X.F; --@RESOURCE_LEAK:FAIL
   Y.G := X.G; --@RESOURCE_LEAK:PASS
end Main;
