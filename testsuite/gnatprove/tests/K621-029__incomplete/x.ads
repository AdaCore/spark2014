package X is
   type T is private with Default_Initial_Condition;
   procedure P (x : T) with Global => null, Annotate => (GNATprove, Always_Return);
private
   pragma SPARK_Mode (Off);
   type Ptr is access integer;
   type T is record
      A : Ptr := null;
   end record;
end X;
