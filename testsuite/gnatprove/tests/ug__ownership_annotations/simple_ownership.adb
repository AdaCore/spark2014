procedure Simple_Ownership with SPARK_Mode is
   package Nested is
      type T is private with
        Default_Initial_Condition,
        Annotate => (GNATprove, Ownership);

      function Read (X : T) return Boolean;
   private
      pragma SPARK_Mode (Off);
      type T is null record;
      function Read (X : T) return Boolean is (True);
   end Nested;
   use Nested;

   X : T;
   Y : T;

begin
   pragma Assert (Read (X)); -- OK

   Y := X;

   pragma Assert (Read (X)); -- Error, X has been moved
end Simple_Ownership;
