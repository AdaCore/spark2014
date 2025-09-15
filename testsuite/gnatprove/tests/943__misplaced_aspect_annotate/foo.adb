procedure Foo with SPARK_Mode is
   package A is
      type T is private;
   private
      pragma SPARK_Mode (Off);
      type T is null record with Annotate => (GNATprove, Ownership);
   end A;
   package B is
      type T is private;
   private
      pragma SPARK_Mode (Off);
      type T is null record with Annotate => (GNATProve, Predefined_Equality, "no_equality");
   end B;
   package C is
      type T is private with Annotate => (GNATprove, No_Wrap_Around);
   private
      type T is mod 2**8;
   end C;
   package D is
      type T is private with Annotate => (GNATprove, No_Bitwise_Operations);
   private
      type T is mod 2**8;
   end D;
begin
   null;
end Foo;
