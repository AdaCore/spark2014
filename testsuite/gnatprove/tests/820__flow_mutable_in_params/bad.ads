package Bad with
  SPARK_Mode => On, Always_Terminates
is

   type Generator is limited private;

   function Random (Gen : Generator) return Integer
     with Side_Effects, Depends => (Random'Result => Gen);
   pragma Annotate (GNATprove, Mutable_In_Parameters, Generator);

private
   pragma SPARK_Mode (Off);

   type Writable_Access (Self : access Generator) is limited null record;
   --  Auxiliary type to make Generator a self-referential type

   type Generator is limited record
      Writable  : Writable_Access (Generator'Access);
      --  This self reference allows functions to modify Generator arguments

      State : Integer := 0;
   end record;

end Bad;
