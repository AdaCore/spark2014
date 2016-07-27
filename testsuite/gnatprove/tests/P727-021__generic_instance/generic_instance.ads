package Generic_Instance with SPARK_Mode is
   type Root is tagged record
      F : Natural;
   end record;

   type Nat_Array is array (1 .. 100) of Root;

   generic
      type E (<>) is private;
      with function F (X : E) return Boolean is <>;
      with procedure P (X : in out E) is <>;
   package G_Prop is
      function G (X : E) return Boolean renames F;
      procedure Q (X : in out E) renames P;
   end G_Prop;

   function Is_Valid (X : Root'Class) return Boolean;

   function F (X : Root'Class) return Boolean with
     Pre => Is_Valid (X);

   procedure P (X : in out Root'Class) with
     Pre => Is_Valid (X);

   procedure Test (X : in out Root'Class);

end Generic_Instance;
