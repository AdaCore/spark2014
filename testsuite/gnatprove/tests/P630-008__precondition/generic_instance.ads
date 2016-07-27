package Generic_Instance with SPARK_Mode is
   type Root is tagged record
      F : Natural;
   end record;

   type Nat_Array is array (1 .. 100) of Root;

   generic
      type E (<>) is private;
      with function P (X : E) return Boolean is <>;
   package G_Prop is
      function PP (X : E) return Boolean renames P;
   end G_Prop;

   function P (X : Root'Class) return Boolean;

   procedure Test (X : Root'Class);
end Generic_Instance;
