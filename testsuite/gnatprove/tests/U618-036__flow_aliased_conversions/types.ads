package Types is
   pragma Elaborate_Body;

   type Root_T is tagged record
      Field : Integer;
   end record;

   procedure Foo (Self : in out Root_T);

   function Constructor (I : Integer := 0) return Root_T is ((Field => I));

   function Sub (Left  : Root_T;
                 Right : Root_T) return Integer is
      (Left.Field - Right.Field);

   type Derived_T is new Root_T with record
      A : Integer;
   end record;

   overriding procedure Foo (Self : in out Derived_T);
   overriding function Constructor (I : Integer := 0) return Derived_T is
      ((Field => I, A => 5));

end Types;
