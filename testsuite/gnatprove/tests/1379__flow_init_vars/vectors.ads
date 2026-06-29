package Vectors is
   subtype Unused is Positive;

   type Vector (Capacity : Natural) is record
      Dummy : String (1 .. 3);
      Foo   : Natural;
   end record;

   procedure Delete (Container : in out Vector; Index : Natural)
   with
     Global     => null,
     Exit_Cases =>
       (Index = 1 =>
          (Exception_Raised => Constraint_Error),
        others => Normal_Return);

   procedure Delete
     (Container : in out Vector; Index : Natural; Count : Natural)
   with
     Global     => null,
     Exit_Cases =>
       (Index = 1 =>
          (Exception_Raised => Constraint_Error),
        others => Normal_Return);

end Vectors;
