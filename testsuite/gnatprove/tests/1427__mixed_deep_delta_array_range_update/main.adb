procedure Main with SPARK_Mode is
   type Wrapper is record
      Wrapped : Integer;
   end record;
   type A is array (Integer range <>) of Wrapper;
   subtype T is Integer range 1 .. 1;
   Z0 : A (0 .. 4) := (for I in 1 .. 3 => (Wrapped => 0), others => (Wrapped => 1));
   X : A := (1 .. 2 => (Wrapped => 0));
   X_Ok : A := (X with delta (1) => (Wrapped => 2), (2).Wrapped => 3);
   Y_Ko : A := (X with delta for I in 1 .. 2 => (Wrapped => I), (2).Wrapped => 3);
   Z_Ko : A := (X with delta 1 .. 2 => (Wrapped => 2), (2).Wrapped => 3);
   T_Ko : A := (X with delta T => (Wrapped => 2), (2).Wrapped => 3);
   U_Ko : A := (X with delta Integer range 1 .. 1 => (Wrapped => 2), (2).Wrapped => 3);
   V_Ko : A := (X with delta T'Range => (Wrapped => 2), (2).Wrapped => 3);
begin
   null;
end Main;
