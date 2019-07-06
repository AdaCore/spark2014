package P is

   type T_Vector is array (Natural range 0 .. 1) of Natural;
   type T_Matrix is array (Natural range 0 .. 3) of T_Vector;

   type T_Record is
      record
         Data : T_Matrix;
      end record;

   Foo : T_Record :=
     (Data => (others => (others => 0)));

   X : constant Integer := Foo.Data'Component_Size;

end P;
