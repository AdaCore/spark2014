package Show_Composite_Types_Shortcoming is

   type T is array (Natural range <>) of Integer;

   procedure Init_Loop (A : out T);

end Show_Composite_Types_Shortcoming;
