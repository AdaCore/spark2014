package Length is

   type Constr_Ar is array (1..20) of Integer;

   function F return Boolean
      with Post => (F'Result);

   function G return Integer
      with Post => (G'Result = Constr_Ar'Length);

   type Unconstr_Ar is array (Integer range <>) of Integer;

   B : Boolean;

   procedure UF (X : Unconstr_Ar)
      with Post => (B = (X'Length = 20));
end Length;
