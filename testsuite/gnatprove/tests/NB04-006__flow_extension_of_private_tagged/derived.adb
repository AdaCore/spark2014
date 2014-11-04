package body Derived is
   overriding function Make (B : Boolean) return Derived_T is
      R : Derived_T;
   begin
      Base_T (R) := Make (B);
      R.B        := B;
      return R;
   end Make;
end Derived;
