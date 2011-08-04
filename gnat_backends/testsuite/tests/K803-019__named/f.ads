package F is
  type Floating_Type is digits 4;
  type Fixed_Type is delta 0.125 range -10.0 .. 10.0;
  type Integer_Type is range 0..1023;
  type Int_Array is array(Integer_Type) of Fixed_Type;

  Int_Array_Object : Int_Array;
  Integ : constant Integer_Type  := 2;
  Float : constant Floating_Type := 2.0;
  Named_Float   : constant := Float;
  Int2Fix : constant := Fixed_Type (Integ);
end;
