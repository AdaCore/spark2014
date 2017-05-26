package P
is
   Z : Integer;

   type T is tagged record
      X : Integer;
   end record;

   procedure Proc (A : T)
      with Global => (In_Out => Z);

end P;
