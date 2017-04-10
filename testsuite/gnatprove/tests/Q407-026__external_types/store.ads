package Store
with
  Abstract_State => State
is

   procedure Init
   with
     Global => (Output => State),
     Depends => (State => null);

   procedure Store_Element (E : Integer)
   with
     Global => (In_Out => State),
     Depends => (State =>+ E);

end Store;
