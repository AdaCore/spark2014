package Pack
  with Initializes => (B1, B2)
is

   type Derived_Bool is new Boolean;

   B1 : Derived_Bool := True;

   subtype Bool_Subtype is Boolean;

   B2 : Bool_Subtype := True;

   B : Boolean;

   procedure Do_Nothing;

end Pack;
