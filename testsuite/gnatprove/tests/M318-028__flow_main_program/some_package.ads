package Some_Package
   with Abstract_State => State
is
   procedure Init with Global => (Output => State);
   X : Integer;
end Some_Package;
