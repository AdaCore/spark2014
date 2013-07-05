package Some_Package
   with Abstract_State => State
is
   pragma Elaborate_Body (Some_Package);
   X : Integer;
end Some_Package;
