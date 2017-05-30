package A is

   function Add (X, Y : Integer) return Integer;
   function Add_Annotated (X, Y : Integer) return Integer with Global => null;

end A;
