package body P
is
   procedure Clear (Map : out My_Mapping)
   is
   begin
      My_Hash.Clear (Map.X);
   end Clear;

   function Contains (Map : My_Mapping;
                      Key : My_String) return Boolean
   is
   begin
      return My_Hash.Contains (Map.X, Key);
   end Contains;

end P;
