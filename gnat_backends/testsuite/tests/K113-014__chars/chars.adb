package body Chars is

   function DoIt return Boolean is
      X : Character := 'A';
      Y : Character := 'a';
      WX : Wide_Character := 'A';
      WY : Wide_Character := 'a';
      WWX : Wide_Wide_Character := 'A';
      WWY : Wide_Wide_Character := 'a';
      Z : Boolean := X < Y;
      WZ : Boolean := WX < WY;
      WWZ : Boolean := WWX < WWY;
      F : Character := Character'First;
      WF : Wide_Character := Wide_Character'First;
      WWF : Wide_Wide_Character := Wide_Wide_Character'First;
   begin
      return (Z and then WZ and then WWZ);
   end DoIt;

end Chars;
