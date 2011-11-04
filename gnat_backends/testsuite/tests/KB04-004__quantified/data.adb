package body Data is
   procedure Make_Available (X : in out T) is
   begin
      null;
   end Make_Available;
   
   procedure Make_Available_2 (X : in out T) is
   begin
      for I in X'Range loop
	 X(I) := not X(I);
      end loop;
   end Make_Available_2;
   
   procedure Make_Available_3 (X : in out T) is
   begin
      for I in X'Range loop
	 pragma Assert (for all K in X'First .. I-1 => X(K) = not X'Old(K));
	 X(I) := not X(I);
      end loop;
   end Make_Available_3;
end Data;
