package Data is 
   type T is array (1 .. 10) of Boolean;
   
   --  These postconditions should not be provable
   
   procedure Make_Available (X : in out T) with
     Post => (for all I in X'Range => X(I) = not X'Old(I));
   procedure Make_Available_2 (X : in out T) with
     Post => (for all I in X'Range => X(I) = not X'Old(I));
   
   --  This postcondition should be provable
   
   procedure Make_Available_3 (X : in out T) with
     Post => (for all I in X'Range => X(I) = not X'Old(I));
end Data;
