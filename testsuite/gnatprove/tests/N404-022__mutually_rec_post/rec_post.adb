package body Rec_Post is
   function Is_Even (I : Natural) return Boolean is (I mod 2 = 0);
   function Is_Odd (I : Natural) return Boolean is (I mod 2 = 1);
end;
