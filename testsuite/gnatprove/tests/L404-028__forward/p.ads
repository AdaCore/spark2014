package P is
   procedure Incr (X : in out Integer) with
     Post => X = Add_One (X'Old);

   function Add_One (X : Integer) return Integer is (X + 1);
end P;
