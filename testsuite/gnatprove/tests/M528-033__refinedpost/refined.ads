package Refined is

   procedure P (X : in out Integer)
      with Pre => (X < Integer'Last),
           Post => (X > X'Old);
end Refined;
