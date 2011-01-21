package Ite is
   procedure Not_Null (X : in out Integer)
      with Post => (X /= 0);
end Ite;
