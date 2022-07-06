procedure Incoh with SPARK_Mode is
   type Ptr is access Integer;
   function Copy(I:Ptr) return Ptr
      with Post =>
        (Copy'Result = null) = (I = null)
        and then (if I /= null then Copy'Result.all = I.all);
   function Copy(I:Ptr) return Ptr is
   begin
      if I = null
      then
         return null;
      else
         return new Integer'(I.all);
      end if;
   end;
   function Deref(I:Ptr) return Integer
     with Pre => I /= null,
     Post => Deref'Result = I.all;
   function Deref(I:Ptr) return Integer is (I.all);
   X : Ptr := new Integer'(0);
   Y : Integer;
begin
   -- Allowed (memory is leaked)
   pragma Assert(Deref(Copy(X)) = 0);
   pragma Assert(Copy(X).all = 0);
   -- Disallowed
   Y := Deref(Copy(X));
   Y := Copy(X).all;
end;
