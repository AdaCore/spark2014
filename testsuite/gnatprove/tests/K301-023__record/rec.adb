package body Rec is

   function Next (X : Counter) return Positive is
   begin
      return X.Count + 1;
   end Next;

end Rec;
