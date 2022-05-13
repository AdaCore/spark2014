with Types; use Types;
procedure Bad_Loop is
   X : Ptr := new Integer'(42);
   Y : Ptr;
begin
   loop
      Y := X;
      exit;
   end loop;
   Y := X;
end Bad_Loop;
