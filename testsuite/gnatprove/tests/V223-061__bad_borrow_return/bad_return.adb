with Types; use Types;
procedure Bad_Return (X : in out Ptr) is
   Y : Ptr;
begin
   if X.all = 0 then
      Y := X;
      return;
   end if;
end Bad_Return;
