pragma Extensions_Allowed (All);
procedure P is
   type T is access Integer;
   type TA is access all Integer;
   type TC is access constant Integer;
begin
   X : T;
   X := new Integer'(3);
   begin
      Y : T := X;
   end;
   if True then
      Y : T := X;
   else
      Y : T := X;
   end if;

   XA : TA;
   XA := new Integer'(3);
   begin
      YA : TA := XA;
   end;
   case True is
      when True =>
         Y : T := X;
      when False =>
         Y : T := X;
   end case;

   XC : TC;
   XC := new Integer'(3);
   begin
      YC : TC := XC;
   end;
end P;
