package body Simple_Extended_Return
is
   C : Boolean;

   function Simple_Extended_R1 return Integer
     with Post => Simple_Extended_R1'Result = 1
   is
   begin
      if True then
	 return X : Integer := 1;
      end if;
      return Y : Integer := 3;
   end Simple_Extended_R1;

   function Simple_Extended_R2 (X : Integer) return Boolean
     with Post => Simple_Extended_R2'Result = True
   is
   begin
      if X > 0 then
	 return A : Boolean := True;
      else
	 return B : Boolean do
	   B := True;
	 end return;
      end if;
   end Simple_Extended_R2;

begin

   C := Simple_Extended_R2 (4);

   pragma Assert (C = True);

end Simple_Extended_Return;
