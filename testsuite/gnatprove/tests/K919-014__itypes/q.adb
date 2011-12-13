package body Q is
   procedure Q1 (X : in out R) is
   begin
      for J in X.C'Range loop
	 null;
      end loop;
   end Q1;
end Q;
