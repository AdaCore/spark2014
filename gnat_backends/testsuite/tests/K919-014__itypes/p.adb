package body P is
   procedure P1 (X : in out R) is
   begin
      for J in X.C'Range loop
	 null;
      end loop;
   end P1;
end P;
