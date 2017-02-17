package body Test is

   procedure Test_For_Loop is
   begin
      for B in Derived_Bool'Range loop
	 Do_Nothing;
      end loop;

      for B in Bool_Subtype'Range loop
	 Do_Nothing;
      end loop;
   end Test_For_Loop;

   procedure Test_While_Loop is
   begin
      while B1 loop
	 Do_Nothing;
	 exit when B2;
      end loop;

      while B2 loop
	 Do_Nothing;
	 exit when B1;
      end loop;
   end Test_While_Loop;

   procedure Test_Case_Stmt is
   begin
      case B1 is
	 when True =>
	    case B2 is
	       when True =>
		  Do_Nothing;
	       when False =>
		  null;
	    end case;

	 when False =>
	    null;
      end case;
   end Test_Case_Stmt;

   procedure Test_If is
   begin
      if B1 then
	 Do_Nothing;
      elsif B2 then
	 B1 := True;
      else
	 B2 := False;
      end if;

      if B2 then
	 Do_Nothing;
      elsif B1 then
	 B1 := False;
	 Do_Nothing;
      else
	 B2 := True;
	 Do_Nothing;
      end if;

      if Boolean (B1) and then B2 then
	 Do_Nothing;
      elsif B1 and then Derived_Bool (B2) then
	 B2 := False;
	 Do_Nothing;
      end if;
   end Test_If;

end Test;
