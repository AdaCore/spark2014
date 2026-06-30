
--  Test accounting of effects of functions when determining which borrowers
--  are modified on a given path.

procedure Updated_Borrower with SPARK_Mode is

   E : exception;
   X : aliased Integer := 0;
   Y : aliased Integer := 0;
   function Random (X : Integer) return Boolean with Global => null, Import;
   function F (X : in out Integer; Y : Integer) return Boolean with Side_Effects, Global => null, Import, Always_Terminates => True;
begin
   declare
      Z : access Integer := X'Access;
      T : access Integer := Y'Access;
   begin
      if Random (Z.all) then
         loop exit when F (Z.all, T.all); end loop;
      else
         loop continue when F (T.all, Z.all); exit; end loop;
         raise E;
      end if;
   end;
   pragma Assert (Y = 0); --@ASSERT:PASS
   pragma Assert (X = 0); --@ASSERT:FAIL
exception
   when E =>
      pragma Assert (X = 0); --@ASSERT:PASS
      pragma Assert (Y = 0); --@ASSERT:FAIL
end Updated_Borrower;
