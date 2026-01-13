procedure Main with SPARK_Mode is

   procedure Test_Static is
      type R (Present : Boolean := False) is record
         case Present is
         when True =>
            F : Integer;
         when False => null;
         end case;
      end record;

      X : aliased R := (Present => False);
      Y : aliased R (False) := (Present => False);

      procedure P (X : in out R) with Pre => not X.Present is
      begin
         if X'Constrained then
            declare
               Y : R (False) with Import, Address => X'Address;
            begin
               null;
            end;
         else
            declare
               Y : R with Import, Address => X'Address;
            begin
               null;
            end;
         end if;
      end P;

      procedure P_Bad (X : in out R) with Pre => not X.Present is
      begin
         if X'Constrained then
            declare
               Y : R with Import, Address => X'Address;  --  Size check should fail
            begin
               null;
            end;
         else
            declare
               Y : R (False) with Import, Address => X'Address;  --  Size check should fail
            begin
               null;
            end;
         end if;
      end P_Bad;
   begin
      declare
         Z : R with Import, Address => X'Address;
      begin
         null;
      end;
      declare
         Z : R (False) with Import, Address => Y'Address;
      begin
         null;
      end;
      P (X);
      P (Y);
   end;

   procedure Test_Dynamic is
      function Id (X : Integer) return Integer is (X);
      C : constant Integer := Id (5);
      type Bool_Array is array (Integer range 1 .. C) of Boolean with Pack;

      type R (Present : Boolean := False) is record
         G : Bool_Array; --  component whose size is not known statically
         case Present is
         when True =>
            F : Integer;
         when False => null;
         end case;
      end record;

      X : aliased R := (Present => False, G => (others => True));
      Y : aliased R (False) := (Present => False, G => (others => True));

      procedure P (X : in out R) with Pre => not X.Present is
      begin
         if X'Constrained then
            declare
               Y : R (False) with Import, Address => X'Address;
            begin
               null;
            end;
         else
            declare
               Y : R with Import, Address => X'Address;
            begin
               null;
            end;
         end if;
      end P;

      procedure P_Bad (X : in out R) with Pre => not X.Present is
      begin
         if X'Constrained then
            declare
               Y : R with Import, Address => X'Address;  --  Size check should fail
            begin
               null;
            end;
         else
            declare
               Y : R (False) with Import, Address => X'Address;  --  Size check should fail
            begin
               null;
            end;
         end if;
      end P_Bad;
   begin
      declare
         Z : R with Import, Address => X'Address;
      begin
         null;
      end;
      declare
         Z : R (False) with Import, Address => Y'Address;
      begin
         null;
      end;
      P (X);
      P (Y);
   end;
begin
   Test_Static;
end Main;
