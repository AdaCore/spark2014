procedure Test with SPARK_Mode is

   type R (Present : Boolean := False) is record
      case Present is
         when True =>
            F : Integer;
         when False => null;
      end case;
   end record;

   X : aliased R := (Present => False);
   Y : aliased R (False) := (Present => False);

   procedure Process (X : aliased in out R) with Pre => not X.Present is
   begin
      pragma Assert (X'Size = 32); --  Should this hold?
      if not X'Constrained then
         X := (Present => True, F => 12);
         pragma Assert (X'Size = 64); --  Is it OK that X can change size?
      end if;
   end Process;

begin
   pragma Assert (X'Size = 64);
   Process (X);
   pragma Assert (Y'Size = 32);
   Process (Y);
end;
