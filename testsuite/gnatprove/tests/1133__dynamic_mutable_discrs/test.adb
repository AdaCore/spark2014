procedure Test with SPARK_Mode is

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

      procedure P (X : in out R) with Pre => True is
         Y : constant R := X;
      begin
         if X'Constrained then
            pragma Assert (X'Size = Y'Size);
         else
            pragma Assert (X'Size = R'Object_Size);
         end if;
      end P;

      procedure P_Bad (X : in out R) is
         Y : constant R := X;
      begin
         pragma Assert (X'Size = Y'Size); -- @ASSERT:FAIL
      end P_Bad;

   begin
      pragma Assert (X'Size = R'Object_Size);
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

      procedure P (X : in out R) with Pre => True is
         Y : constant R := X;
      begin
         if X'Constrained then
            pragma Assert (X'Size = Y'Size);
         else
            pragma Assert (X'Size = R'Object_Size);
         end if;
      end P;

      procedure P_Bad (X : in out R) is
         Y : constant R := X;
      begin
         pragma Assert (X'Size = Y'Size); -- @ASSERT:FAIL
      end P_Bad;

   begin
      pragma Assert (X'Size = R'Object_Size);
      P (X);
      P (Y);
   end;

begin
   Test_Static;
   Test_Dynamic;
end;
