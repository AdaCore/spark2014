procedure Main2 is

   --  Same as Main, but with X being modified indirectly

   X : Boolean := True;

   procedure Flip with Pre => True is
   begin
      X := not X;
   end;

   generic
      A, B : Integer;
   procedure Do_If;

   generic
      A, B : Integer;
   procedure Do_Loop;

   generic
      A, B : Integer;
   procedure Do_Case;

   procedure Do_If is
   begin
      if A = B then
         Flip;
      end if;
   end;

   procedure Do_Loop is
   begin
      for J in A .. B loop
         Flip;
      end loop;
   end;

   procedure Do_Case is
   begin
      case A = B is
         when True =>
            Flip;
         when False =>
            null;
      end case;
   end;

   procedure Try_If   is new Do_If   (1,0);
   procedure Try_Loop is new Do_Loop (1,0);
   procedure Try_Case is new Do_Case (1,0);

begin
   Try_If;
   Try_Loop;
   Try_Case;
end;
