package body Test is

   G : Integer;

   procedure Output_Not_Set (A : Boolean;
                             X : out Integer)
   is
   begin
      if A then    --  ***
         return;   --  ***
      end if;
      X := 12;
   end Output_Not_Set;

   procedure Use_Of_Uninitialised (A : Boolean;
                                   X : out Integer)
   is
      N : Integer;
      M : Integer := 8;  -- *** (19)
   begin
      if A then          -- *** (21)
         N := 12;
      else
         M := 12;        -- *** (24)
      end if;
      X := N + M;        -- *** (26)
   end Use_Of_Uninitialised;



end Test;
